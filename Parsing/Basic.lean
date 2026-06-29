/-
  Parsing.Basic — generic, TOTAL `List Char` lexing helpers shared by every LogicQ
  text front-end (the per-level parsers PPM/PPR/QStab/QClifford, and indirectly the
  QASM/Surface front-ends).

  This is a LEAF module (no LogicQ dependencies) so it can be imported from the lowest
  IR layers without creating an import cycle through `Compiler`.

  DECIDABILITY.  Everything is structural recursion over `List Char` (no `String.Pos` /
  `ByteArray` ops), so parser tests built on these helpers stay `by decide`-checkable —
  the kernel reduces `"…".toList`, `Char` predicates, and `String.ofList` equality, but
  NOT `String.splitOn`/`trim`/`toNat?`.
-/

namespace Parsing

/-! ## §1. Lexing primitives. -/

/-- ASCII whitespace. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- An identifier character (identifiers start with a letter). -/
def isIdentChar (c : Char) : Bool := c.isAlpha || c.isDigit || c == '_'

/-- Drop leading whitespace. -/
def dropWs : List Char → List Char
  | c :: cs => if isWs c then dropWs cs else c :: cs
  | []      => []

/-- Trim leading + trailing whitespace. -/
def trimL (cs : List Char) : List Char := (dropWs (dropWs cs).reverse).reverse

/-- The leading run of identifier characters. -/
def takeIdent : List Char → List Char
  | c :: cs => if isIdentChar c then c :: takeIdent cs else []
  | []      => []

/-- Everything after the leading run of identifier characters. -/
def dropIdent : List Char → List Char
  | c :: cs => if isIdentChar c then dropIdent cs else c :: cs
  | []      => []

/-- The decimal value of a digit character, if it is one. -/
def digitVal? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat) else none

/-- Parse an all-digits char list to a `Nat` (no `String.toNat?`). -/
def natOfDigitsAux : Nat → List Char → Option Nat
  | acc, []      => some acc
  | acc, c :: cs => match digitVal? c with
                    | some d => natOfDigitsAux (acc * 10 + d) cs
                    | none   => none

def natOfDigits? : List Char → Option Nat
  | [] => none
  | cs => natOfDigitsAux 0 cs

/-- Split a char list at the FIRST occurrence of `close`, returning `(before, after)`. -/
def spanUntil (close : Char) : List Char → Option (List Char × List Char)
  | c :: cs => if c == close then some ([], cs)
               else match spanUntil close cs with
                    | some (a, b) => some (c :: a, b)
                    | none        => none
  | []      => none

/-- Split a char list at the FIRST `->`, returning `(before, after)`. -/
def spanArrow : List Char → Option (List Char × List Char)
  | '-' :: '>' :: cs => some ([], cs)
  | c :: cs => match spanArrow cs with
               | some (a, b) => some (c :: a, b)
               | none        => none
  | []      => none

/-- Split on every occurrence of `sep` (always returns ≥ 1 segment). Tail-recursive. -/
def splitOnChar (sep : Char) (xs : List Char) : List (List Char) :=
  let rec go (cur : List Char) (acc : List (List Char)) : List Char → List (List Char)
    | [] => (cur.reverse :: acc).reverse
    | c :: cs =>
        if c == sep then go [] (cur.reverse :: acc) cs
        else go (c :: cur) acc cs
  go [] [] xs

/-- Strip `// … (end of line)` line comments (the `Bool` is "inside a comment").
    Stripping happens before statement splitting, so a separator inside a comment is
    inert. Tail-recursive. -/
def stripComments (inside0 : Bool) (xs : List Char) : List Char :=
  let rec go (inside : Bool) (acc : List Char) : List Char → List Char
    | [] => acc.reverse
    | '\n' :: cs => go false ('\n' :: acc) cs
    | '/' :: '/' :: cs => go true acc cs
    | c :: cs => if inside then go true acc cs else go false (c :: acc) cs
  go inside0 [] xs

/-- Split a program into statement segments on newlines and `;`, comments stripped,
    blank segments dropped. -/
def stmtSegments (src : String) : List (List Char) :=
  ((splitOnChar '\n' (stripComments false src.toList)).flatMap (splitOnChar ';')).filter
    (fun s => ! (trimL s).isEmpty)

/-! ## §2. A shared parse-error type. -/

/-- A parse-phase error. -/
inductive ParseError where
  | malformed        (msg : String)    -- a recognized statement with a malformed body
  | badInt           (lexeme : String) -- an index / size that is not a `Nat`
  | unknownStatement (text : String)   -- a statement that is not gate-shaped
  deriving Repr, DecidableEq

/-! ## §3. Operand helpers. -/

/-- Parse an indexed reference `name[idx]` (whitespace-tolerant), e.g. `q[0]`. -/
def parseIndexed (cs0 : List Char) : Except ParseError (String × Nat) :=
  let cs   := trimL cs0
  let name := takeIdent cs
  let rest := trimL (dropIdent cs)
  match name with
  | [] => .error (.malformed "expected a register/block name")
  | _  =>
    match rest with
    | '[' :: rest2 =>
        match spanUntil ']' rest2 with
        | some (content, after) =>
            if (trimL after).isEmpty then
              match natOfDigits? (trimL content) with
              | some n => .ok (String.ofList name, n)
              | none   => .error (.badInt (String.ofList (trimL content)))
            else .error (.malformed "trailing characters after ']'")
        | none => .error (.malformed "missing ']' in index")
    | _ => .error (.malformed "expected '[index]' after the name")

/-- Parse a possibly-tagged natural: `q3 ↦ 3`, `c7 ↦ 7`, `5 ↦ 5` (an optional single
    leading `tag` letter is dropped, then digits). -/
def parseTaggedNat? (tag : Char) (cs : List Char) : Option Nat :=
  match trimL cs with
  | c :: rest => if c == tag then natOfDigits? (trimL rest) else natOfDigits? (c :: rest)
  | []        => none

/-- Structural index-of (kernel-reducible, unlike `List.findIdx?` whose not-found branch
    can get `decide`-stuck). -/
def nameIndexAux : List String → String → Nat → Option Nat
  | [],      _,  _ => none
  | n :: ns, nm, i => if n == nm then some i else nameIndexAux ns nm (i + 1)

/-- The position of `nm` in `names` (first match), or `none`. -/
def nameIndex? (names : List String) (nm : String) : Option Nat := nameIndexAux names nm 0

/-- Intern a block/name into a name table, returning its index (first-occurrence order).
    This is the "front end maps block names (`q`, `a`, …) to ids" map, materialised. -/
def internName (names : List String) (nm : String) : List String × Nat :=
  match nameIndex? names nm with
  | some i => (names, i)
  | none   => (names ++ [nm], names.length)

end Parsing
