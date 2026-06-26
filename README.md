# LogicQ
An IR language for fault-tolerant quantum programming.

First, we design a type system with Chain-complex, then programming Logical level fault-tolerant program becomes manipulating these typed QEC object with index.
We support a verified automatic compilation pipeline from the Typed language to QStab- A stabilizer measurement IR, and then to QClifford: Detailed clifford circuit.



# QEC Type system of LogicQ

Following shows an example of defining the type with CellComplex in our QEC type system:

```python
# 1) Define a family of surface codes (sugar -> CSSCode core)
code surface(d: Int) as CellComplex over Z2 {

  cells {
    faces     F[x,y]  in 0..(d-2), 0..(d-2);
    edges_x   Ex[x,y] in 0..(d-2), 0..(d-1);
    edges_y   Ey[x,y] in 0..(d-1), 0..(d-2);
    vertices  V[x,y]  in 0..(d-1), 0..(d-1);
  }

  boundary {
    d2(F[x,y]) =
      Ex[x,y]   +
      Ey[x+1,y] +
      Ex[x,y+1] +
      Ey[x,y];

    d1(Ex[x,y]) = V[x,y]   + V[x+1,y];
    d1(Ey[x,y]) = V[x,y]   + V[x,y+1];
  }

  css {
    hx = matrix(d2);
    hz = transpose(matrix(d1));
  }
}

code five_qubit as StabilizerCode {

  # Number of physical qubits (optional if implied by generator length)
  n = 5;

  generators {
    S0 = "XZZXI";
    S1 = "IXZZX";
    S2 = "XIXZZ";
    S3 = "ZXIXZ";
  }

  logical_z {
    LZ0 = "ZZZZZ";
  }
}
```

Given the type system, we can program with Surface code type

```python
surface q1 [n=40, k=1, d=5]   # First surface-code block (distance-5)
surface q2 [n=40, k=1, d=5]   # Second surface-code block (distance-5)
surface t0 [n=84, k=1, d=7]   # Magic-T ancilla block (distance-7)

q1[0] = LogicH q1[0]

t0 = Distill15to1_T[d=25]     # returns a magic_T handle (see MagicQ below)
InjectT q1[0], t0

q2[1] = LogicCNOT q1[0], q2[1]

c1 = LogicMeasure q1[0]
c2 = LogicMeasure q2[1]
```


# MagicQ -- A high level fault-tolerant quantum programming for dynamic protocol with Post-selection
---

We introduce MagicQ -- which allows the user to construct a magic state factory. MagicQ also has the full power to express all code-switching protocols.

```python
protocol Distill15to1_T(surface f, int d):
  Repeat:

      # ---- X-type stabilizer checks ----
      c_x1 = LogicProp IIIIIIIXXXXXXXX
      c_x2 = LogicProp IIIXXXXIIIIXXXX
      c_x3 = LogicProp IXXIIXXIIXXIIXX
      c_x4 = LogicProp XIXIXIXIXIXIXIX

      # ---- Z-type stabilizer checks ----
      c_z1  = LogicProp IIIIIIIIZZZZZZZZ
      c_z2  = LogicProp IIIZZZZIIIIZZZZ
      c_z3  = LogicProp IZZIIZZIIZZIIZZ
      c_z4  = LogicProp ZIZIZIZIZIZIZIZ
      c_z12 = LogicProp IIIIIIIIIIZZZZ
      c_z13 = LogicProp IIIIIIIIZZIIIZZ
      c_z14 = LogicProp IIIIIIIIZIZIZIZ
      c_z23 = LogicProp IIIIIZZIIIIIIZZ
      c_z24 = LogicProp IIIIZIZIIIIIZIZ
      c_z34 = LogicProp IIZIIIZIIIZIIIZ

      Success = c_x1 == 0 && c_x2 == 0 && c_x3 == 0 && c_x4 == 0 &&
                c_z1 == 0 && c_z2 == 0 && c_z3 == 0 && c_z4 == 0 &&
                c_z12 == 0 && c_z13 == 0 && c_z14 == 0 &&
                c_z23 == 0 && c_z24 == 0 && c_z34 == 0
      Until Success

      return
```
