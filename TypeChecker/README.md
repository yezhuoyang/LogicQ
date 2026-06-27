# Type checker for Legal Logical operations


We design a type system to check whether some Logical Operations(especially transversal gate and code switching) are supported and well formed.  For example, we cannot do PPM between a Surface code logical qubit with a LP code logical qubit without code switching, but is this code switching possible in the first place? this will be decided by the type checker.