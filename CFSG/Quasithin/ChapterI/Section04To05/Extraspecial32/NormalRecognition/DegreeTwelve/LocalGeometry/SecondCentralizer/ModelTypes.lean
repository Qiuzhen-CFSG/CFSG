module

public import Theory.GroupTheory.TwoInvolutionClassOrder
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Field.ZMod

/-!
# The marked symmetric centralizer models

These are the actual products `C₂ × Sₙ` appearing in Aschbacher's second
centralizer calculation. The marked first class consists of even involutions
with trivial central coordinate, and the second consists of all other
involutions. Keeping these definitions independent of the local configuration
also keeps the finite certificates independent of its larger import graph.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 4.2–4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer

open Theory.GroupTheory.TwoInvolutionClassOrder

public abbrev Model (n : ℕ) := Multiplicative (ZMod 2) × Equiv.Perm (Fin n)

/-- The marked central involution. -/
@[expose] public def centralInvolution (n : ℕ) : Model n :=
  (Multiplicative.ofAdd 1, 1)

/-- The first ambient involution class in the model. -/
@[expose] public def FirstClass {n : ℕ} (x : Model n) : Prop :=
  orderOf x = 2 ∧ x.1 = 1 ∧ Equiv.Perm.sign x.2 = 1

/-- The second ambient class, including several internal conjugacy classes. -/
@[expose] public def SecondClass {n : ℕ} (x : Model n) : Prop :=
  orderOf x = 2 ∧ ¬ FirstClass x

/-- The literal model fiber to be counted. -/
public abbrev ModelFiber (n : ℕ) :=
  {p : Model n × Model n // FirstClass p.1 ∧ SecondClass p.2 ∧
    halfOrder p.1 p.2 = centralInvolution n}

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
