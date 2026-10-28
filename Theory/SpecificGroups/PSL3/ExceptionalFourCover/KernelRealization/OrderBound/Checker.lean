module
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.OrderBound.Data

/-!
# Checked equality of finite coordinate tables

The Boolean checker compares every input of all three transformation
coordinates. `eq_of_checkFamily` converts a successful finite computation
into genuine equality in the transformation monoid. Using this explicit
checker avoids higher-order decidable-instance search across module boundaries.
Every numerical application is reduced by the Lean kernel.
Source application: Aschbacher–Smith I.1.3(6), printed p.407; GLS3 §6.1.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel.OrderCertificate

def same {n : Nat} (a b : Function.End (Fin n)) : Bool :=
  (List.finRange n).all (fun i => a i == b i)

theorem same_spec {n : Nat} (a b : Function.End (Fin n)) : same a b = true ↔ a = b := by
  simp only [same, List.all_eq_true, List.mem_finRange, forall_true_left, beq_iff_eq]
  constructor
  · exact fun h => funext h
  · intro h i
    exact congrFun h i

def check (a b : M) : Bool :=
  same a.1.1 b.1.1 && same a.1.2 b.1.2 && same a.2 b.2

theorem eq_of_check {a b : M} (h : check a b = true) : a = b := by
  simp only [check, Bool.and_eq_true, same_spec] at h
  exact Prod.ext (Prod.ext h.1.1 h.1.2) h.2

def checkFamily {n : Nat} (a b : Fin n → M) : Bool :=
  (List.finRange n).all (fun i => check (a i) (b i))

theorem eq_of_checkFamily {n : Nat} (a b : Fin n → M)
    (h : checkFamily a b = true) (i : Fin n) : a i = b i :=
  eq_of_check (List.all_eq_true.mp h i (by simp))

end Matrix.PSL3.ExceptionalFourCover.KernelModel.OrderCertificate
