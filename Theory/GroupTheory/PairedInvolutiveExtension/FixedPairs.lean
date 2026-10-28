module
public import Theory.GroupTheory.PairedInvolutiveExtension.Geometry
public import Theory.GroupTheory.PrimeRankProduct

/-!
# Independent fixed factors in the actor centralizer

The two fixed subgroups of the same involutive automorphism embed as a direct
product into the centralizer of the simultaneous actor. Consequently their
prime ranks add. This is the independent cubic-factor argument used in
Aschbacher--Smith 2.4.34, printed p.548 of the 1 March 2004 manuscript.
-/

public section
namespace Theory.GroupTheory.PairedInvolutiveExtension
open Subgroup
variable {K:Type*} [Group K] (α:MulAut K) (hα:Function.Involutive α)
/-- The two fixed factors embed independently in the diagonal actor centralizer. -/
def fixedPairHom : (α.fixedSubgroup×α.fixedSubgroup) →* centralizer ({graph α hα}:Set (Model α hα)) where
  toFun u := ⟨base α hα u.1 u.2,(mem_centralizer_graph_mk α hα _ _ _ _).mpr ⟨u.1.property,u.2.property⟩⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' u v := by apply Subtype.ext; simp [base]

theorem fixedPairHom_injective : Function.Injective (fixedPairHom α hα) := by
  intro u v huv
  have h := congrArg (fun x:centralizer ({graph α hα}:Set (Model α hα))=>x.val.left) huv
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

theorem primeRank_graph_centralizer_ge [Finite K] (p:ℕ) [Fact p.Prime] :
    2*primeRank p α.fixedSubgroup ≤ primeRank p (centralizer ({graph α hα}:Set (Model α hα))) := by
  have h := primeRank_le_of_injective p (fixedPairHom α hα) (fixedPairHom_injective α hα)
  rw [primeRank_prod_eq_add] at h
  omega
end Theory.GroupTheory.PairedInvolutiveExtension
