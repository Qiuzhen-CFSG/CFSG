module

public import Theory.SpecificGroups.G2.DoubleCoverInvolutions

/-!
# Noncommuting returning conjugates in the long-root class of G₂

A two-central involution is conjugate to the highest long root A(1).
The positive long roots B(1) and E(1) belong to the standard Sylow subgroup
and to that same class. Their commutator is A(1), so they do not commute.
Conjugating the Sylow supplies the same pair in every Sylow marking.

This is the model input for excluding the central-two G₂(4) covers in
Aschbacher--Smith 1.1.5(3)(b) during Proposition 2.2.2, pp.501--502 and
519--520 (1 March 2004 manuscript). It uses only the marked long-root class.
The imported octonion identities retain the attribution and license in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.MarkedStrongClosure
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [Finite F] in
private theorem rootB_rootE_not_commute :
    ¬Commute (rootB (1 : F)) (rootE 1) := by
  intro hc
  have he : MulAut.conj (rootE (1 : F)) (rootB 1) = rootB 1 := by
    rw [MulAut.conj_apply, hc.symm.eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [ShortRootProducts.rootE_conjugate_rootB, one_mul] at he
  have hz : rootA (1 : F) = 1 := mul_right_cancel (he.trans (one_mul _).symm)
  exact one_ne_zero (rootA_injective (hz.trans rootA_zero.symm))

/-- Every Sylow contains noncommuting conjugates of the actual two-central
involution, without an exhaustive classification of involutions. -/
theorem sylow_noncommuting_conjugates (v : Model F)
    (hv : IsSylowCentralInvolution v) (R : Sylow 2 (Model F)) :
    ∃ a b : R, IsConj v (a : Model F) ∧ IsConj v (b : Model F) ∧ ¬Commute a b := by
  have hA : IsConj v (rootA (1 : F)) :=
    (DoubleCoverInvolutions.isConj_one_of_twoCentral hv).symm
  have hB : IsConj (rootA (1 : F)) (rootB 1) :=
    isConj_iff.mpr ⟨weylR, weylR_rootA 1⟩
  have hE : IsConj (rootB (1 : F)) (rootE 1) :=
    isConj_iff.mpr ⟨weylS, weylS_rootB 1⟩
  have hb : rootB (1 : F) ∈ unipotent := subset_closure (by simp)
  have he : rootE (1 : F) ∈ unipotent := subset_closure (by simp)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F) (LieParabolicSetup.sylow (F := F)) R
  have hm : unipotent.map (MulAut.conj g).toMonoidHom = (R : Subgroup (Model F)) :=
    congrArg Sylow.toSubgroup hg
  let a : R := ⟨MulAut.conj g (rootB 1), by
    change MulAut.conj g (rootB 1) ∈ (R : Subgroup (Model F))
    rw [← hm]
    exact mem_map_of_mem _ hb⟩
  let b : R := ⟨MulAut.conj g (rootE 1), by
    change MulAut.conj g (rootE 1) ∈ (R : Subgroup (Model F))
    rw [← hm]
    exact mem_map_of_mem _ he⟩
  refine ⟨a, b, (hA.trans hB).trans (isConj_iff.mpr ⟨g, rfl⟩),
    ((hA.trans hB).trans hE).trans (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
  intro hc
  apply rootB_rootE_not_commute (F := F)
  apply (MulAut.conj g).injective
  have hh := congrArg Subtype.val hc.eq
  exact ((MulAut.conj g).map_mul _ _).trans (hh.trans ((MulAut.conj g).map_mul _ _).symm)

end Atlas.G2.MarkedStrongClosure
