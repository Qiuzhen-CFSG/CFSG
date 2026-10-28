module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Core
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The residual normalizer in the second choice

The source centralizer residual Y_C centralizes L/O₂(L), so [Y_C,L] lies
in O₂(L). If S preserves Y_C, the preliminary containment O₂(L) ≤ R ≤ S
makes Y_C normal in Y_C O₂(L). Since Y_C is two-perfect, it is the exact
two-residual of that join. Conjugation by L preserves the join and hence
preserves Y_C. This contradicts any bound N_G(Y_C) ≤ M for the outside
component L.

The identification of Y_C with O²(C_Y(V)) in the second choice of
Hypothesis 15.3.10 is a separate action calculation. No assertion of that
identification, S-invariance, or elimination of the second choice is made here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.23, penultimate paragraph on printed p.1128.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
variable {G : Type*} [Group G]

private theorem normalizes_join_of_commutator {A P C : Subgroup G}
    (hAP : A ≤ normalizer (P : Set G)) (hcomm : ⁅C, A⁆ ≤ P) :
    A ≤ normalizer ((P ⊔ C : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha w hw
  have hmap : (P ⊔ C).map (MulAut.conj a).toMonoidHom ≤ P ⊔ C := by
    rw [Subgroup.map_sup]
    apply sup_le
    · apply map_le_iff_le_comap.mpr
      intro p hp
      exact mem_sup_left ((hAP ha p).mp hp)
    · apply map_le_iff_le_comap.mpr
      intro c hc
      have hm := (P ⊔ C).mul_mem
        (mem_sup_left (hcomm ((commutator_comm A C) ▸ commutator_mem_commutator ha hc)))
        (mem_sup_right hc)
      change a * c * a⁻¹ ∈ P ⊔ C
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hm
  exact hmap (mem_map.mpr ⟨w, hw, rfl⟩)

private theorem residual_join_two_group {C P : Subgroup G}
    (hC : IsPPerfect 2 C) (hP : IsPGroup 2 P)
    (hn : P ≤ normalizer (C : Set G)) :
    (pResidual 2 (P ⊔ C : Subgroup G)).map (P ⊔ C).subtype = C := by
  let H := P ⊔ C
  let : (C.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le hn C.le_normalizer)
  have hc : IsPPerfect 2 (C.subgroupOf H) :=
    hC.of_surjective (subgroupOfEquivOfLe (show C ≤ H from le_sup_right)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show C ≤ H from le_sup_right)).symm.surjective
  have hsup : C.subgroupOf H ⊔ P.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup (show C ≤ H from le_sup_right) (show P ≤ H from le_sup_left), sup_comm]
    exact subgroupOf_self H
  change (pResidual 2 H).map H.subtype = C
  rw [pResidual_eq_of_isPPerfect_sup (C.subgroupOf H) (P.subgroupOf H) hc
    hP.comap_subtype hsup, map_subgroupOf_eq_of_le (show C ≤ H from le_sup_right)]

private theorem normalizes_residual_of_commutator {A P C : Subgroup G}
    (hAP : A ≤ normalizer (P : Set G)) (hcomm : ⁅C, A⁆ ≤ P)
    (hC : IsPPerfect 2 C) (hP : IsPGroup 2 P)
    (hPC : P ≤ normalizer (C : Set G)) : A ≤ normalizer (C : Set G) := by
  have h := (normalizes_join_of_commutator hAP hcomm).trans
    (normalizer_le_normalizer_characteristic_image (P ⊔ C)
      (pResidual 2 (P ⊔ C : Subgroup G)))
  rwa [residual_join_two_group hC hP hPC] at h

/-- The exact residual identity used in the second-choice normalizer argument. -/
theorem YC_eq_residual_core_join [Finite G] (d : LocalData G) (L : Subgroup G)
    (hcore : L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSC : d.S ≤ normalizer (YC d L : Set G)) :
    Stellmacher.twoResidualAmbient (YC d L ⊔ L.pCoreIn 2) = YC d L := by
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual, sup_comm]
  exact residual_join_two_group (ComponentIntersection.centralizerResidual_isPPerfect _ _)
    (L.isPGroup_pCoreIn 2) (hcore.trans ((R_le_S d hR).trans hSC))

/-- S-invariance recovers the genuine component normalization of Y_C. -/
theorem component_normalizes_YC [Finite G] (d : LocalData G) (L : Subgroup G)
    (hcore : L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSC : d.S ≤ normalizer (YC d L : Set G)) :
    L ≤ normalizer (YC d L : Set G) := by
  have hcomm : ⁅YC d L, L⁆ ≤ L.pCoreIn 2 :=
    ((Chapter4.le_sectionCentralizer_iff _ L).mp
      ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right)).2
  exact normalizes_residual_of_commutator
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    hcomm (ComponentIntersection.centralizerResidual_isPPerfect _ _)
    (L.isPGroup_pCoreIn 2) (hcore.trans ((R_le_S d hR).trans hSC))

/-- The outside component prevents the residual normalizer from lying in M. -/
theorem YC_normalizer_not_le_M [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSC : d.S ≤ normalizer (YC d c.L : Set G)) :
    ¬ normalizer (YC d c.L : Set G) ≤ d.M := by
  intro h
  exact c.outside ((component_normalizes_YC d c.L hcore hR hSC).trans h)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree

end
