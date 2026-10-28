module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceRecognition

/-!
# The nontrivial two-core at the reciprocal source point

The centralizer of the conjugate point is the actual conjugate of H. It
normalizes the conjugate span Uα. Consequently its intersection with H
normalizes the nontrivial elementary star image Uα*, which lies in its
relative two-core. This proves 14.7.59 on the literal source star quotient,
without a recognition datum or a chosen normal-subgroup witness.

Source: Aschbacher–Smith, 14.7.59, printed p.1067. The earlier critical-path
placement and positive rank selection remain explicit source inputs.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
/-- The original reciprocal point centralizer is the conjugate of H. -/
theorem partner_centralizer (path : CriticalPath (L := L) F) :
    centralizer (path.Zα : Set G) = conjugate F.H path.conjugator := by
  obtain ⟨z,hz,he⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hH := F.H_eq_centralizer (by decide) z he
  let e := MulAut.conj path.conjugator⁻¹
  have hz' : path.Zα = (zpowers z).map e.toMonoidHom := by
    change (F.Vi 1).map e.toMonoidHom = _
    rw [he]
  have hcenter : centralizer (F.Vi 1 : Set G) = F.H :=
    (le_antisymm (Subgroup.centralizer_le_normalizer _) (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide))))
  apply le_antisymm
  · intro x hx
    have hxH : e.symm x ∈ F.H := by
      rw [hH,mem_centralizer_singleton_iff]
      apply e.injective
      have hzmem : e z ∈ path.Zα := by rw [hz']; exact mem_map_of_mem _ (mem_zpowers z)
      simpa only [map_mul,e.apply_symm_apply] using (hx (e z) hzmem).symm
    exact ⟨e.symm x,hxH,e.apply_symm_apply x⟩
  · rintro x ⟨y,hy,rfl⟩ a ⟨b,hb,rfl⟩
    have hy' := hcenter ▸ hy
    change e b * e y = e y * e b
    simpa only [map_mul] using congrArg e (hy' b hb)

omit [Finite G] in
/-- Relative normality of Uα under its actual point centralizer. -/
theorem partner_centralizer_normalizes (path : CriticalPath (L := L) F) :
    centralizer (path.Zα : Set G) ≤ normalizer (path.Uα : Set G) := by
  rw [partner_centralizer path]
  exact (map_mono (f := (MulAut.conj path.conjugator⁻¹).toMonoidHom)
    (le_normalizer_conjugateSpanBy V F.H)).trans (le_normalizer_map _)

/-- Lemma 14.7.59 on the literal star image of H ∩ C_G(Zα). The nonzero
normal two-subgroup is the actual critical actor Uα*, not an arbitrary seed. -/
theorem partner_relative_twoCore_ne_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) :
    (star F (F.H ⊓ centralizer (path.Zα : Set G))).pCoreIn 2 ≠ ⊥ := by
  let A := star F path.Uα
  let J := F.H ⊓ centralizer (path.Zα : Set G)
  have hA := critical_elementary h hab path hplace selection
  let : IsElementaryAbelian 2 A := hA.2
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hZA : path.Zα ≤ path.Uα :=
    map_mono ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : IsElementaryAbelian 2 path.Uα :=
    IsElementaryAbelian.map (MulAut.conj path.conjugator⁻¹).toMonoidHom
  have hAJ : path.Uα ≤ J := le_inf hAH
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hZA))
  have hnorm : J ≤ normalizer (path.Uα : Set G) :=
    inf_le_right.trans (partner_centralizer_normalizes path)
  let : (path.Uα.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hAJ).mpr hnorm
  have hmap : A ≤ star F J := map_mono (subgroupOf_mono F.H hAJ)
  have hn : star F J ≤ normalizer (A : Set (HStar F.H)) := by
    rintro _ ⟨j,hj,rfl⟩
    apply le_normalizer_map (starMap F)
    refine ⟨j,?_,rfl⟩
    change j ∈ normalizer ((path.Uα.subgroupOf F.H) : Set F.H)
    rw [mem_normalizer_iff]
    intro a
    change ((a : G) ∈ path.Uα ↔ _)
    exact (mem_normalizer_iff.mp (hnorm hj) a)
  have hcore : A ≤ (star F J).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup (p := 2) (G := A)) hmap hn
  intro hz
  exact hA.1 (bot_unique (hz ▸ hcore))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
