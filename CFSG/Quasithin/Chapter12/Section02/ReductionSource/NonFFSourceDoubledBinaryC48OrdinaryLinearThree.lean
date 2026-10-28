module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryLocal
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BinaryThreeSection

/-!
# Excluding ordinary binary linear-three components of the doubled source

The literal original residual has an SL₃(2) quotient and acts through a
two-group kernel inside the ordinary component's full central quotient.
It normalizes the nontrivial image of the original radical intersection.
In PSL₃ over any binary field this normalizer lies in a point or line
parabolic. Neither parabolic admits this perfect binary-three section.
This excludes the entire ordinary PSL₃(2ⁿ) family, including n = 1.

Source: Aschbacher--Smith C.3.5, printed p.150, applied to the original
Chapter 12 non-FF doubled-binary reciprocal witness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- No ordinary component of the literal binary doubled C.4.8 witness has
central quotient PSL₃ over a binary field. The original radical and full
central kernel are retained throughout the parabolic comparison. -/
theorem sourceOrbit_binary_witness_ordinary_not_linear_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K)
    {n : ℕ} (hn : 1 ≤ n) : ¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n) := by
  rintro ⟨B,_,_,hB,⟨eB⟩⟩
  let : Fintype B := Fintype.ofFinite B
  let : CharP B 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hB)
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let X := (LH.subgroupOf H).subgroupOf K
  let R := ((J.pCoreIn 2).subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hLK : LH.subgroupOf H ≤ K := hc.ordinary_component_contains_original K hK
  let eX : X ≃* LH := (subgroupOfEquivOfLe hLK).trans (subgroupOfEquivOfLe hLH)
  have hnorm := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy LH (H ⊓ normalizer (L : Set G)) = LH :=
    le_antisymm (conjugateSpanBy_le le_rfl hnorm) (le_conjugateSpanBy _ _)
  have hpLH : Group.IsPerfect LH := by
    have hh := hc.span_perfect
    rwa [hspan] at hh
  let := hpLH
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := eX.symm.toMonoidHom) eX.symm.surjective
  obtain ⟨_,_,_,_,_,_,e,_,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let eQ : (X ⧸ pCore 2 X) ≃* BinaryLinearThree.Group :=
    (QuotientGroup.congr _ _ eX (pCore_map_iso 2 eX)).trans e
  let π := eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hπ : Function.Surjective π := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
  let f := eB.toMonoidHom.comp (q.comp X.subtype)
  have hf : IsPGroup 2 f.ker := by
    have he : f.ker = (q.comp X.subtype).ker :=
      MonoidHom.ker_comp_of_injective _ _ eB.injective
    rw [he]
    exact pCore_isPGroup.to_le
      (DoubledBinaryOddPlacement.central_kernel_le_twoCore eQ X.subtype X.subtype_injective)
  have hl := hc.ordinary_quotient_local_data K hK
  rw [hspan] at hl
  let P := (R.map q).map eB.toMonoidHom
  have hP : IsPGroup 2 P := hl.2.1.map eB.toMonoidHom
  have hPne : P ≠ ⊥ := fun he => hl.2.2.1
    ((map_eq_bot_iff_of_injective _ eB.injective).mp he)
  have hfP : f.range ≤ normalizer (P : Set PSL(3,B)) := by
    have hh := (map_mono (f := eB.toMonoidHom) hl.2.2.2.1).trans
      ((R.map q).le_normalizer_map eB.toMonoidHom)
    simpa only [f,MonoidHom.range_comp,range_subtype] using hh
  obtain ⟨g,point,hg⟩ := MainConverse.LinearThreeGeometry.twoLocal_conjugate_le B
    (by omega : 0 < n) hB (normalizer (P : Set PSL(3,B))) ⟨P,hPne,hP,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj : IsPGroup 2 j.ker := by
    have he : j.ker = f.ker :=
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
    rwa [he]
  have hjP : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic B point := by
    apply le_trans ?_ hg
    rintro _ ⟨x,rfl⟩
    exact mem_map_of_mem _ (hfP ⟨x,rfl⟩)
  apply Matrix.PSL3.LinearThree.no_binary_three_quotient_in_parabolic B π hπ j hj
  cases point
  · exact Or.inr hjP
  · exact Or.inl hjP

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
