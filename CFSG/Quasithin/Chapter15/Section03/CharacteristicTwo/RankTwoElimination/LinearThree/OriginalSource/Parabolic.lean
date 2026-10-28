module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Sylow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualInvariance.ParabolicAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.PPerfectHom

/-!
# The component parabolic from the original Sylow intersection

The subgroup Y_L(S∩L) lies in M and hence is proper in the outside component
L. It contains a Sylow two-subgroup of L and therefore the two-core. Its
image in the marked binary SL₃ quotient is consequently proper and contains
a Sylow subgroup. It is not a two-group: otherwise its nontrivial two-perfect
residual Y_L would itself be a two-group.

The binary Bruhat subgroup calculation now identifies this image as a
conjugate of a point or line parabolic, using the original quotient marking.
No C.2.7 classification input is needed for this particular conclusion.

Source: Aschbacher–Smith, 15.3.11(1), 15.3.12(1), and the opening paragraph
of 15.3.23, printed pp.1123–1128; the intrinsic projective-plane calculation
is in `Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking`.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
open CFSG.Quasithin.Chapter15.Section03.RankTwo

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

private theorem parabolic_of_sylow (H : Subgroup Matrix.PSL3Two.SL)
    (P : Sylow 2 Matrix.PSL3Two.SL) (hP : (P : Subgroup _) ≤ H)
    (hH : H ≠ ⊤) (h₂ : ¬ IsPGroup 2 H) :
    ∃ (Q : Subgroup Matrix.PSL3Two.SL) (g : Matrix.PSL3Two.SL),
      (Q = Matrix.PSL3Two.pointParabolicSL ∨ Q = Matrix.PSL3Two.lineParabolicSL) ∧
      H = Q.conjBy g := by
  let B : Sylow 2 Matrix.PSL3Two.SL := Sylow.ofCard Matrix.PSL3Two.borelSL (by
    rw [Matrix.PSL3Two.card_borelSL, Matrix.PSL3Two.card_SL]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Matrix.PSL3Two.SL P B
  have hB : (P : Subgroup _).map (MulAut.conj g).toMonoidHom =
      Matrix.PSL3Two.borelSL := by
    change (g • P).toSubgroup = Matrix.PSL3Two.borelSL
    rw [hg]
    rfl
  let E := (MulAut.conj g).mapSubgroup
  have hb : Matrix.PSL3Two.borelSL ≤ E H := hB ▸ map_mono hP
  have hp : E H ≠ ⊤ := fun h =>
    hH (E.injective (h.trans E.map_top.symm))
  have hn : ¬ IsPGroup 2 (E H) := fun h =>
    h₂ (h.of_equiv ((MulAut.conj g).subgroupMap H).symm)
  refine ⟨E H, g⁻¹, Matrix.PSL3Two.parabolic_of_borel_le_of_not_two _ hb hp hn, ?_⟩
  exact (Subgroup.conjBy_inv H g).symm

variable {G : Type*} [Group G] [Finite G]

/-- The source component parabolic has the required point-or-line marking
under any specified identification of L/O₂(L) with SL₃(2). The only residual
input is its nontriviality, supplied by the original 15.3.12(1). -/
theorem component_parabolic_of_sylow (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hne : YL d c.L ≠ ⊥)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL) :
    ∃ (Q : Subgroup Matrix.PSL3Two.SL) (g : Matrix.PSL3Two.SL),
      (Q = Matrix.PSL3Two.pointParabolicSL ∨ Q = Matrix.PSL3Two.lineParabolicSL) ∧
      ((YL d c.L ⊔ (d.S ⊓ c.L)).subgroupOf c.L).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) = Q.conjBy g := by
  let A := YL d c.L
  let K := A ⊔ (d.S ⊓ c.L)
  let D := K.subgroupOf c.L
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))
  have hAL : A ≤ c.L := (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hAM : A ≤ d.M :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left).trans
      ((yplus_le_residualY_of_choice d.choice).trans
        (Chapter14.SourcePreliminaries.sourceResidual_le _ _))
  have hKM : K ≤ d.M := sup_le hAM (inf_le_left.trans (inf_le_left.trans d.sylow_le))
  obtain ⟨T, hT⟩ := Extension.SourceCases.component_sylow d c P hP
  have hTD : (T : Subgroup c.L) ≤ D := by
    intro t ht
    have htS : t ∈ d.S.subgroupOf c.L := hT ▸ ht
    exact mem_sup_right ⟨htS, t.property⟩
  have hk : f.ker = pCore 2 c.L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkD : f.ker ≤ D := hk ▸ (pCore_isPGroup.le_sylow_of_normal T).trans hTD
  have hD : D ≠ ⊤ := by
    intro ht
    apply c.outside
    intro l hl
    exact hKM (show (⟨l, hl⟩ : c.L) ∈ D from ht ▸ mem_top _)
  have hproper : D.map f ≠ ⊤ := by
    intro ht
    have he := comap_map_eq_self hkD
    rw [ht, comap_top] at he
    exact hD he.symm
  have hnot : ¬ IsPGroup 2 (D.map f) := by
    intro hp
    have hker : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup
    have hD2 := hp.comap_of_ker_isPGroup f hker
    rw [comap_map_eq_self hkD] at hD2
    have hA2 : IsPGroup 2 A :=
      (hD2.to_le (show A.subgroupOf c.L ≤ D from fun _ ha => mem_sup_left ha)).of_equiv
        (subgroupOfEquivOfLe hAL)
    have hperfect := ComponentIntersection.intersectionResidual_isPPerfect d.Yplus c.L
    have hid := hperfect.hom_eq_one_of_isPGroup hA2 (MonoidHom.id A)
    apply hne
    apply eq_bot_iff.mpr
    intro a ha
    exact congrArg Subtype.val (DFunLike.congr_fun hid ⟨a, ha⟩)
  let S := T.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact parabolic_of_sylow (D.map f) S (map_mono hTD) hproper hnot

/-- The Sylow intersection S∩L normalizes Y_L before any normalization of
L by the whole S has been proved. -/
theorem component_sylow_normalizes_residual (d : LocalData G) (L : Subgroup G) :
    d.S ⊓ L ≤ normalizer (YL d L : Set G) :=
  ResidualInvariance.componentSylow_normalizes_YL d L

/-- The marked parabolic has precisely the image of Y_L as its two-residual.
Only the intrinsic S∩L-normalization is used, so this is available before
the residual geometry establishes normalization of L by all of S. -/
theorem component_residual_image_of_parabolic (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) (M : Subgroup Matrix.PSL3Two.SL)
    (hM : ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = M) :
    ((YL d L).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
        (pResidual 2 M).map M.subtype :=
  ResidualInvariance.YL_image_of_component_parabolic d L e M hM

/-- A single inner adjustment of the given quotient marking simultaneously
puts the component parabolic and its actual Y_L image in standard position.
This supplies the marked residual used by the radical-factor argument. -/
theorem exists_standard_component_residual_marking (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hne : YL d c.L ≠ ⊥)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL) :
    ∃ (e' : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
      (M : Subgroup Matrix.PSL3Two.SL),
      (M = Matrix.PSL3Two.pointParabolicSL ∨ M = Matrix.PSL3Two.lineParabolicSL) ∧
      ((YL d c.L ⊔ (d.S ⊓ c.L)).subgroupOf c.L).map
        (e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) = M ∧
      ((YL d c.L).subgroupOf c.L).map
        (e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) =
          (pResidual 2 M).map M.subtype := by
  obtain ⟨M, g, hstd, hM⟩ := component_parabolic_of_sylow d c P hP hne e
  let e' := e.trans (MulAut.conj g⁻¹)
  have hM' : ((YL d c.L ⊔ (d.S ⊓ c.L)).subgroupOf c.L).map
      (e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) = M := by
    change ((YL d c.L ⊔ (d.S ⊓ c.L)).subgroupOf c.L).map
      ((MulAut.conj g⁻¹).toMonoidHom.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)))) = M
    rw [← map_map, hM]
    exact M.conjBy_inv g
  exact ⟨e', M, hstd, hM', component_residual_image_of_parabolic d c.L e' M hM'⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
