module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.CoreQuotient
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.PSL2
public import Theory.Alternating.Theorem523Reduction
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.Basic

/-!
# The I.1.3 cover inputs to 15.3.22 and 15.3.32

Every finite perfect central cover of A₈ has two-group kernel, by divisibility
by the kernel of the constructed universal Schur double cover. The actual
PSL₃(2) ≃ PSL₂(7) and PSL₄(2) ≃ A₈ comparisons transport this conclusion
to the binary linear groups; universality of the identity covers PSL₅(2).

For the literal map L/O₂(L) → L⁺, a selected binary model of L⁺ makes its
kernel the center of L/O₂(L). The preceding bounds therefore discharge the
center hypothesis in `RankTwoElimination.core_quotient_equiv_of_center_isTwoGroup`.
The original `componentMap` has kernel exactly O₂(L), and the constructed
comparison agrees pointwise with `coreQuotientMap`. No model of L/O₂(L) is
assumed in this covering step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.1.3,
printed p.407; 15.3.22, p.1128; the paragraph preceding 15.3.32, p.1132.
The actual universal covers and exceptional comparisons are proved in the
imported group-theory modules. This leaf supplies their local applications.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs
universe u v w
private def postcompose {H : Type u} {K : Type v} {J : Type w}
    [Group H] [Group K] [Group J] (f : PerfectCentralCovering.Cover H K)
    (e : K ≃* J) : PerfectCentralCovering.Cover H J where
  toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
  surjective := e.surjective.comp f.surjective
  isPerfect := f.isPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact f.ker_le_center

private theorem postcompose_ker {H : Type u} {K : Type v} {J : Type w}
    [Group H] [Group K] [Group J] (f : PerfectCentralCovering.Cover H K)
    (e : K ≃* J) : (postcompose f e).toMonoidHom.ker = f.toMonoidHom.ker :=
  MonoidHom.ker_comp_of_injective _ _ e.injective

/-- Every finite perfect central cover of the actual A₈ has two-group kernel. -/
theorem eightCoverKernelTwo : EightCoverKernelTwo.{u} := by
  intro H _ _ f
  let : IsQuasisimple (alternatingGroup (Fin 8)) :=
    GLS3.Chapter5.SchurPresentation.alternatingGroup_isQuasisimple 3
  let : IsQuasisimple H := f.isQuasisimple
  have hd := GLS3.Chapter5.Covering.coveringKernel_card_dvd_of_universal
    (GLS3.Chapter5.SchurPresentation.schurAlternatingCovering 3)
    (GLS3.Chapter5.SchurPresentation.theorem_5_2_3_b_universality 3 (by decide) (by decide))
    f.toCovering
  rw [GLS3.Chapter5.SchurPresentation.theorem_5_2_3_a] at hd
  change Nat.card f.toMonoidHom.ker ∣ 2 at hd
  exact IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hd)

/-- Transport of the PSL₂(7) universal double-cover bound to PSL₃(2). -/
theorem binaryPSL3_cover_kernel_isTwoGroup {H : Type u} [Group H] [Finite H]
    (f : PerfectCentralCovering.Cover H (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) :
    IsPGroup 2 f.toMonoidHom.ker := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (3 < Nat.card (ZMod 7)) := ⟨by norm_num⟩
  let g := postcompose f Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm
  let : IsQuasisimple H := g.isQuasisimple
  obtain ⟨hu, ⟨e⟩⟩ := ChapterI.LieMultipliers.PSL2.primeField_universalCover
    (ZMod 7) (by norm_num) (by norm_num)
  have hd := GLS3.Chapter5.Covering.coveringKernel_card_dvd_of_universal
    (GorensteinWalter.PSL2Cover.cover (ZMod 7)) hu g.toCovering
  have he : Nat.card (GorensteinWalter.PSL2Cover.cover (ZMod 7)).toMonoidHom.ker = 2 := by
    rw [Nat.card_congr e.toEquiv]
    simp
  rw [he] at hd
  change Nat.card g.toMonoidHom.ker ∣ 2 at hd
  rw [show g.toMonoidHom.ker = f.toMonoidHom.ker from postcompose_ker _ _] at hd
  exact IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hd)

/-- Transport of the Schur A₈ double-cover bound to PSL₄(2). -/
theorem binaryPSL4_cover_kernel_isTwoGroup {H : Type u} [Group H] [Finite H]
    (f : PerfectCentralCovering.Cover H (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :
    IsPGroup 2 f.toMonoidHom.ker := by
  have h := eightCoverKernelTwo H
    (postcompose f Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)
  rwa [postcompose_ker] at h

/-- The universal identity cover of PSL₅(2) bounds every perfect-cover kernel. -/
theorem binaryPSL5_cover_kernel_isTwoGroup {H : Type u} [Group H] [Finite H]
    (f : PerfectCentralCovering.Cover H (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))) :
    IsPGroup 2 f.toMonoidHom.ker := by
  let : IsQuasisimple (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple (ZMod 2)
  let : IsQuasisimple H := f.isQuasisimple
  have hd := GLS3.Chapter5.Covering.coveringKernel_card_dvd_of_universal
    Covering.id Theory.SpecificGroups.PSL5Two.UniversalCover.identity_isUniversal f.toCovering
  have he : Nat.card (Covering.id : Covering
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))).toMonoidHom.ker = 1 := by
    simp [Covering.id, MonoidHom.ker_id]
  rw [he] at hd
  change Nat.card f.toMonoidHom.ker ∣ 1 at hd
  exact IsPGroup.of_card_dvd_pow (n := 0) (by simpa using hd)
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs
open RankTwoElimination
universe u

/-- The three binary model cases surviving the rank-two sieve. -/
theorem binaryPSL_cover_kernel_isTwoGroup {H : Type u} [Group H] [Finite H]
    (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (f : PerfectCentralCovering.Cover H (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    IsPGroup 2 f.toMonoidHom.ker := by
  rcases hn with rfl | rfl | rfl
  · exact binaryPSL3_cover_kernel_isTwoGroup f
  · exact binaryPSL4_cover_kernel_isTwoGroup f
  · exact binaryPSL5_cover_kernel_isTwoGroup f

variable {G : Type u} [Group G] [Finite G] (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I) [(actionKernel d c.L).Normal]
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R ≤ centralizer (d.V : Set G))
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (model : plusImage d c.L c.L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))

include hcore hR hC n hn model

/-- The literal center hypothesis for the covering step in 15.3.22. -/
theorem center_isTwoGroup_of_binary_plus :
    IsPGroup 2 (center (c.L ⧸ pCore 2 c.L)) := by
  let _ := c.core_quotient_quasisimple
  let _ := component_image_quasisimple d c hcore hR hC
  let _ : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n (by omega)
  let _ : IsSimpleGroup (plusImage d c.L c.L) := model.isSimpleGroup
  let hc := core_centralizes_span d c.L hcore hR
  let f : Covering (c.L ⧸ pCore 2 c.L) (plusImage d c.L c.L) :=
    { toMonoidHom := coreQuotientMap d c.L hc
      surjective := coreQuotientMap_surjective d c.L hc }
  have hk := binaryPSL_cover_kernel_isTwoGroup n hn
    (postcompose (PerfectCentralCovering.ofCovering f) model)
  rw [postcompose_ker] at hk
  change IsPGroup 2 f.toMonoidHom.ker at hk
  rwa [f.ker_eq_center_of_isSimple] at hk

/-- Apply the existing covering step with its I.1.3 center premise discharged. -/
theorem core_quotient_equiv_of_binary_plus :
    Nonempty ((c.L ⧸ pCore 2 c.L) ≃* plusImage d c.L c.L) :=
  core_quotient_equiv_of_center_isTwoGroup d c hcore hR hC
    (center_isTwoGroup_of_binary_plus d c hcore hR hC n hn model)

/-- The original component projection has precisely the intrinsic two-core as kernel. -/
theorem componentMap_ker_of_binary_plus :
    (componentMap d c.L).ker = pCore 2 c.L := by
  let _ := c.core_quotient_quasisimple
  let _ := component_image_quasisimple d c hcore hR hC
  have hc := core_centralizes_span d c.L hcore hR
  let f : Covering (c.L ⧸ pCore 2 c.L) (plusImage d c.L c.L) :=
    { toMonoidHom := coreQuotientMap d c.L hc
      surjective := coreQuotientMap_surjective d c.L hc }
  have hk : IsPGroup 2 f.toMonoidHom.ker :=
    (center_isTwoGroup_of_binary_plus d c hcore hR hC n hn model).to_le f.ker_le_center
  let q := QuotientGroup.mk' (pCore 2 c.L)
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hk' : IsPGroup 2 (componentMap d c.L).ker := by
    have h := hk.comap_of_ker_isPGroup q hq
    rw [MonoidHom.comap_ker] at h
    change IsPGroup 2
      ((QuotientGroup.lift (pCore 2 c.L) (componentMap d c.L)
        (core_le_componentMap_ker d c.L hc)).comp q).ker at h
    rwa [QuotientGroup.lift_comp_mk'] at h
  exact le_antisymm (le_sSup ⟨inferInstance, hk'⟩) (core_le_componentMap_ker d c.L hc)

/-- The comparison is induced by the original core-quotient map. Its exposed
body retains this compatibility as a definitional equality. -/
@[expose] noncomputable def coreQuotientEquivBinaryPlus :
    (c.L ⧸ pCore 2 c.L) ≃* plusImage d c.L c.L :=
  MulEquiv.ofBijective (coreQuotientMap d c.L (core_centralizes_span d c.L hcore hR))
    ⟨(QuotientGroup.injective_lift_iff _ _ _).mpr
      (componentMap_ker_of_binary_plus d c hcore hR hC n hn model).symm,
      coreQuotientMap_surjective d c.L _⟩

/-- The comparison preserves the supplied action, without changing its marking. -/
@[simp] theorem coreQuotientEquivBinaryPlus_apply (l : c.L) :
    coreQuotientEquivBinaryPlus d c hcore hR hC n hn model
      (QuotientGroup.mk' (pCore 2 c.L) l) = componentMap d c.L l := rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs

end
