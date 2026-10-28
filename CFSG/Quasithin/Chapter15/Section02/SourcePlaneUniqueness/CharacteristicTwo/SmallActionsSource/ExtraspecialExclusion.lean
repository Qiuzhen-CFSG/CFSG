module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ExtraspecialAction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.MiddleStar
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.SeedCentralImage

/-!
# Corrected source15.2.21(3): the extraspecial contradiction

The arbitrary outside seed reduces the star alternatives to the actual
Heisenberg residual. The middle parabolic supplies Y₀ inside C_M(V),
whose star image is precisely that residual's center. The original S fixes
this center by the marked scalar-action calculation. Thus Y₀ becomes
central in Y₀S modulo the ambient two-core, contradicting its original
S₃ core quotient through a two-group kernel.

All three star alternatives are now excluded. The wreath quotients,
component-orbit alternative, NI image and Omega row are genuine earlier
source inputs, retained for their existing owners and final discharge by
qt-e-152-plane-uniqueness. No local split-exclusion conclusion is assumed.
TerminalExclusion applies this theorem to the original binary component.

Source: Aschbacher--Smith15.2.21(3), printed p.1114, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding.OmegaAction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I Y₁ : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Corrected source15.2.21(3), for an arbitrary two-perfect outside seed.
The literal star quotient and marked Heisenberg action discharge the
extraspecial alternative; the cyclic and elementary alternatives are
already excluded by StarReduction. -/
theorem source_15_2_21_3_from_preceding
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (s : Seed M I (smallActionS T ZS) Y₁) (hout : ¬ Y₁ ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3))
    (eK : (smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) := by
  let := hsource.prepared.elementary
  intro ho
  by_contra hnot
  obtain ⟨hcard,_,_,eP⟩ := linearFour_star_extraspecial d hquotient horbit hI s hout eNI hnot eK ho
  obtain ⟨Y₀,hYC,hYK,hp,hTY,hYc,hYq⟩ := exists_middle_seed d hquotient horbit hI hnot eK
  let S := smallActionS T ZS
  let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
  let q := QuotientGroup.mk' (pCore 2 M)
  let P := (Y.subgroupOf M).map q
  let C := (center P).map P.subtype
  let L := Y₀ ⊔ S
  have hYM : Y₀ ≤ M := hYC.trans inf_le_left
  have hSM : S ≤ M := inf_le_left.trans hsource.maximal.1.2
  have hLM : L ≤ M := sup_le hYM hSM
  let j := inclusion hLM
  let f := q.comp j
  have hYI : Y₀ ≤ I := hYC.trans (inf_le_right.trans (d.module_centralizer_le hI))
  have s₀ : Seed M I S Y₀ := ⟨le_inf hYM hYI,hp,inf_le_left.trans hTY,hYq⟩
  have hmark : (Y₀.subgroupOf M).map q = C :=
    centralizing_seed_star_image_eq_center hYC hp hYc ho hcard eP
  have hScentral : (S.subgroupOf M).map q ≤ centralizer (C : Set (M ⧸ pCore 2 M)) := by
    rintro _ ⟨r,hr,rfl⟩ _ ⟨z,hz,rfl⟩
    exact (mul_inv_eq_iff_eq_mul.mp (s.star_center_centralized d hI hout eNI ho hcard eP r hr z hz)).symm
  have hCcentral : C ≤ centralizer (C : Set (M ⧸ pCore 2 M)) := by
    rintro _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hz w)
  have hcentral : (L.subgroupOf M).map q ≤ centralizer (C : Set (M ⧸ pCore 2 M)) := by
    rw [show L = Y₀ ⊔ S from rfl,subgroupOf_sup hYM hSM,Subgroup.map_sup,hmark]
    exact sup_le hCcentral hScentral
  apply s₀.not_central_image (T.isPGroup'.to_le inf_le_left) f
  · change IsPGroup 2 (q.comp j).ker
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective j (inclusion_injective hLM)
  · intro y hy x
    have hx : f x ∈ (L.subgroupOf M).map q := mem_map_of_mem q x.property
    have hyC : f y ∈ C := hmark ▸ mem_map_of_mem q hy
    exact (hcentral hx (f y) hyC).symm
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
