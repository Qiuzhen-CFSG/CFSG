module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.StarReduction
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.CubicNormalizer
public import Theory.SpecificGroups.HeisenbergPrime.ScalarAction

/-!
# The original S-action on the extraspecial star center

An arbitrary corrected outside seed has a nonnormal cubic image in the
actual S₃-square action. Since S normalizes that seed, its action on the
full cubic plane is scalar. The marked Heisenberg determinant calculation
and the previously proved literal action-kernel identity then show that
S fixes the actual star residual center.

Source: Aschbacher--Smith15.2.21(3), printed p.1114, refs/quasithin.pdf.
ExtraspecialExclusion applies this to the middle seed and the terminal
binary component; no center-action conclusion is assumed.
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

/-- Normalization of the arbitrary outside cubic makes the original S
fix the actual star residual center. The action and kernel retain their
literal source maps throughout. -/
theorem Seed.star_center_centralized
    (hI : PlaneEscapes Mc ZS I)
    (s : Seed M I (smallActionS T ZS) Y₁) (hout : ¬ Y₁ ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    let q := QuotientGroup.mk' (pCore 2 M)
    let P := (Y.subgroupOf M).map q
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 9 →
    Nonempty (P ≃* HeisenbergPrime 3) →
    ∀ r : M, (r : G) ∈ smallActionS T ZS →
      ∀ z : P, z ∈ center P → q r * (z : M ⧸ pCore 2 M) * (q r)⁻¹ = z := by
  let := hsource.prepared.elementary
  dsimp only
  intro ho hcard ⟨eP⟩ r hr z hz
  let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
  let q := QuotientGroup.mk' (pCore 2 M)
  let P := (Y.subgroupOf M).map q
  let g := omegaStarActor hsource.prepared.normalized ho
  let e := ho.2.2.2.1.some
  let f := e.toMonoidHom.comp g
  let f₀ := e.toMonoidHom.comp (action hsource)
  let B := (Y₁.subgroupOf M).map f₀
  let : (Y.subgroupOf M).Normal := source_omega_lemma_15_2_3_2 T
    hsource.maximal.1.2 hsource.prepared.normalized ho
  let : P.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsExtraspecial 3 P := IsExtraspecial.of_mulEquiv eP.symm
    (HeisenbergPrime.isExtraspecial (by decide))
  have hBc : Nat.card B = 3 := by
    rw [show B = ((Y₁.subgroupOf M).map (action hsource)).map e.toMonoidHom from (map_map _ _ _).symm,
      card_map_of_injective e.injective,s.action_image_eq_residual d hI hout eNI,
      card_map_of_injective (intersectionImage hsource I).subtype_injective]
    have hh := congrArg (fun K : Subgroup (Equiv.Perm (Fin 3)) => Nat.card K)
      (map_pResidual_of_surjective 2 eNI.toMonoidHom eNI.surjective)
    rwa [card_map_of_injective eNI.injective,
      Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card] at hh
  have hBn : ¬ B.Normal := by
    intro hn
    have hh := hn.comap e.toMonoidHom
    rw [show B = ((Y₁.subgroupOf M).map (action hsource)).map e.toMonoidHom from (map_map _ _ _).symm,
      comap_map_eq_self_of_injective e.injective] at hh
    exact s.action_image_not_normal d hI hout eNI hh
  have hrn : f₀ r ∈ normalizer (B : Set _) := by
    apply le_normalizer_map f₀
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq (s.le_NI.trans inf_le_left)]
    exact s.normalized hr
  have hscalar := SymmetricThreeProductResidual.normalizer_cubic_scalar B hBc hBn (f₀ r) hrn
  have hk : (f.domRestrict P).ker = center P := by
    have hgk := source_omega_extraspecial_star_kernel T hsource.maximal.1.2 hsource.partner
      hsource.prepared ho hcard inferInstance
    ext x
    change e (g x) = 1 ↔ x ∈ center P
    constructor
    · intro hx
      have hxg : x ∈ (g.domRestrict P).ker := e.injective (hx.trans e.map_one.symm)
      exact hgk ▸ hxg
    · intro hx
      have hxg : g x = 1 := (hgk.symm ▸ hx : x ∈ (g.domRestrict P).ker)
      exact (congrArg e hxg).trans e.map_one
  have ht : (∀ x : P, f (MulAut.conjNormal (q r) x) = f x) ∨
      (∀ x : P, f (MulAut.conjNormal (q r) x) = (f x)⁻¹) := by
    have hcube (x : P) : (f x) ^ 3 = 1 := by
      have hx : x ^ 3 = 1 := eP.injective (by rw [map_pow,HeisenbergPrime.pow_prime (by decide),map_one])
      rw [←map_pow,show (x : M ⧸ pCore 2 M) ^ 3 = 1 from congrArg Subtype.val hx,map_one]
    have hcalc (x : P) : f (MulAut.conjNormal (q r) x) = f₀ r * f x * (f₀ r)⁻¹ := by
      rw [MulAut.conjNormal_apply,map_mul,map_mul,map_inv]
      rfl
    rcases hscalar with hs | hs
    · exact Or.inl (fun x => (hcalc x).trans (hs (f x) (hcube x)))
    · exact Or.inr (fun x => (hcalc x).trans (hs (f x) (hcube x)))
  exact congrArg Subtype.val (HeisenbergPrime.fixes_center_of_scalar_image eP
    (MulAut.conjNormal (q r)) (f.domRestrict P) hk ht z hz)
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
