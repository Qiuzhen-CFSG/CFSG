module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SupercriticalNineSource.Extraspecial
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.ActionKernel.AffineModel

/-!
# The actual natural-nine seed in the proof of 15.4.10

Starting with the original counterexample and the preceding local source
facts, the proof derives a nontrivial two-core image, excludes its action
on the quintic core by the genuine positive-family contradiction, and
selects a normal ternary supercritical subgroup. The actual cubic actor
excludes the extraspecial branch. The resulting E9 has irreducible Sylow
image, a noncentral uppercase residual lift, and original X-action of
order 24. The existing affine-model theorem is then applied to this seed.

The universal preceding 15.4.2--5 facts remain hypotheses owned by the
source assembly. This is the first three paragraphs of 15.4.10, printed
p.1159, not the subsequent uniqueness or representation-bound argument.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
open FamilySource Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
variable {G : Type*} [Group G] [Finite G]

/-- The normal E9 and all literal source action witnesses, derived from
the counterexample and the genuine preceding local facts. -/
theorem exists_nine_source
    (T : Sylow 2 G) (M X : Subgroup G) (_hMmax : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M) (hM : HasCharacteristicTwo M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)))
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (hcounter : ¬ X ≤ centralizer (localV (T : Subgroup G) M : Set G))
    (hs : Group.IsSolvable M)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3 ∨ p = 5)
    (hr3 : primeRank 3 M ≤ 2) (hr5 : primeRank 5 M ≤ 2)
    (hnon : ∀ Y ∈ Chapter1.Xi G (T : Subgroup G),
      ¬ Y ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hex : ∀ Y ∈ Chapter1.Xi G (T : Subgroup G), Y ∉ Chapter3.XiPlus G (T : Subgroup G)) :
    ∃ P : Subgroup (CoreQuotient M), ∃ hP : P.Normal,
      IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧
      (∀ B : Subgroup (CoreQuotient M), B ≤ P →
        image M (T : Subgroup G) ≤ normalizer (B : Set (CoreQuotient M)) → B = ⊥ ∨ B = P) ∧
      lift M P ∈ Chapter1.Xi G (T : Subgroup G) ∧
      (¬ lift M P ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) ∧
      Nat.card (((@MulAut.conjNormal (CoreQuotient M) _ P hP).comp
        ((quotientMap M).comp (inclusion hXM))).range) = 24 := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  obtain ⟨P, hPN, hshape, _, hmove⟩ := exists_ternary_source_shape T M X hTM hXM hM hX
    hX3 hcounter hs hp hr3 hr5 hex
  let : P.Normal := hPN
  let f := (quotientMap M).comp (inclusion hXM)
  let a := (MulAut.conjNormal : CoreQuotient M →* MulAut P).comp f
  have hr : primeRank 3 (CoreQuotient M) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 M) pCore_isPGroup).trans hr3
  obtain ⟨hE, hc⟩ := ternary_shape_elementary hr hX.1.2.1 hX3 f P hshape hmove
  let : IsElementaryAbelian 3 P := hE
  have hperfect : IsPPerfect 2 P := by
    apply (pResidual_eq_top_iff 2 P).mp
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime
      ((hshape.isPGroup.orderOf_coprime (by decide : Nat.Coprime 3 2) x).symm)
  have hXi : lift M P ∈ Chapter1.Xi G (T : Subgroup G) :=
    normal_lift_mem_upper_Xi T M hTM
      (twoCore_ne_bot_of_nontrivial_overgroup M X hXM hM hX3) P hperfect
      ⟨3, Nat.prime_three, by decide, hshape⟩
      (sylow_frattini_irreducible (Or.inl rfl) T M X Z hTM hXM hX hX3 P hshape hmove)
  refine ⟨P, hPN, hE, hc, ?_, hXi, hnon _ hXi,
    ternary_action_card M X hXM hX.1.2.1 hX3 P hshape hmove⟩
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hn : (T : Subgroup G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
      hX.1.1.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
    exact sup_eq_right.mp (T.is_maximal'
      ((isPGroup_pCoreIn 2 X).to_sup_of_normal_left' T.isPGroup' hn) le_sup_right)
  intro B hBP hBT
  let D := B.subgroupOf P
  have hD : ∀ x ∈ pCore 2 X, ∀ b ∈ D, a x b ∈ D := by
    intro x hx b hb
    have hxi : f x ∈ image M (T : Subgroup G) :=
      ⟨inclusion hXM x, hQT ⟨x, hx, rfl⟩, rfl⟩
    exact ((mem_normalizer_iff.mp (hBT hxi)) (b : CoreQuotient M)).mp hb
  have hmap : D.map P.subtype = B := map_subgroupOf_eq_of_le hBP
  rcases core_irreducible_on_plane (Or.inl rfl) hc hX.1.2.1 hX3 a hmove D hD with hb | ht
  · left
    simpa only [hb, Subgroup.map_bot] using hmap.symm
  · right
    rw [ht, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hmap.symm

open CentralizerNormalClosureCubic Representation.AffineNine

/-- The derived source seed, its two initial core reductions, and the
marked affine model with the original XT complement and centralizer core.
No model or action seed remains as an extra hypothesis. -/
theorem exists_nine_affine_model
    (T : Sylow 2 G) (M X : Subgroup G) (hMmax : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M) (hM : HasCharacteristicTwo M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)))
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (hcounter : ¬ X ≤ centralizer (localV (T : Subgroup G) M : Set G))
    (hs : Group.IsSolvable M)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3 ∨ p = 5)
    (hr3 : primeRank 3 M ≤ 2) (hr5 : primeRank 5 M ≤ 2)
    (hnon : ∀ Y ∈ Chapter1.Xi G (T : Subgroup G),
      ¬ Y ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hex : ∀ Y ∈ Chapter1.Xi G (T : Subgroup G), Y ∉ Chapter3.XiPlus G (T : Subgroup G)) :
    image M (X.pCoreIn 2) ≠ ⊥ ∧
    image M (X.pCoreIn 2) ≤ centralizer (pCore 5 (CoreQuotient M) : Set (CoreQuotient M)) ∧
    ∃ P : Subgroup (CoreQuotient M), ∃ hP : P.Normal,
      IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧
      (∀ B : Subgroup (CoreQuotient M), B ≤ P →
        image M (T : Subgroup G) ≤ normalizer (B : Set (CoreQuotient M)) → B = ⊥ ∨ B = P) ∧
      lift M P ∈ Chapter1.Xi G (T : Subgroup G) ∧
      (¬ lift M P ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) ∧
      Nat.card (((@MulAut.conjNormal (CoreQuotient M) _ P hP).comp
        ((quotientMap M).comp (inclusion hXM))).range) = 24 ∧
    (let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
    let Y := lift M P
    let S := X ⊔ (T : Subgroup G)
    let H := (Y ⊔ X) ⊔ (T : Subgroup G)
    let W := normalClosure (Z.subgroupOf H : Set H)
    let C := centralizer (W : Set H)
    let q := QuotientGroup.mk' C
    let B := (S.subgroupOf H).map q
    IsPGroup 2 C ∧
      (T : Subgroup G) ⊓ centralizer (sourceClosure H Z : Set G) =
        (H ⊓ centralizer (sourceClosure H Z : Set G)).pCoreIn 2 ∧
      ∃ (eY : Y ⧸ pCore 2 Y ≃* P) (c : P ≃* Translation),
        (∀ y : Y,
          (eY (QuotientGroup.mk' (pCore 2 Y) y) : CoreQuotient M) =
            quotientMap M ⟨(y : G), lift_le M P y.property⟩) ∧
        ((∃ (f : (H ⧸ C) ≃* Special) (b : B ≃* SpecialLinear),
          (∀ y : Y,
            f (q ⟨(y : G), (show Y ≤ H from le_sup_left.trans le_sup_left) y.property⟩) =
              SemidirectProduct.inl (c (eY (QuotientGroup.mk' (pCore 2 Y) y)))) ∧
          ∀ s : B, f s = SemidirectProduct.inr (b s)) ∨
        (∃ (f : (H ⧸ C) ≃* Full) (b : B ≃* LinearGroup),
          (∀ y : Y,
            f (q ⟨(y : G), (show Y ≤ H from le_sup_left.trans le_sup_left) y.property⟩) =
              SemidirectProduct.inl (c (eY (QuotientGroup.mk' (pCore 2 Y) y)))) ∧
          ∀ s : B, f s = SemidirectProduct.inr (b s))) ) := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  refine ⟨twoCore_image_ne_bot T M X hTM hXM hM hX hX3 hcounter,
    twoCore_image_centralizes_fiveCore T M X Z hTM hXM hM hX hX3 hr5 hex, ?_⟩
  obtain ⟨P, hPN, hE, hc, hirr, hXi, hnc, h24⟩ :=
    exists_nine_source T M X hMmax hTM hXM hM hX hX3 hcounter hs hp hr3 hr5 hnon hex
  let : P.Normal := hPN
  let : IsElementaryAbelian 3 P := hE
  refine ⟨P, hPN, hE, hc, hirr, hXi, hnc, h24, ?_⟩
  have hZT : Z ≤ (T : Subgroup G) := by
    intro z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hTC : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht |>.symm
  exact ActionKernel.AffineModel.residual_nine_affine_model_and_core
    T M X Z P hc hTM hXM hZT hTC hX hirr hnc hX3 h24

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
