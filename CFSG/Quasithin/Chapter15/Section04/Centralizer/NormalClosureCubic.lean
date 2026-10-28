module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.TernaryLine
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Normal cubic complements in the source normal closure

The actual quotient image of the normal closure is an elementary nine-group.
The image of X is cubic and normalized by the actual Sylow image. The
four-point action therefore gives a normal cubic subgroup in the quotient.
It differs from the image of X, since otherwise residual recovery would
make X normal in the original overgroup.

All quotient and residual maps are those of FamilySource. No membership
in the later Y-family, with its additional Thompson commutator condition,
is used. Source: Aschbacher--Smith, final paragraph of 15.4.8, p.1160.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic
open FamilySource LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G]

/-- The literal M-normal closure of X, embedded in G. -/
@[expose] def sourceClosure (M X : Subgroup G) : Subgroup G :=
  (normalClosure (X.subgroupOf M : Set M)).map M.subtype

private theorem closure_le (M X : Subgroup G) : sourceClosure M X ≤ M := map_subtype_le _

private theorem le_closure {M X : Subgroup G} (hXM : X ≤ M) : X ≤ sourceClosure M X := by
  intro x hx
  exact ⟨⟨x, hXM hx⟩, le_normalClosure hx, rfl⟩

private theorem closure_subgroupOf (M X : Subgroup G) :
    (sourceClosure M X).subgroupOf M = normalClosure (X.subgroupOf M : Set M) := by
  rw [sourceClosure, ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]

private theorem closure_normalizes (M X : Subgroup G) :
    M ≤ normalizer (sourceClosure M X : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer (closure_le M X)).mp
  rw [closure_subgroupOf]
  infer_instance

private theorem normalClosure_perfect {D : Type*} [Group D] (A : Subgroup D)
    (hA : IsPPerfect 2 A) : IsPPerfect 2 (normalClosure (A : Set D)) := by
  let N := normalClosure (A : Set D)
  let R := (pResidual 2 N).map N.subtype
  have hRn : R.Normal := inferInstance
  let := hRn
  have hAR : A ≤ R := by
    have he : (pResidual 2 A).map A.subtype = A := by
      rw [(pResidual_eq_top_iff 2 A).mpr hA, ← MonoidHom.range_eq_map, range_subtype]
    exact he ▸ embedded_pResidual_mono 2 (show A ≤ N from le_normalClosure)
  have hNR : N ≤ R := normalClosure_le_normal hAR
  apply (pResidual_eq_top_iff 2 N).mp
  apply top_unique
  intro n _
  obtain ⟨r, hr, he⟩ := hNR n.property
  exact (Subtype.ext he : r = n) ▸ hr

private theorem closure_perfect {M X : Subgroup G} (hXM : X ≤ M) (hp : IsPPerfect 2 X) :
    IsPPerfect 2 (sourceClosure M X) := by
  have hp' : IsPPerfect 2 (X.subgroupOf M) := hp.of_surjective
    (subgroupOfEquivOfLe hXM).symm.toMonoidHom (subgroupOfEquivOfLe hXM).symm.surjective
  exact (normalClosure_perfect (X.subgroupOf M) hp').of_surjective
    (M.subtype.subgroupMap _) (M.subtype.subgroupMap_surjective _)

private theorem local_normalizes (M U V : Subgroup G)
    (hn : U ≤ normalizer (V : Set G)) :
    U.subgroupOf M ≤ normalizer (V.subgroupOf M : Set M) := by
  intro u hu
  apply mem_normalizer_iff.mpr
  intro v
  exact mem_normalizer_iff.mp (hn hu) (v : G)

/-- Residual recovery for every normalized two-perfect subgroup, without
the later Y-family or a Thompson commutator premise. -/
theorem perfect_eq_lift_image (T : Sylow 2 G) {M X : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M)
    (hp : IsPPerfect 2 X) (hn : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    lift M (image M X) = X := by
  have hp' : IsPPerfect 2 (X.subgroupOf M) := hp.of_surjective
    (subgroupOfEquivOfLe hXM).symm.toMonoidHom (subgroupOfEquivOfLe hXM).symm.surjective
  have hk : IsPGroup 2 (quotientMap M).ker := by
    rw [quotientMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  rw [lift, image, residualPreimage_image_eq (quotientMap M) _ hp' hk
    (core_normalizes T hTM hn), map_subgroupOf_eq_of_le hXM]

private theorem image_closure_normal (M X : Subgroup G) : (image M (sourceClosure M X)).Normal := by
  change (((sourceClosure M X).subgroupOf M).map (quotientMap M)).Normal
  rw [closure_subgroupOf]
  exact Subgroup.Normal.map inferInstance (quotientMap M) (QuotientGroup.mk'_surjective _)

private theorem image_mono {M X Y : Subgroup G} (hXY : X ≤ Y) : image M X ≤ image M Y :=
  map_mono (comap_mono hXY)

variable [Finite G]

private theorem cubic_join (P A B : Subgroup G) [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hAP : A ≤ P) (hBP : B ≤ P)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hne : A ≠ B) : A ⊔ B = P := by
  have hJP : A ⊔ B ≤ P := sup_le hAP hBP
  let : IsElementaryAbelian 3 (A ⊔ B : Subgroup G) := IsElementaryAbelian.of_le hJP
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).mp
    (IsElementaryAbelian.isPGroup (p := 3) (G := (A ⊔ B : Subgroup G)))
  have hle : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp
    (by simpa only [hn, hP] using Nat.card_le_card_of_injective (Subgroup.inclusion hJP) (Subgroup.inclusion_injective hJP))
  have hpos : 0 < n := by
    have hsmall := Nat.card_le_card_of_injective
      (Subgroup.inclusion (show A ≤ A ⊔ B from le_sup_left))
      (Subgroup.inclusion_injective (show A ≤ A ⊔ B from le_sup_left))
    rw [hA, hn] at hsmall
    by_contra h
    have hn0 : n = 0 := by omega
    simp only [hn0, pow_zero] at hsmall
    omega
  have hnot : n ≠ 1 := by
    intro he
    have hJA : A ⊔ B = A := (eq_of_le_of_card_ge (show A ≤ A ⊔ B from le_sup_left)
      (by rw [hn, he, pow_one, hA])).symm
    have hBA : B ≤ A := hJA ▸ le_sup_right
    exact hne (eq_of_le_of_card_ge hBA (by rw [hA, hB])).symm
  have hn2 : n = 2 := by omega
  apply eq_of_le_of_card_ge hJP
  rw [hP, hn, hn2]
  norm_num

/-- A normal cubic complement in the actual quotient image of the normal
closure. The initial cubic subgroup need only be Sylow-invariant. -/
theorem complementary_cubic (T : Sylow 2 G) (M X : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M)
    (hp : IsPPerfect 2 X) (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hnon : ¬ M ≤ normalizer (X : Set G))
    [IsElementaryAbelian 3 (image M (sourceClosure M X))]
    (hY : Nat.card (image M (sourceClosure M X)) = 9)
    (hX : Nat.card (image M X) = 3) :
    ∃ A : Subgroup (CoreQuotient M), A.Normal ∧ Nat.card A = 3 ∧
      A ≤ image M (sourceClosure M X) ∧ A ≠ image M X ∧
      image M X ⊔ A = image M (sourceClosure M X) := by
  let P := image M (sourceClosure M X)
  let B := image M X
  let : P.Normal := image_closure_normal M X
  let S : Sylow 2 (CoreQuotient M) :=
    (T.subtype hTM).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 M))
  have hSB : (S : Subgroup (CoreQuotient M)) ≤ normalizer (B : Set _) :=
    (map_mono (local_normalizes M T X hn)).trans ((X.subgroupOf M).le_normalizer_map (quotientMap M))
  have hBP : B ≤ P := image_mono (le_closure hXM)
  obtain ⟨A, hAP, hAn, hA3⟩ := exists_normal_cubic_le_of_sylow_invariant P (Or.inr hY) S B hBP hX hSB
  have hne : A ≠ B := by
    intro he
    have hBn : B.Normal := he ▸ hAn
    have hMn : M ≤ normalizer (lift M B : Set G) :=
      lift_normalized M M le_rfl B (by rw [normalizer_eq_top_iff.mpr hBn]; exact le_top)
    rw [perfect_eq_lift_image T hTM hXM hp hn] at hMn
    exact hnon hMn
  exact ⟨A, hAn, hA3, hAP, hne, (cubic_join P B A hY hBP hAP hX hA3 hne.symm)⟩

end CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic

/-!
The source action-control conclusion places the whole normal closure in
C_G(Z). The normal quotient cubic then lifts inside that normal closure,
is normal in M, belongs to NormalCentralizerXi, and generates the normal
closure together with X. The source image cardinalities are the preceding
rank/core calculation, retained with qt-15-04-centralizer; universal
15.4.10 remains with qt-15-04-centralizer-witness.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic
open FamilySource LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Actual 15.4.10 action control places the source normal closure in C_G(Z). -/
theorem sourceClosure_le_centralizer (T : Sylow 2 G) (Z M X : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTM : (T : Subgroup G) ≤ M)
    (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hc : X ≤ centralizer (localV (T : Subgroup G) M : Set G)) :
    sourceClosure M X ≤ centralizer (Z : Set G) := by
  let W := normalClosure ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf M : Set M)
  let C := centralizer (W : Set M)
  have hCn : C.Normal := inferInstance
  let := hCn
  have hXC : X.subgroupOf M ≤ C := by
    intro x hx w hw
    apply Subtype.ext
    exact hc hx w (mem_map_of_mem M.subtype hw)
  have hNC : normalClosure (X.subgroupOf M : Set M) ≤ C := normalClosure_le_normal hXC
  rintro y ⟨y, hy, rfl⟩ z hz
  have hzM : z ∈ M := hTM (hZT hz)
  have hzW : (⟨z, hzM⟩ : M) ∈ W :=
    le_normalClosure (show (⟨z, hzM⟩ : M) ∈
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf M from hZ ▸ hz)
  exact congrArg Subtype.val ((hNC hy) ⟨z, hzM⟩ hzW)

/-- The normal complementary cubic lifts through the original M quotient
to a source family member and gives the literal source generating equality. -/
theorem lifted_member_and_join (T : Sylow 2 G) (Z M X : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hCM : centralizer (Z : Set G) ≤ M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hYC : sourceClosure M X ≤ centralizer (Z : Set G))
    (hnon : ¬ M ≤ normalizer (X : Set G))
    [IsElementaryAbelian 3 (image M (sourceClosure M X))]
    (hY : Nat.card (image M (sourceClosure M X)) = 9)
    (hB : Nat.card (image M X) = 3) :
    ∃ A : Subgroup (CoreQuotient M), A.Normal ∧ Nat.card A = 3 ∧
      lift M A ∈ NormalCentralizerXi (T : Subgroup G) Z ∧
      M ≤ normalizer (lift M A : Set G) ∧ sourceClosure M X = X ⊔ lift M A := by
  have hTM := hTC.trans hCM
  have hXM := hX.2.1.trans hCM
  have hp : IsPPerfect 2 X := hX.1.2.1
  obtain ⟨A, hAn, hA3, hAP, _, hjoin⟩ := complementary_cubic T M X hTM hXM hp hX.1.1 hnon hY hB
  let Y := sourceClosure M X
  let X₁ := lift M A
  have hYM : Y ≤ M := closure_le M X
  have hX₁M : X₁ ≤ M := lift_le M A
  have hYp : IsPPerfect 2 Y := closure_perfect hXM hp
  have hYp' : IsPPerfect 2 (Y.subgroupOf M) := hYp.of_surjective
    (subgroupOfEquivOfLe hYM).symm.toMonoidHom (subgroupOfEquivOfLe hYM).symm.surjective
  have hk : IsPGroup 2 (quotientMap M).ker := by
    rw [quotientMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hX₁Y : X₁ ≤ Y := by
    have hl := residualPreimage_le (quotientMap M) hk (Y.subgroupOf M) hYp'
      (core_normalizes T hTM (hTM.trans (closure_normalizes M X))) hAP
    have hm := map_mono (f := M.subtype) hl
    rwa [map_subgroupOf_eq_of_le hYM] at hm
  have hMn : M ≤ normalizer (X₁ : Set G) :=
    lift_normalized M M le_rfl A (by rw [normalizer_eq_top_iff.mpr hAn]; exact le_top)
  have hX₁C : X₁ ≤ centralizer (Z : Set G) := hX₁Y.trans hYC
  have hZtwo : IsPGroup 2 Z := T.isPGroup'.of_injective
    (Subgroup.inclusion hZT) (Subgroup.inclusion_injective hZT)
  have hZcore : Z ≤ (X₁ ⊔ (T : Subgroup G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hZtwo (hZT.trans le_sup_right)
      ((sup_le hX₁C hTC).trans (Subgroup.centralizer_le_normalizer _))
  have hH : X₁ ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, show (T : Subgroup G) ≤ X₁ ⊔ (T : Subgroup G) from le_sup_right⟩
    intro hbot
    exact hZne (le_bot_iff.mp (hbot ▸ hZcore))
  obtain ⟨e, _⟩ := prime_lift_quotient M A hA3
  have hi : (pCore 2 X₁).index = 3 := (Nat.card_congr e.toEquiv).trans hA3
  have hmem : X₁ ∈ NormalCentralizerXi (T : Subgroup G) Z :=
    ⟨⟨hTM.trans hMn, lift_perfect M A, hH,
      hi ▸ Nat.prime_three, hi ▸ (by decide : Odd 3)⟩, hX₁C, hCM.trans hMn⟩
  have hJY : X ⊔ X₁ ≤ Y := sup_le (le_closure hXM) hX₁Y
  have hJM : X ⊔ X₁ ≤ M := sup_le hXM hX₁M
  have hYJ : Y ≤ normalizer ((X ⊔ X₁ : Subgroup G) : Set G) :=
    (le_inf (hYC.trans hX.2.2) (hYM.trans hMn)).trans
      (normalizer_inf_normalizer_le_normalizer_sup X X₁)
  have him : image M (X ⊔ X₁) = image M Y := by
    change ((X ⊔ X₁).subgroupOf M).map (quotientMap M) = _
    rw [subgroupOf_sup hXM hX₁M, Subgroup.map_sup]
    change image M X ⊔ image M (lift M A) = image M Y
    rw [image_lift M A (three_isPPerfect A hA3)]
    exact hjoin
  have heq : (X ⊔ X₁).subgroupOf M = Y.subgroupOf M := eq_of_perfect_of_map_eq (quotientMap M) hk hYp'
    (comap_mono hJY) (local_normalizes M Y (X ⊔ X₁) hYJ) him
  have he := congrArg (Subgroup.map M.subtype) heq
  rw [map_subgroupOf_eq_of_le hJM, map_subgroupOf_eq_of_le hYM] at he
  exact ⟨A, hAn, hA3, hmem, hMn, he.symm⟩

/-- The source normal-closure step from the actual 15.4.10 action conclusion.
The two displayed image cardinalities and elementary structure are exactly
the preceding source rank/core calculation, not a model-recognition premise. -/
theorem source_complement_from_action_control (T : Sylow 2 G) (Z M X : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hCM : centralizer (Z : Set G) ≤ M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hnon : ¬ M ≤ normalizer (X : Set G))
    [IsElementaryAbelian 3 (image M (sourceClosure M X))]
    (hY : Nat.card (image M (sourceClosure M X)) = 9)
    (hB : Nat.card (image M X) = 3)
    (hcontrol : X ≤ centralizer (localV (T : Subgroup G) M : Set G)) :
    ∃ A : Subgroup (CoreQuotient M), A.Normal ∧ Nat.card A = 3 ∧
      lift M A ∈ NormalCentralizerXi (T : Subgroup G) Z ∧
      M ≤ normalizer (lift M A : Set G) ∧ sourceClosure M X = X ⊔ lift M A :=
  lifted_member_and_join T Z M X hZT hTC hZne hCM hX
    (sourceClosure_le_centralizer T Z M X hZT (hTC.trans hCM) hZ hcontrol) hnon hY hB

/-- Actual application to the universal 15.4.10 conclusion at the selected
maximal two-local overgroup of C_G(Z). -/
theorem source_complement_of_universal_action_control (T : Sylow 2 G) (Z M X : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hCM : centralizer (Z : Set G) ≤ M) (hM : IsMaximalTwoLocal M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hnon : ¬ M ≤ normalizer (X : Set G))
    [IsElementaryAbelian 3 (image M (sourceClosure M X))]
    (hY : Nat.card (image M (sourceClosure M X)) = 9)
    (hB : Nat.card (image M X) = 3)
    (h10 : ∀ D ∈ NormalCentralizerXi (T : Subgroup G) Z, ∀ N : Subgroup G,
      IsMaximalTwoLocal N → D ⊔ (T : Subgroup G) ≤ N →
      D ≤ N ⊓ centralizer (localV (T : Subgroup G) N : Set G)) :
    ∃ A : Subgroup (CoreQuotient M), A.Normal ∧ Nat.card A = 3 ∧
      lift M A ∈ NormalCentralizerXi (T : Subgroup G) Z ∧
      M ≤ normalizer (lift M A : Set G) ∧ sourceClosure M X = X ⊔ lift M A := by
  apply source_complement_from_action_control T Z M X hZT hTC hZne hZ hCM hX hnon hY hB
  exact (h10 X hX M hM (sup_le (hX.2.1.trans hCM) (hTC.trans hCM))).trans inf_le_right

omit [Finite G] in
/-- The actual local action centralizer lies in C_G(Z), since its defining
normal closure contains the original omega subgroup Z. -/
theorem action_centralizer_le (T : Sylow 2 G) (Z M : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTM : (T : Subgroup G) ≤ M)
    (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) :
    centralizer (localV (T : Subgroup G) M : Set G) ≤ centralizer (Z : Set G) := by
  apply centralizer_le
  intro z hz
  exact ⟨⟨z, hTM (hZT hz)⟩, le_normalClosure (hZ ▸ hz), rfl⟩

/-- Applying 15.4.10 to both actual source members puts their join in the
second action centralizer and proves its relative normality there. This is
the source input to the remaining rank-two omega calculation; no normality
in the second maximal overgroup is assumed. -/
theorem source_complement_in_second_action_centralizer
    (T : Sylow 2 G) (Z M₁ M₂ X : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hCM₁ : centralizer (Z : Set G) ≤ M₁) (hCM₂ : centralizer (Z : Set G) ≤ M₂)
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hnon : ¬ M₁ ≤ normalizer (X : Set G))
    [IsElementaryAbelian 3 (image M₁ (sourceClosure M₁ X))]
    (hY : Nat.card (image M₁ (sourceClosure M₁ X)) = 9)
    (hB : Nat.card (image M₁ X) = 3)
    (h10 : ∀ D ∈ NormalCentralizerXi (T : Subgroup G) Z, ∀ N : Subgroup G,
      IsMaximalTwoLocal N → D ⊔ (T : Subgroup G) ≤ N →
      D ≤ N ⊓ centralizer (localV (T : Subgroup G) N : Set G)) :
    ∃ A : Subgroup (CoreQuotient M₁), A.Normal ∧ Nat.card A = 3 ∧
      lift M₁ A ∈ NormalCentralizerXi (T : Subgroup G) Z ∧
      M₁ ≤ normalizer (lift M₁ A : Set G) ∧ sourceClosure M₁ X = X ⊔ lift M₁ A ∧
      sourceClosure M₁ X ≤ M₂ ⊓ centralizer (localV (T : Subgroup G) M₂ : Set G) ∧
      ((sourceClosure M₁ X).subgroupOf
        (M₂ ⊓ centralizer (localV (T : Subgroup G) M₂ : Set G))).Normal := by
  obtain ⟨A, hAn, hA3, hAmem, hAM, hjoin⟩ :=
    source_complement_of_universal_action_control T Z M₁ X hZT hTC hZne hZ
      hCM₁ hM₁ hX hnon hY hB h10
  let H₂ := M₂ ⊓ centralizer (localV (T : Subgroup G) M₂ : Set G)
  have hDH (D : Subgroup G) (hD : D ∈ NormalCentralizerXi (T : Subgroup G) Z) : D ≤ H₂ :=
    h10 D hD M₂ hM₂ (sup_le (hD.2.1.trans hCM₂) (hTC.trans hCM₂))
  have hYH : sourceClosure M₁ X ≤ H₂ := by
    rw [hjoin]
    exact sup_le (hDH X hX) (hDH (lift M₁ A) hAmem)
  have hHC : H₂ ≤ centralizer (Z : Set G) :=
    inf_le_right.trans (action_centralizer_le T Z M₂ hZT (hTC.trans hCM₂) hZ)
  have hHY : H₂ ≤ normalizer (sourceClosure M₁ X : Set G) := by
    rw [hjoin]
    exact (le_inf (hHC.trans hX.2.2) (hHC.trans hAmem.2.2)).trans
      (normalizer_inf_normalizer_le_normalizer_sup X (lift M₁ A))
  exact ⟨A, hAn, hA3, hAmem, hAM, hjoin, hYH,
    (normal_subgroupOf_iff_le_normalizer hYH).mpr hHY⟩

end CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic
