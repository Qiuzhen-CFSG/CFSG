module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry.FieldNormalizers
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry.SylowNormalizers
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineSections
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.InnerSymmetric

/-!
# Field-of-nine placement from full four-group normalizers

Restrict the prescribed semilinear Sylow to its normal PGL₂ layer. The
checked paired-normalizer theorem chooses an S₄ through the original actor
in which that actor is nonnormal. This remains a genuine subgroup of the
full semilinear normalizer of the paired four-group.

A four-group nonnormal in S₄ cannot lie in the two-core of any group
containing that S₄: pull the two-core back along the inclusion and use
that the S₄ two-core itself has order four. Projective descent also proves
that every field-involution centralizer over F₉ has order 48, so an
intersection of order 16 is literally Sylow in that centralizer.

The two independent normalizer calculations identify the full normalizer
with a field-involution centralizer and prove its position relative to the
prescribed Sylow. Combining them proves `NineFieldPlacement` without extra
geometric premises. Its actual `NineSections` application constructs an E₁
member through the original actor that generates the ambient group with T.

Source: Aschbacher–Smith E.1.2 and E.1.14(6), printed pp.209–210, 214,
citing Aschbacher (1982), Lemma 4.10.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry
open PrimeGeometry.Inner.SymmetricNormalizers

private theorem nonnormal_four_not_le_core_comap
    {H K : Type*} [Group H] [Group K] [Finite H]
    (e : H ≃* Equiv.Perm (Fin 4)) (i : H →* K) (hi : Function.Injective i)
    (A : Subgroup H) [IsKleinFour A] (hn : ¬ A.Normal) :
    ¬ A ≤ (pCore 2 K).comap i := by
  intro hA
  have hcore : (pCore 2 K).comap i ≤ pCore 2 H :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective i hi⟩
  let : IsKleinFour (pCore 2 H) := symmetric_core_klein e
  have heq : A = pCore 2 H := eq_of_le_of_card_ge (hA.trans hcore) (by
    simp only [IsKleinFour.card_four, le_refl])
  exact hn (heq ▸ inferInstance)

variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]

omit [Finite F] [Finite (PGammaL2 F)] in
private theorem inner_le_linear : pGammaL2PSLRange F ≤ pGammaL2PGLRange F := by
  rintro x ⟨y, rfl⟩
  exact ⟨_, rfl⟩

private theorem paired_linear_normalizer (hF : Nat.card F = 3 ^ 2)
    (T : Sylow 2 (PGammaL2 F)) (A : Subgroup (PGammaL2 F))
    (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 2)
    (hAL : A ≤ pGammaL2PSLRange F) (hAT : A ≤ (T : Subgroup _)) :
    IsKleinFour (A.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)) ∧
    ∃ B : Subgroup (PGL2 F), IsKleinFour B ∧
      B ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range ∧
      B.map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) ≤ (T : Subgroup _) ∧
      A.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) ≤ normalizer (B : Set _) ∧
      Nonempty (normalizer (B : Set (PGL2 F)) ≃* Equiv.Perm (Fin 4)) ∧
      ¬ ((A.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)).subgroupOf
        (normalizer (B : Set _))).Normal := by
  let : Finite (PGL2 F) := Finite.of_injective
    (SemidirectProduct.inl : PGL2 F → PGammaL2 F) SemidirectProduct.inl_injective
  let L := pGammaL2PGLRange F
  let e : PGL2 F ≃* L := pGammaL2PGLRangeEquiv F
  let i : PGL2 F →* PGammaL2 F := SemidirectProduct.inl
  let A₀ := A.comap i
  have hAi : A ≤ i.range := hAL.trans inner_le_linear
  have hmap : A₀.map i = A := by
    rw [map_comap_eq, inf_eq_right.mpr hAi]
  have hc : Function.Injective i := SemidirectProduct.inl_injective
  let eA : A₀ ≃* A := (A₀.equivMapOfInjective i hc).trans (MulEquiv.subgroupCongr hmap)
  let := hA
  let : IsElementaryAbelian 2 A₀ := {
    is_comm.comm := fun a b => eA.injective (by
      simpa only [map_mul] using IsMulCommutative.is_comm.comm (eA a) (eA b))
    exponent_dvd_p := by
      rw [Monoid.exponent_eq_of_mulEquiv eA]
      exact IsElementaryAbelian.exponent_dvd_p 2 A }
  have hfour : IsKleinFour A₀ := LinearWitnesses.large_actor_isKleinFour
    (show IsOddPrimePower (Nat.card F) from ⟨3, 2, Nat.prime_three, by decide, by decide, hF⟩)
    (Or.inr ⟨MulEquiv.refl _⟩) A₀ (by rw [Group.rank_congr eA, hr]; decide)
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal L
  let S₀ := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hA₀S : A₀ ≤ (S₀ : Subgroup _) := by
    intro a ha
    change a ∈ (S : Subgroup L).map e.symm.toMonoidHom
    refine ⟨e a, ?_, e.symm_apply_apply a⟩
    rw [hS]
    exact hAT ha
  have hA₀L : A₀ ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range := by
    intro a ha
    obtain ⟨b, hb⟩ := (mem_pGammaL2PSLRange_iff F (i a)).mp (hAL ha)
    exact ⟨b, SemidirectProduct.inl_injective hb⟩
  obtain ⟨B, hBS, hBL, hB, _, _, hABN, he, hn⟩ :=
    LinearWitnesses.DiagonalPlacement.InnerSymmetric.exists_paired_inner_normalizer
      Nat.prime_three (by decide) (by decide) hF S₀ A₀ hfour hA₀S hA₀L
  refine ⟨hfour, B, hB, hBL, ?_, le_sup_left.trans hABN, he, hn⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbS := hBS hb
  change b ∈ (S : Subgroup L).map e.symm.toMonoidHom at hbS
  obtain ⟨s, hs, heq⟩ := hbS
  rw [hS] at hs
  have heq' : e b = s := by
    rw [← heq]
    exact e.apply_symm_apply s
  change i b ∈ (T : Subgroup _)
  change (e b).val ∈ (T : Subgroup _)
  rwa [heq']

private theorem map_singleton_centralizer {G : Type*} [Group G]
    (e : G ≃* G) (x : G) :
    (centralizer ({x} : Set G)).map e.toMonoidHom = centralizer ({e x} : Set G) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e z * e x = e x * e z
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hz)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

omit [Finite (PGammaL2 F)] in
/-- Every genuine field-involution centralizer over F₉ has order 48. -/
theorem fieldCentralizer_card (hF : Nat.card F = 3 ^ 2)
    (x : PGammaL2 F) (hx : orderOf x = 2) (hf : x.right ≠ 1) :
    Nat.card (centralizer ({x} : Set (PGammaL2 F))) = 48 := by
  have hq : IsOddPrimePower (Nat.card F) :=
    ⟨3, 2, Nat.prime_three, by decide, by decide, hF⟩
  obtain ⟨c, hc⟩ := projective_semilinear_involution_conj_inr hq x hx hf
  let a := MulAut.conj (SemidirectProduct.inl c : PGammaL2 F)⁻¹
  have ha : a x = SemidirectProduct.inr x.right := by
    simpa [a, MulAut.conj_apply] using hc
  have hsq : x.right ^ 2 = 1 := by
    change (SemidirectProduct.rightHom x) ^ 2 = 1
    have hh := congrArg (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F))
      (show x ^ 2 = 1 by simpa only [hx] using pow_orderOf_eq_one x)
    simpa only [map_pow, map_one] using hh
  have hmap := map_singleton_centralizer a x
  rw [ha] at hmap
  rw [← card_map_of_injective (f := a.toMonoidHom) a.injective, hmap,
    Nat.card_congr (smallFieldCentralizerEquiv hF x.right hsq hf).toEquiv,
    Nat.card_prod, FiniteField.card_ringAut_of_card_prime_pow Nat.prime_three hF]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

omit [Finite (PGammaL2 F)] in
/-- An intersection of order 16 is the literal Sylow subgroup of this
48-element centralizer. -/
theorem fieldCentralizer_sylow_of_card (hF : Nat.card F = 3 ^ 2)
    (T : Sylow 2 (PGammaL2 F)) (x : PGammaL2 F)
    (hx : orderOf x = 2) (hf : x.right ≠ 1)
    (hcard : Nat.card ((T : Subgroup _).subgroupOf
      (centralizer ({x} : Set (PGammaL2 F)))) = 16) :
    ∃ S : Sylow 2 (centralizer ({x} : Set (PGammaL2 F))),
      (S : Subgroup _) = (T : Subgroup _).subgroupOf (centralizer ({x} : Set _)) := by
  let P := (T : Subgroup _).subgroupOf (centralizer ({x} : Set (PGammaL2 F)))
  have hi : P.index = 3 := by
    have hh := P.card_mul_index
    rw [hcard, fieldCentralizer_card hF x hx hf] at hh
    omega
  have hP : IsPGroup 2 P := T.isPGroup'.comap_subtype
  exact ⟨hP.toSylow (by rw [hi]; decide), rfl⟩

/-- Reduction to two independent full-normalizer calculations. The paired
S₄ is chosen through the original inner actor, so the actor is nonnormal
in that S₄ and therefore has nontrivial image modulo the larger two-core.
The unconditional theorem below supplies both model hypotheses. -/
theorem nineFieldPlacement_of_normalizers (hF : Nat.card F = 3 ^ 2)
    (hfield : FourNormalizerField F) (hsyl : FourNormalizerSylowGeometry F) :
    NineFieldPlacement F := by
  intro T A hA hr hAL hAT
  let : Finite (PGL2 F) := Finite.of_injective
    (SemidirectProduct.inl : PGL2 F → PGammaL2 F) SemidirectProduct.inl_injective
  let i : PGL2 F →* PGammaL2 F := SemidirectProduct.inl
  obtain ⟨hfour, B, hB, hBL, hBT, hAN, ⟨e⟩, hn⟩ :=
    paired_linear_normalizer hF T A hA hr hAL hAT
  obtain ⟨x, hx, hf, hCN⟩ := hfield B hB hBL
  obtain ⟨hcard, hgen⟩ := hsyl T B hB hBL hBT
  let H := normalizer (B : Set (PGL2 F))
  let C := centralizer ({x} : Set (PGammaL2 F))
  have hHN : H.map i ≤ C := by
    change H.map i ≤ centralizer ({x} : Set (PGammaL2 F))
    rw [hCN]
    exact le_normalizer_map i
  have hmap : (A.comap i).map i = A :=
    map_comap_eq_self (hAL.trans inner_le_linear)
  have hAC : A ≤ C := by
    rw [← hmap]
    exact (map_mono hAN).trans hHN
  have hcent : x ∈ centralizer (A : Set (PGammaL2 F)) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hAC ha)
  let f : H →* C := (i.comp H.subtype).codRestrict C
    (fun y => hHN ⟨y, y.property, rfl⟩)
  have hinj : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    exact SemidirectProduct.inl_injective (congrArg Subtype.val hyz)
  let : IsKleinFour (A.comap i) := hfour
  let : IsKleinFour ((A.comap i).subgroupOf H) := klein_subgroupOf _ _ hAN
  have hnot : ¬ A.subgroupOf C ≤ pCore 2 C := by
    intro hc
    apply nonnormal_four_not_le_core_comap e f hinj ((A.comap i).subgroupOf H) hn
    intro a ha
    exact hc ha
  refine ⟨x, hx, hf, hcent, ?_, hnot, ?_⟩
  · apply fieldCentralizer_sylow_of_card hF T x hx hf
    rwa [hCN]
  · rwa [hCN]

/-- Actual application of the placement reduction to the S₃ quotient
constructor in `NineSections`. The original actor and ambient Sylow are
retained, and the constructed E₁ member generates the ambient group with T.
This conditional variant retains the two independent normalizer hypotheses. -/
theorem exists_fieldCentralizer_member_of_normalizers (hF : Nat.card F = 3 ^ 2)
    (hfield : FourNormalizerField F) (hsyl : FourNormalizerSylowGeometry F)
    (T : Sylow 2 (PGammaL2 F)) (A : Subgroup (PGammaL2 F))
    (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 2)
    (hAL : A ≤ pGammaL2PSLRange F) (hAT : A ≤ (T : Subgroup _)) :
    ∃ x : PGammaL2 F, orderOf x = 2 ∧ x.right ≠ 1 ∧
      IsEMemberAt 1 (T : Subgroup _) A (centralizer ({x} : Set (PGammaL2 F))) ∧
      (T : Subgroup _) ⊔ centralizer ({x} : Set (PGammaL2 F)) = ⊤ := by
  obtain ⟨x, hx, hf, hc, hS, ha, hgen⟩ :=
    nineFieldPlacement_of_normalizers hF hfield hsyl T A hA hr hAL hAT
  exact ⟨x, hx, hf, isEMemberAt_nine_fieldCentralizer hF T A hA hr
    (hAL.trans inner_le_linear) hAT x hx hf hc hS ha, hgen⟩

/-- Over every field of order nine, the original inner rank-two actor admits
a field-involution centralizer with the literal Sylow intersection, nontrivial
actor image modulo its two-core, and generation with the prescribed Sylow.
Both independent normalizer calculations are discharged. -/
theorem nineFieldPlacement (hF : Nat.card F = 3 ^ 2) : NineFieldPlacement F :=
  nineFieldPlacement_of_normalizers hF (fourNormalizerField hF)
    (SylowNormalizers.fourNormalizerSylowGeometry hF)

/-- The constructed field-involution centralizer is an actual E₁ member
for the original actor and Sylow, and generates the full group with that
Sylow. This applies the intrinsic S₃ quotient construction of `NineSections`
with every placement premise discharged. -/
theorem exists_fieldCentralizer_member (hF : Nat.card F = 3 ^ 2)
    (T : Sylow 2 (PGammaL2 F)) (A : Subgroup (PGammaL2 F))
    (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 2)
    (hAL : A ≤ pGammaL2PSLRange F) (hAT : A ≤ (T : Subgroup _)) :
    ∃ x : PGammaL2 F, orderOf x = 2 ∧ x.right ≠ 1 ∧
      IsEMemberAt 1 (T : Subgroup _) A (centralizer ({x} : Set (PGammaL2 F))) ∧
      (T : Subgroup _) ⊔ centralizer ({x} : Set (PGammaL2 F)) = ⊤ := by
  obtain ⟨x, hx, hf, hc, hS, ha, hgen⟩ := nineFieldPlacement hF T A hA hr hAL hAT
  exact ⟨x, hx, hf, isEMemberAt_nine_fieldCentralizer hF T A hA hr
    (hAL.trans inner_le_linear) hAT x hx hf hc hS ha, hgen⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry
