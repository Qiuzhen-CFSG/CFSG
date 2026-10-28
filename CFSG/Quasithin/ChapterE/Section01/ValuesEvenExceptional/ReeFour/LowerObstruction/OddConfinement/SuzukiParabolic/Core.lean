module

public import Theory.SpecificGroups.Suzuki.ElementaryNormalizer
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki
public import Theory.GroupTheory.PCoreSurjective

/-!
# Intrinsic two-core control in the full Suzuki Levi

A nontrivial normal two-subgroup projects nontrivially onto the Suzuki factor,
because the complementary field torus has odd order. Sylow conjugacy and the
ovoid fixed-point theorem put its normalizer in a Borel. The normal root Sylow,
together with the trivial torus coordinate of every two-element, then contains
all two-subgroups of the original subgroup and is its intrinsic two-core.

This is the Levi input for the Suzuki-parabolic root-rank calculation in
Aschbacher--Smith E.1.14(1), printed p.214 of `refs/quasithin.pdf`, citing
Aschbacher (1982), Lemma 4.7. The ovoid geometry is Huppert--Blackburn XI.3.3.
The application to the literal Ree projection is in the parent module.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
open Subgroup ReeF4 BenderSuzuki.MatrixGroups

private theorem twoGroup_hom_to_odd_eq_one {G D : Type*} [Group G] [Group D]
    [Finite D] (hG : IsPGroup 2 G) (hD : Odd (Nat.card D)) (f : G →* D) (x : G) :
    f x = 1 := by
  obtain ⟨n, hn⟩ := hG x
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hD.coprime_two_right.pow_right n)
    (orderOf_dvd_natCard _) (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hn, map_one]))

private theorem suzuki_product_twoSubgroup_le_core
    {D : Type*} [CommGroup D] [Finite D] {m : ℕ} (hm : 0 < m)
    (hD : Odd (Nat.card D)) (R : Subgroup (SuzukiMatrixGroup m × D))
    (hne : pCore 2 R ≠ ⊥) (B : Subgroup R) (hB : IsPGroup 2 B) :
    B ≤ pCore 2 R := by
  let f : R →* SuzukiMatrixGroup m := (MonoidHom.fst _ _).comp R.subtype
  let t : R →* D := (MonoidHom.snd _ _).comp R.subtype
  have ht : ∀ C : Subgroup R, IsPGroup 2 C → ∀ x ∈ C, t x = 1 := by
    intro C hC x hx
    exact twoGroup_hom_to_odd_eq_one hC hD (t.comp C.subtype) ⟨x, hx⟩
  have hN : (pCore 2 R).map f ≠ ⊥ := by
    intro hz
    apply hne
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    apply Prod.ext
    · exact mem_bot.mp (hz ▸ mem_map_of_mem f hx)
    · exact ht _ pCore_isPGroup x hx
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨Q, hQ⟩ := (pCore_isPGroup (p := 2) (G := R)).map f |>.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) Q P
  let F : R →* SuzukiMatrixGroup m := (MulAut.conj g).toMonoidHom.comp f
  let W := (pCore 2 R).map F
  have hWR : W ≤ SuzukiRootSubgroup m := by
    rw [← hP, ← hg]
    rintro x ⟨v, hv, rfl⟩
    exact ⟨f v, hQ (mem_map_of_mem f hv), rfl⟩
  have hW : W ≠ ⊥ := by
    intro hz
    apply hN
    apply (((pCore 2 R).map f).map_eq_bot_iff_of_injective
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mp
    simpa only [map_map] using hz
  have hFn : F.range ≤ normalizer (W : Set (SuzukiMatrixGroup m)) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using
      (pCore 2 R).le_normalizer_map F
  have hFb : F.range ≤ SuzukiBorelSubgroup m :=
    hFn.trans (suzuki_normalizer_le_borel_of_le_root m hm W hW hWR)
  have hFnR : F.range ≤ normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) := by
    rwa [suzukiRootSubgroup_normalizer m hm]
  let C := (SuzukiRootSubgroup m).comap F ⊓ t.ker
  have hCn : C.Normal := by
    refine ⟨?_⟩
    intro x hx y
    constructor
    · change F (y * x * y⁻¹) ∈ SuzukiRootSubgroup m
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp (hFnR ⟨y, rfl⟩) _).mp hx.1
    · exact (inferInstance : t.ker.Normal).conj_mem x hx.2 y
  let cF : C →* SuzukiRootSubgroup m :=
    (F.comp C.subtype).codRestrict _ (fun x => x.property.1)
  have hcF : Function.Injective cF := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (MulAut.conj g).injective (congrArg Subtype.val hxy)
    · exact x.property.2.trans y.property.2.symm
  have hCp : IsPGroup 2 C := (hP ▸ P.isPGroup').of_injective cF hcF
  have hCc : C ≤ pCore 2 R := le_sSup ⟨hCn, hCp⟩
  apply le_trans ?_ hCc
  have hBn : B.map F ≤ normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) :=
    (map_le_range F B).trans hFnR
  have hBR : B.map F ≤ SuzukiRootSubgroup m := by
    calc
      B.map F = B.map F ⊓ normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) :=
        (inf_eq_left.mpr hBn).symm
      _ = B.map F ⊓ (P : Subgroup (SuzukiMatrixGroup m)) := by
        rw [← hP]
        exact (hB.map F).inf_normalizer_sylow P
      _ ≤ SuzukiRootSubgroup m := hP ▸ inf_le_right
  intro b hb
  exact ⟨hBR (mem_map_of_mem F hb), ht B hB b hb⟩

/-- In the genuine full Suzuki Levi, a subgroup with nontrivial two-core has
all of its two-subgroups in that intrinsic core, including the odd torus. -/
theorem suzukiLevi_twoSubgroup_le_core {m : ℕ} (hm : 0 < m)
    (R : Subgroup (SuzukiMatrixGroup m × (CoefficientField m)ˣ))
    (hne : pCore 2 R ≠ ⊥) (B : Subgroup R) (hB : IsPGroup 2 B) :
    B ≤ pCore 2 R := by
  apply suzuki_product_twoSubgroup_le_core hm _ R hne B hB
  rw [Nat.card_units, field_card]
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    (Even.pow_of_ne_zero even_two (by omega)) odd_one

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
