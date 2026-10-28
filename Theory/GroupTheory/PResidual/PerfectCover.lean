module

public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Perfect residuals and covering modulo a normal subgroup

In a finite group the p-residual is p-perfect: the quotient by its iterated
residual is an extension of two p-groups and hence a p-group. A covering
`X ⊆ I N`, with `N` normal in `X` and `X` p-perfect, therefore remains a
covering after replacing `X ∩ I` by its p-residual. The proof maps onto
`X/N` and uses preservation of residuals under finite surjections.

We also record monotonicity and relative normality for residuals embedded
in a common ambient group. These statements involve no classification
hypotheses. Application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), proof of Lemma 4.1.4,
printed pp. 606–607.
-/

public section

namespace Subgroup


variable {G : Type*} [Group G]

/-- The p-residual of a finite group is p-perfect. -/
theorem isPPerfect_pResidual [Finite G] (p : ℕ) : IsPPerfect p (pResidual p G) := by
  let R := pResidual p G
  let S := pResidual p R
  let K := S.map R.subtype
  have hK : IsPGroup p (G ⧸ K) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
    obtain ⟨n, hn⟩ := Subgroup.isPGroup_quotient_pResidual (G := G) p
      (QuotientGroup.mk' R g)
    have hgn : g ^ p ^ n ∈ R := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' R (g ^ p ^ n) = 1
      rw [map_pow]
      exact hn
    obtain ⟨m, hm⟩ := Subgroup.isPGroup_quotient_pResidual (G := R) p
      (QuotientGroup.mk' S ⟨g ^ p ^ n, hgn⟩)
    have hgm : (⟨g ^ p ^ n, hgn⟩ : R) ^ p ^ m ∈ S := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' S ((⟨g ^ p ^ n, hgn⟩ : R) ^ p ^ m) = 1
      rw [map_pow]
      exact hm
    refine ⟨n + m, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact mem_map.mpr ⟨_, hgm, by simp only [coe_pow, subtype_apply, pow_add, pow_mul]⟩
  have hRK : R ≤ K := sInf_le ⟨inferInstance, hK⟩
  apply (pResidual_eq_top_iff p R).mp
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := mem_map.mp (hRK x.property)
  have : y = x := Subtype.ext he
  exact this ▸ hy

open scoped Pointwise

/-- A cover modulo a normal subgroup of a p-perfect group is already a
cover by the residual of the intersection. Products are literal set products. -/
theorem eq_mul_embedded_pResidual_of_cover [Finite G] (p : ℕ)
    (X I : Subgroup G) (N : Subgroup X) [N.Normal]
    (hX : IsPPerfect p X)
    (hcover : (X : Set G) ⊆ (I : Set G) * (N.map X.subtype : Set G)) :
    (X : Set G) =
      ((pResidual p (X ⊓ I : Subgroup G)).map (X ⊓ I).subtype : Set G) *
        (N.map X.subtype : Set G) := by
  let f : (X ⊓ I : Subgroup G) →* X ⧸ N :=
    (QuotientGroup.mk' N).comp (inclusion inf_le_left)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨i, hi, n, hn, he⟩ := Set.mem_mul.mp (hcover x.property)
    obtain ⟨n', hn', rfl⟩ := mem_map.mp hn
    change i * (n' : G) = (x : G) at he
    have hiX : i ∈ X := by
      have hie : i = (x : G) * (n' : G)⁻¹ := by rw [← he]; group
      rw [hie]
      exact X.mul_mem x.property (X.inv_mem n'.property)
    refine ⟨⟨i, hiX, hi⟩, ?_⟩
    apply QuotientGroup.eq.mpr
    have hie : ((⟨i, hiX⟩ : X)⁻¹ * x) = n' := by
      apply Subtype.ext
      change i⁻¹ * (x : G) = n'
      rw [← he]
      group
    change ((⟨i, hiX⟩ : X)⁻¹ * x) ∈ N
    simpa only [hie] using hn'
  have hq : IsPPerfect p (X ⧸ N) :=
    hX.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hr : (pResidual p (X ⊓ I : Subgroup G)).map f = ⊤ := by
    rw [map_pResidual_of_surjective p f hf, (pResidual_eq_top_iff p _).mpr hq]
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨r, hr, he⟩ := mem_map.mp (show QuotientGroup.mk' N ⟨x, hx⟩ ∈
      (pResidual p (X ⊓ I : Subgroup G)).map f by rw [hr]; trivial)
    have hn : (⟨r.val, r.property.1⟩ : X)⁻¹ * ⟨x, hx⟩ ∈ N :=
      QuotientGroup.eq.mp he
    exact Set.mem_mul.mpr ⟨r.val, mem_map.mpr ⟨r, hr, rfl⟩,
      r.val⁻¹ * x, mem_map.mpr ⟨_, hn, rfl⟩, by group⟩
  · rintro x ⟨r, hr, n, hn, rfl⟩
    exact X.mul_mem ((map_subtype_le _ hr).1) (map_subtype_le _ hn)

/-- Embedded p-residuals are monotone in the ambient subgroup. -/
theorem embedded_pResidual_mono (p : ℕ) {X Y : Subgroup G} (hXY : X ≤ Y) :
    (pResidual p X).map X.subtype ≤ (pResidual p Y).map Y.subtype := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  exact mem_map.mpr ⟨inclusion hXY a,
    map_pResidual_le p (inclusion hXY) (mem_map.mpr ⟨a, ha, rfl⟩), rfl⟩

/-- The embedded residual of a relatively normal subgroup is relatively normal. -/
theorem normal_embedded_pResidual_subgroupOf (p : ℕ) {X M : Subgroup G} (hXM : X ≤ M)
    (hN : (X.subgroupOf M).Normal) :
    (((pResidual p X).map X.subtype).subgroupOf M).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans hXM)).mpr
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  have hgN := (normal_subgroupOf_iff_le_normalizer hXM).mp hN hg
  let f := X.normalizerMonoidHom ⟨g, hgN⟩
  exact mem_map.mpr ⟨f a,
    map_pResidual_le p f.toMonoidHom (mem_map.mpr ⟨a, ha, rfl⟩), rfl⟩

/-- Viewing a finite residual in an ambient group preserves p-perfectness. -/
theorem isPPerfect_embedded_pResidual [Finite G] (p : ℕ) (X : Subgroup G) :
    IsPPerfect p ((pResidual p X).map X.subtype) := by
  let e := (pResidual p X).equivMapOfInjective X.subtype X.subtype_injective
  exact (isPPerfect_pResidual (G := X) p).of_surjective e.toMonoidHom e.surjective

end Subgroup
