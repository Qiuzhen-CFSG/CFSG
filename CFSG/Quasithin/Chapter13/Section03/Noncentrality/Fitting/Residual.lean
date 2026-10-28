module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Quotient
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.Quasithin.Rank

/-!
# The residual preimage in 13.3.14(d)

For an odd subgroup D of the literal star quotient H/O₂(H), take its full
preimage and then its two-residual. Its image is D and its intrinsic two-core
quotient is D, through the original quotient map. Rank two therefore forces
this residual to move U whenever O²(C_G(U)) has odd-prime rank at most one.

These statements construct the source residual after D is supplied. They do
not select the supercritical subgroup or assert its membership in Ξ.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.3.14(d), printed p.892, PDF p.909.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
variable {G : Type*} [Group G]

/-- The full preimage P₊ of D in H under H → H/O₂(H). -/
def starPreimage (H : Subgroup G) (D : Subgroup (Star H)) : Subgroup H :=
  D.comap (QuotientGroup.mk' (pCore 2 H))

/-- The source P=O²(P₊), embedded in H; this is not a prime core. -/
def starResidual (H : Subgroup G) (D : Subgroup (Star H)) : Subgroup H :=
  (pResidual 2 (starPreimage H D)).map (starPreimage H D).subtype

/-- The chosen residual is two-perfect. -/
theorem starResidual_isPPerfect [Finite G] (H : Subgroup G) (D : Subgroup (Star H)) :
    IsPPerfect 2 (starResidual H D) := isPPerfect_embedded_pResidual 2 _

/-- A normal star subgroup has a normal residual preimage in H. -/
theorem starResidual_normal [Finite G] (H : Subgroup G) (D : Subgroup (Star H))
    [D.Normal] : (starResidual H D).Normal := by
  unfold starResidual starPreimage
  infer_instance

/-- Taking the two-residual preserves the image when the star subgroup is two-perfect. -/
theorem starResidual_image [Finite G] (H : Subgroup G) (D : Subgroup (Star H))
    (hD : IsPPerfect 2 D) :
    (starResidual H D).map (QuotientGroup.mk' (pCore 2 H)) = D := by
  rw [starResidual, map_embedded_pResidual]
  have he : (starPreimage H D).map (QuotientGroup.mk' (pCore 2 H)) = D :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) D
  rw [he, (pResidual_eq_top_iff 2 D).mpr hD, ← MonoidHom.range_eq_map, range_subtype]

/-- Restriction of the original star projection, with codomain its exact image D. -/
noncomputable def starResidualProjection [Finite G] (H : Subgroup G)
    (D : Subgroup (Star H)) (hD : IsPPerfect 2 D) : starResidual H D →* D :=
  (MulEquiv.subgroupCongr (starResidual_image H D hD)).toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (starResidual H D))

/-- The residual projection is literally the original quotient map. -/
theorem starResidualProjection_coe [Finite G] (H : Subgroup G)
    (D : Subgroup (Star H)) (hD : IsPPerfect 2 D) (x : starResidual H D) :
    (starResidualProjection H D hD x : Star H) =
      QuotientGroup.mk' (pCore 2 H) (x : H) := rfl

/-- The residual maps onto D. -/
theorem starResidualProjection_surjective [Finite G] (H : Subgroup G)
    (D : Subgroup (Star H)) (hD : IsPPerfect 2 D) :
    Function.Surjective (starResidualProjection H D hD) :=
  (MulEquiv.subgroupCongr (starResidual_image H D hD)).surjective.comp
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)

/-- The kernel is the intersection with H’s two-core. -/
theorem starResidualProjection_kernel [Finite G] (H : Subgroup G)
    (D : Subgroup (Star H)) (hD : IsPPerfect 2 D) :
    (starResidualProjection H D hD).ker = (pCore 2 H).comap (starResidual H D).subtype := by
  rw [starResidualProjection, MonoidHom.ker_comp_of_injective _ _
    (MulEquiv.subgroupCongr _).injective, ker_subgroupMap, QuotientGroup.ker_mk']
  rfl

/-- Identify the intrinsic two-core quotient with D when D has trivial two-core. -/
noncomputable def starResidualCoreEquiv [Finite G] (H : Subgroup G)
    (D : Subgroup (Star H)) (hD : IsPPerfect 2 D) (hcore : pCore 2 D = ⊥) :
    (starResidual H D ⧸ pCore 2 (starResidual H D)) ≃* D := by
  let f := starResidualProjection H D hD
  have hf := starResidualProjection_surjective H D hD
  have hk : IsPGroup 2 f.ker := by
    rw [starResidualProjection_kernel]
    exact pCore_isPGroup.comap_of_injective _ (starResidual H D).subtype_injective
  have he : f.ker = pCore 2 (starResidual H D) := by
    have hh := f.comap_pCore_of_ker_isPGroup hf hk
    rw [hcore] at hh
    exact hh
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The quotient equivalence is induced by the original star projection. -/
theorem starResidualCoreEquiv_mk_coe [Finite G] (H : Subgroup G)
    (D : Subgroup (Star H)) (hD : IsPPerfect 2 D) (hcore : pCore 2 D = ⊥)
    (x : starResidual H D) :
    (starResidualCoreEquiv H D hD hcore
      (QuotientGroup.mk' (pCore 2 (starResidual H D)) x) : Star H) =
        QuotientGroup.mk' (pCore 2 H) (x : H) := rfl

/-- An odd-prime group has no nontrivial two-group quotient. -/
theorem odd_pGroup_isTwoPerfect {D : Type*} [Group D] {p : ℕ}
    (hp : Odd p) (hD : IsPGroup p D) : IsPPerfect 2 D := by
  apply (pResidual_eq_top_iff 2 D).mp
  apply top_unique
  intro x _
  exact mem_pResidual_of_orderOf_coprime
    (hD.orderOf_coprime (Nat.coprime_two_right.mpr hp) x).symm

/-- An odd-prime group has trivial two-core. -/
theorem odd_pGroup_twoCore_eq_bot {D : Type*} [Group D] [Finite D] {p : ℕ}
    [Fact p.Prime] (hp : Odd p) (hD : IsPGroup p D) : pCore 2 D = ⊥ := by
  have he := pCore_isPGroup.disjoint_of_coprime (hD.to_subgroup (⊤ : Subgroup D))
    (Nat.coprime_two_left.mpr hp)
  exact (disjoint_top.mp he)

/-- The source P/O₂(P) ≅ P* for every odd star subgroup. -/
noncomputable def oddStarResidualCoreEquiv [Finite G] (H : Subgroup G)
    (D : Subgroup (Star H)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hD : IsPGroup p D) :
    (starResidual H D ⧸ pCore 2 (starResidual H D)) ≃* D :=
  starResidualCoreEquiv H D (odd_pGroup_isTwoPerfect hp hD)
    (odd_pGroup_twoCore_eq_bot hp hD)

/-- A two-perfect centralizing subgroup lies in the actual centralizing residual. -/
theorem twoPerfect_le_centralizingResidual {P U : Subgroup G}
    (hP : IsPPerfect 2 P) (hc : P ≤ centralizer (U : Set G)) :
    P ≤ centralizingResidual U := by
  have hm := map_pResidual_le 2 (inclusion hc)
  rw [(pResidual_eq_top_iff 2 P).mpr hP] at hm
  intro x hx
  exact mem_map.mpr ⟨inclusion hc ⟨x, hx⟩,
    hm (mem_map.mpr ⟨⟨x, hx⟩, trivial, rfl⟩), rfl⟩

/-- Rank above one prevents a two-perfect subgroup from centralizing U. -/
theorem twoPerfect_moves_of_centralizingResidual_rank [Finite G]
    (P U : Subgroup G) (hP : IsPPerfect 2 P) (p : ℕ) [Fact p.Prime]
    (hr : 1 < primeRank p P) (hY : primeRank p (centralizingResidual U) ≤ 1) :
    ⁅U, P⁆ ≠ ⊥ := by
  intro hc
  have hle := twoPerfect_le_centralizingResidual hP
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
  have hb := (_root_.primeRank_le_of_injective p (inclusion hle) (inclusion_injective hle)).trans hY
  omega

/-- Apply reduction (b) to the actual residual preimage of a rank-two star subgroup. -/
theorem starResidual_moves_of_rank [Finite G]
    (H U : Subgroup G) (D : Subgroup (Star H)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hD : IsPGroup p D) (hr : 1 < primeRank p D)
    (hY : primeRank p (centralizingResidual U) ≤ 1) :
    ⁅U, (starResidual H D).map H.subtype⁆ ≠ ⊥ := by
  let e := (starResidual H D).equivMapOfInjective H.subtype H.subtype_injective
  apply twoPerfect_moves_of_centralizingResidual_rank _ U
    ((starResidual_isPPerfect H D).of_surjective e.toMonoidHom e.surjective) p _ hY
  have hrank := primeRank_quotient_le_of_isTwoGroup p hp
    (pCore 2 (starResidual H D)) pCore_isPGroup
  rw [primeRank_congr p (oddStarResidualCoreEquiv H D hp hD)] at hrank
  rw [← primeRank_congr p e]
  exact hr.trans_le hrank

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
