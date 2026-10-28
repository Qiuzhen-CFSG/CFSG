module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Reduction
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.SylowElementConjugacy
public import Mathlib.GroupTheory.Complement

/-!
# Excluding the two-point stabilizer from the two-core

This is the trivial-intersection step of GLS, Volume 4, Chapter 2,
Proposition 17.6. An element in the two-core cannot invert a nonidentity
odd-order element. All involutions of a group with cyclic Sylow
two-subgroups are conjugate. Thus an inverter in the two-point stabilizer
excludes every involution of that stabilizer from the two-core; Cauchy's
theorem gives trivial intersection. The required inverter is still an
explicit input from the local counting and model analysis.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem not_mem_twoCore_of_odd_inverted {u x : G}
    (hxodd : Odd (orderOf x)) (hxne : x ≠ 1)
    (hinv : u * x * u⁻¹ = x⁻¹) : u ∉ pCore 2 G := by
  intro hu
  let P := pCore 2 G
  let f : G →* G ⧸ P := QuotientGroup.mk' P
  have hfu : f u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
  have hfx : f x = (f x)⁻¹ := by
    simpa only [map_mul, map_inv, hfu, one_mul, inv_one, mul_one] using congrArg f hinv
  have hsquare : (f x) ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [hfx]
    exact inv_mul_cancel _
  have ho : Odd (orderOf (f x)) := hxodd.of_dvd_nat (orderOf_map_dvd f x)
  have hfxone : f x = 1 := by
    apply orderOf_eq_one_iff.mp
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsquare) with h1 | h2
    · exact h1
    · exact False.elim ((by decide : ¬ Odd 2) (h2 ▸ ho))
  have hxP : x ∈ P := (QuotientGroup.eq_one_iff x).mp hfxone
  have hpow := (IsPGroup.iff_orderOf.mp (pCore_isPGroup (p := 2) (G := G))) ⟨x, hxP⟩
  obtain ⟨k, hk⟩ := hpow
  have hk' : orderOf x = 2 ^ k := by simpa using hk
  have hk0 : k = 0 := by
    by_contra hk0
    exact hxodd.not_two_dvd_nat (hk' ▸ dvd_pow_self 2 hk0)
  exact hxne (orderOf_eq_one_iff.mp (by simpa [hk0] using hk'))

private theorem isConj_of_cyclic_sylow_two
    (D : Type*) [Group D] [Finite D] (hcyc : ∀ S : Sylow 2 D, IsCyclic S)
    {x y : D} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  let S : Sylow 2 D := Classical.choice inferInstance
  let : IsCyclic S := hcyc S
  obtain ⟨a, ha⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  obtain ⟨b, hb⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hy)
  have hao : orderOf a = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp ha
    change MulAut.conj g x = (a : D) at hg
    rw [← Subgroup.orderOf_coe, ← hg, MulEquiv.orderOf_eq, hx]
  have hbo : orderOf b = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hb
    change MulAut.conj g y = (b : D) at hg
    rw [← Subgroup.orderOf_coe, ← hg, MulEquiv.orderOf_eq, hy]
  have hab : a = b := IsCyclic.eq_of_orderOf_eq_two hao hbo
  exact ha.trans (hab ▸ hb.symm)

private theorem disjoint_twoCore_of_inverter
    (D : Subgroup G) (hcyc : ∀ S : Sylow 2 D, IsCyclic S)
    (u : D) (hu : orderOf u = 2) (x : G)
    (hxodd : Odd (orderOf x)) (hxne : x ≠ 1)
    (hinv : (u : G) * x * (u : G)⁻¹ = x⁻¹) : Disjoint D (pCore 2 G) := by
  have hunot := not_mem_twoCore_of_odd_inverted hxodd hxne hinv
  apply disjoint_iff_inf_le.mpr
  by_contra hh
  have hne : D ⊓ pCore 2 G ≠ ⊥ := by simpa using hh
  let K := D ⊓ pCore 2 G
  let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  have hK : IsPGroup 2 K := IsPGroup.to_le pCore_isPGroup inf_le_right
  obtain ⟨n, hn, hcard⟩ := hK.nontrivial_iff_card.mp inferInstance
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := K) 2
    (hcard ▸ dvd_pow_self 2 (by omega))
  let vD : D := ⟨v, v.property.1⟩
  have hvD : orderOf vD = 2 := by simpa [vD] using hv
  obtain ⟨d, hd⟩ := isConj_iff.mp (isConj_of_cyclic_sylow_two D hcyc hvD hu)
  have hmem : (d : G) * (v : G) * (d : G)⁻¹ ∈ pCore 2 G :=
    (inferInstance : (pCore 2 G).Normal).conj_mem v v.property.2 d
  apply hunot
  have heq := congrArg Subtype.val hd
  change (d : G) * (v : G) * (d : G)⁻¹ = (u : G) at heq
  rwa [heq] at hmem

/-- Transport Section 16's cyclic-Sylow conclusion to the internal
copy of the two-point stabilizer. -/
public theorem residualPairIn_cyclic_sylow_of_local {Z : Set G} {M : Subgroup G} (h : IsProductDisconnected Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    {t : G} (ht : t ∉ M) : ∀ S : Sylow 2 (residualPairIn M t), IsCyclic S := by
  intro S
  let e := residualPairInEquiv M t
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let eS : S ≃* T := (S : Subgroup (residualPairIn M t)).equivMapOfInjective
    e.toMonoidHom e.injective
  let : IsCyclic T := (hlocal _ (residualPairStabilizer_localClosure_eq_bot h ht)).2 T
  exact isCyclic_of_surjective eS.symm eS.symm.surjective


/-- The inverter data from Section 17 excludes the entire intersection,
not just the chosen involution. Normality here is inside `M`. -/
public theorem TwoCoreCountingData.disjoint_twoCore
    {Z : Set G} {M : Subgroup G} (d : TwoCoreCountingData Z M)
    (h : IsProductDisconnected Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S) :
    Disjoint (residualPairIn M d.t) (pCore 2 M) :=
  disjoint_twoCore_of_inverter _
    (residualPairIn_cyclic_sylow_of_local h hlocal d.t_not_mem)
    d.u d.u_order d.x d.x_odd d.x_ne d.inverts

end BenderSuzuki.ZD
