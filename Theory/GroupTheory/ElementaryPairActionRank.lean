module
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.LayerRankOrbit
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Theory.Representation.BinaryOffender.Basic

/-!
# The actual elementary action on two exchanged components

If an elementary abelian group A exchanges J and J^a, an element of
N_A(J) fixing J pointwise also fixes J^a, since it commutes with a.
The action on their join therefore has rank at most m2(Aut(J)) + 1:
one factor action and the quotient of order two account for the whole
image. A pointwise kernel on the pair is allowed, and no ambient normality
of J is assumed.

The central Hall Suzuki support argument uses this with its original
component orbit and quotient kernel.
Source: Aschbacher--Smith D.3.9, printed pp.200--201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- An exchanged pair adds at most one to the factor automorphism rank. -/
theorem elementary_exchanged_pair_action_rank
    (J A : Subgroup G) [IsElementaryAbelian 2 A]
    (a : G) (ha : a ∈ A)
    (hi : (normalizer (J : Set G)).relIndex A = 2)
    (he : componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom) :
    Representation.BinaryOffender.rank
      ((componentOrbit J A).normalizerMonoidHom.comp
        (inclusion (le_normalizer_componentOrbit J A))).range ≤
      primeRank 2 (MulAut J) + 1 := by
  let X := componentOrbit J A
  let α := X.normalizerMonoidHom.comp (inclusion (le_normalizer_componentOrbit J A))
  let E := α.range
  let f : A →* E := α.rangeRestrict
  let N := (normalizer (J : Set G)).subgroupOf A
  let E₀ := N.map f
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.of_injective N.subtype N.subtype_injective
  have hNi : N.index = 2 := hi
  let η : N →* MulAut J := J.normalizerMonoidHom.comp
    { toFun b := ⟨b.val.val,b.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let β := f.comp N.subtype
  have hk : η.ker ≤ β.ker := by
    intro b hb
    have hbc : (b.val : G) ∈ centralizer (J : Set G) := by
      intro j hj
      have hh := congrArg (fun u : MulAut J => (u ⟨j,hj⟩ : G)) hb
      change (b.val : G)*j*(b.val : G)⁻¹=j at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hba : (b.val : G)*a = a*(b.val : G) :=
      congrArg Subtype.val (mul_comm b.val (⟨a,ha⟩ : A))
    have hbai : (b.val : G)*a⁻¹ = a⁻¹*(b.val : G) :=
      congrArg Subtype.val (mul_comm b.val ((⟨a,ha⟩ : A)⁻¹))
    have hcx : X ≤ centralizer ({(b.val : G)} : Set G) := by
      rw [show X = J ⊔ J.map (MulAut.conj a).toMonoidHom from he]
      apply sup_le
      · intro j hj
        exact mem_centralizer_singleton_iff.mpr (hbc j hj)
      · rintro j ⟨k,hk,rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        change (a*k*a⁻¹)*(b.val : G) = (b.val : G)*(a*k*a⁻¹)
        calc
          (a*k*a⁻¹)*(b.val : G) = a*(k*(a⁻¹*(b.val : G))) := by group
          _ = a*(k*((b.val : G)*a⁻¹)) := by rw [←hbai]
          _ = a*((b.val : G)*(k*a⁻¹)) := by rw [←mul_assoc k,hbc k hk,mul_assoc]
          _ = (b.val : G)*(a*k*a⁻¹) := by rw [←mul_assoc,←hba]; group
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (b.val : G)*x*(b.val : G)⁻¹=x
    have hc := mem_centralizer_singleton_iff.mp (hcx x.property)
    rw [←hc,mul_assoc,mul_inv_cancel,mul_one]
  have hcard : Nat.card E₀ ≤ Nat.card η.range := by
    have hr : β.range = E₀ := by rw [MonoidHom.range_comp,range_subtype]
    rw [←hr]
    have hd := index_dvd_of_le hk
    rw [index_ker,index_ker] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have helem : IsElementaryAbelian 2 η.range :=
    IsElementaryAbelian.of_surjective η.rangeRestrict η.rangeRestrict_surjective
  have hb := (primeRank_le_iff_elementary_card_le (p := 2) (MulAut J)).mp le_rfl η.range helem
  have hidx : E₀.index ≤ 2 := Nat.le_of_dvd (by decide)
    (hNi ▸ N.index_map_dvd α.rangeRestrict_surjective)
  have hc : Nat.card E ≤ 2^(primeRank 2 (MulAut J)+1) := by
    calc
      Nat.card E = Nat.card E₀ * E₀.index := E₀.card_mul_index.symm
      _ ≤ 2^(primeRank 2 (MulAut J))*2 := Nat.mul_le_mul (hcard.trans hb) hidx
      _ = _ := (pow_succ _ _).symm
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [Representation.BinaryOffender.rank,Nat.log_pow (by decide : 1<2)] using hh

/-- For a moved component of a layer of odd rank at most two, the actual
orbit action has the same factor-plus-one bound. -/
theorem elementary_component_exchanged_orbit_action_rank
    (J A : Subgroup G) [IsElementaryAbelian 2 A] (hJ : IsComponent G J)
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p (componentLayer G) ≤ 2)
    (hAJ : ¬ A ≤ normalizer (J : Set G)) :
    Representation.BinaryOffender.rank
      ((componentOrbit J A).normalizerMonoidHom.comp
        (inclusion (le_normalizer_componentOrbit J A))).range ≤
      primeRank 2 (MulAut J) + 1 := by
  have hi : (normalizer (J : Set G)).index = 2 :=
    (hJ.normal_or_index_two_of_layer_odd_rank_le_two hrank).resolve_left
      (fun hj => hAJ (by
        let := hj
        exact le_top.trans (normalizer_eq_top J).ge))
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hAJ
  let N := normalizer (J : Set G)
  let : N.Normal := normal_of_index_eq_two hi
  have hd : N.relIndex A ∣ 2 := by
    simpa only [show N.index = 2 from hi] using N.relIndex_dvd_index_of_normal A
  have hirel : N.relIndex A = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun he => hAJ (Subgroup.relIndex_eq_one.mp he))
  have heq : componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two J A N hirel inf_le_right ha han
  exact elementary_exchanged_pair_action_rank J A a ha hirel heq

end Theory.GroupTheory
