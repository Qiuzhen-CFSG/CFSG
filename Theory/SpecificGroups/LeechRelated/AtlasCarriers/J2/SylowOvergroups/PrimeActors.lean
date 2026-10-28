module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OrdinaryLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.CoverSquareOrbit
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Theory.GroupTheory.SolvableSylowOvergroups.OrderActors

/-!
# Quintic actors and proper Sylow overgroups in Hall–Janko

The certified full-Sylow cover puts each proper overgroup into the two
actual locals of orders 1920 and 1152. A three-free overgroup containing
five would have order 640 in the first local, hence index three. That
local is perfect, so its action on three cosets is trivial, a contradiction.
The second local is five-free. The outer two-group calculation then
excludes a faithful quintic actor on a normal J₂ factor when the actual
actor–Sylow join has order dividing a power of two times five.

The Chapter6 original Cartan consumer retains its literal two-core
quotients and Sylow marking. Source: Aschbacher–Smith A.3.12(16) and5.2.2,
printed pp.47–48 and648–649. The imported native coverage retains the
ATLAS J2G1-p100B0 attribution, license and checked word certificates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.SylowOvergroups
open ExceptionalParabolics

private theorem conjugate_cover (S : Sylow 2 Carrier) (P : Subgroup Carrier)
    (hSP : (S : Subgroup Carrier) ≤ P) (hP : P ≠ ⊤) :
    ∃ c : Carrier ≃* Carrier,
      (Seed.s ≤ P.map c.toMonoidHom) ∧
      (P.map c.toMonoidHom ≤ Seed.l₁ ∨ P.map c.toMonoidHom ≤ Seed.p₂) := by
  let S₀ := SecondParabolic.sylow FirstParabolic.card_l₁
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S S₀
  let c := MulAut.conj g
  have hS : (S : Subgroup Carrier).map c.toMonoidHom = Seed.s :=
    congrArg Sylow.toSubgroup hg
  have hPc : P.map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hP
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  exact ⟨c,hS ▸ map_mono hSP,proper_overgroup_le _ (hS ▸ map_mono hSP) hPc⟩

/-- Every proper full-Sylow overgroup has order dividing one of the two native local orders. -/
theorem proper_overgroup_order (S : Sylow 2 Carrier) (P : Subgroup Carrier)
    (hSP : (S : Subgroup Carrier) ≤ P) (hP : P ≠ ⊤) :
    Nat.card P ∣ 1920 ∨ Nat.card P ∣ 1152 := by
  obtain ⟨c,_,hc⟩ := conjugate_cover S P hSP hP
  have he := Nat.card_congr (c.subgroupMap P).toEquiv
  rcases hc with hc | hc
  · exact .inl (he ▸ FirstParabolic.card_l₁ ▸ card_dvd_of_le hc)
  · exact .inr (he ▸ PairNormalizer.card_p₂ ▸ card_dvd_of_le hc)

/-- A three-free full-Sylow overgroup contains no element of order five. -/
theorem not_five_of_three_free (S : Sylow 2 Carrier) (P : Subgroup Carrier)
    (hSP : (S : Subgroup Carrier) ≤ P) (h3 : ¬ 3 ∣ Nat.card P) :
    ¬ 5 ∣ Nat.card P := by
  have hP : P ≠ ⊤ := by
    intro he
    apply h3
    rw [he,card_top,FirstParabolic.card_carrier]
    decide
  obtain ⟨c,hsc,hc⟩ := conjugate_cover S P hSP hP
  let J := P.map c.toMonoidHom
  have he : Nat.card J = Nat.card P := card_map_of_injective c.injective
  intro h5
  rcases hc with hc | hc
  · have hd : Nat.card J ∣ 1920 := FirstParabolic.card_l₁ ▸ card_dvd_of_le hc
    have h128 : 128 ∣ Nat.card J := PairNormalizer.card_s ▸ card_dvd_of_le hsc
    have hcases : ∀ m ∈ (1920 : ℕ).divisors,
        128 ∣ m → ¬ 3 ∣ m → 5 ∣ m → m = 640 := by decide +kernel
    have hj : Nat.card J = 640 := hcases _ (Nat.mem_divisors.mpr ⟨hd,by decide⟩)
      h128 (he ▸ h3) (he ▸ h5)
    have hi := (J.subgroupOf Seed.l₁).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hc).toEquiv,hj,FirstParabolic.card_l₁] at hi
    let : Group.IsPerfect Seed.l₁ := FirstParabolic.CoverSquareOrbit.l₁_isPerfect
    let a : (⊤ : Subgroup Seed.l₁) ≃* Seed.l₁ := topEquiv
    let : Group.IsPerfect (⊤ : Subgroup Seed.l₁) :=
      Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
    have ht : J.subgroupOf Seed.l₁ = ⊤ := top_unique
      (le_of_isPerfect_of_index_le_four ⊤ _ (by omega))
    have hh := congrArg (fun U : Subgroup Seed.l₁ => Nat.card U) ht
    rw [Nat.card_congr (subgroupOfEquivOfLe hc).toEquiv,hj,card_top,FirstParabolic.card_l₁] at hh
    omega
  · have hd : Nat.card J ∣ 1152 := PairNormalizer.card_p₂ ▸ card_dvd_of_le hc
    have hh := (he ▸ h5).trans hd
    norm_num at hh

variable {G : Type*} [Group G] [Finite G]

/-- The actual J₂ action excludes a faithful quintic actor on a normal factor
when its join with the full Sylow has order dividing a power of two times five. -/
theorem no_five_actor (K E : Subgroup G) [K.Normal] (S : Sylow 2 G) {a : ℕ}
    (e : K ≃* Carrier) (hE : Nat.card E = 5)
    (hd : Disjoint E (centralizer (K : Set G)))
    (hc : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ 2^a * 5) : False := by
  have hzK : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center Carrier at hh
    rw [OrdinaryLocal.center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  apply no_odd_actor_of_sylow_order_bound K E S (by decide : Odd 5) hzK
    (outer_isTwoGroup.of_equiv (MulAut.outerCongr e).symm) _ hE hd hc
  intro P J hJ hPJ
  have h3 : ¬3 ∣ Nat.card J := Nat.prime_three.coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right (by decide)).of_dvd_right hJ)
  have hh := not_five_of_three_free (P.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (map_mono hPJ) (by rwa [card_map_of_injective e.injective])
  rwa [card_map_of_injective e.injective] at hh

end Sporadic.LeechRelated.J2.SylowOvergroups
