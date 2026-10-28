module
public import Theory.GroupTheory.OddCentralInvolutionLifting.Centralizers
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.GroupTheory.CentralizerSmallKernelTransport
/-!
# The literal cubic-centralizer quotient and its involutions

Odd central kernels lift involutions uniquely and preserve their centralizers.
If an involution centralizer has order twelve and all its squares lie in a
central cubic kernel, its image is elementary abelian of order four.
Involution fusion also passes through the same quotient map.

The original source application is Aschbacher–Smith 5.2.15, printed
pp.654–655 (`refs/quasithin.pdf`). The quotient here is literally
C_G(c)/⟨c⟩; no abstract replacement of the cyclic kernel is made.
-/
public noncomputable section
open Subgroup
namespace Theory.GroupTheory.QuasithinM23
variable {X Q : Type*} [Group X] [Group Q] [Finite X]

omit [Finite X] in
theorem odd_quotient_involutions_isConj (q : X →* Q) (hq : Function.Surjective q)
    (hodd : Odd (Nat.card q.ker))
    (hfus : ∀ s t : X, orderOf s = 2 → orderOf t = 2 → IsConj s t)
    (a b : Q) (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨s,hs,hs2⟩ := OddCentralLifting.exists_involution_lift q hodd hq a (ha ▸ pow_orderOf_eq_one a)
  obtain ⟨t,ht,ht2⟩ := OddCentralLifting.exists_involution_lift q hodd hq b (hb ▸ pow_orderOf_eq_one b)
  have hs1 : s ≠ 1 := by
    intro he
    rw [←hs,he,map_one,orderOf_one] at ha
    omega
  have ht1 : t ≠ 1 := by
    intro he
    rw [←ht,he,map_one,orderOf_one] at hb
    omega
  simpa only [hs,ht] using q.map_isConj (hfus s t
    (orderOf_eq_prime hs2 hs1) (orderOf_eq_prime ht2 ht1))

/-- The order-twelve commuting-pair centralizer becomes an elementary four-group
through the literal central cubic quotient. -/
theorem central_cubic_quotient_centralizer
    (q : X →* Q) (hq : Function.Surjective q) (hker : Nat.card q.ker = 3)
    (hcentral : q.ker ≤ center X)
    (t : X) (ht : orderOf t = 2)
    (hcard : Nat.card (centralizer ({t} : Set X)) = 12)
    (hsquare : ∀ x ∈ centralizer ({t} : Set X), x^2 ∈ q.ker) :
    orderOf (q t) = 2 ∧ Nat.card (centralizer ({q t} : Set Q)) = 4 ∧
      IsElementaryAbelian 2 (centralizer ({q t} : Set Q)) := by
  let : Finite Q := Finite.of_surjective q hq
  have hodd : Odd (Nat.card q.ker) := by rw [hker]; decide
  have ht2 : t^2=1 := ht ▸ pow_orderOf_eq_one t
  have hqt : q t ≠ 1 := by
    intro hz
    have ht1 := OddCentralLifting.kernel_involution_eq_one q hodd hz ht2
    simp [ht1] at ht
  have himage : (centralizer ({t} : Set X)).map q = centralizer ({q t} : Set Q) := by
    rw [OddCentralLifting.centralizer_eq_comap q hodd hcentral ht2,
      map_comap_eq_self_of_surjective hq]
  have hle : q.ker ≤ centralizer ({t} : Set X) :=
    hcentral.trans (center_le_centralizer _)
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (centralizer ({t} : Set X)) q
  rw [inf_eq_right.mpr hle,hker,himage,hcard] at hh
  have hpow (x : centralizer ({q t} : Set Q)) : x^2=1 := by
    obtain ⟨a,ha,he⟩ := (show (x : Q) ∈ (centralizer ({t} : Set X)).map q from himage.symm ▸ x.property)
    apply Subtype.ext
    change (x : Q)^2=1
    rw [←he,←map_pow]
    exact hsquare a ha
  refine ⟨orderOf_eq_prime (by rw [←map_pow,ht2,map_one]) hqt,by omega,?_⟩
  exact
    { toIsMulCommutative := by
        exact IsMulCommutative.of_comm (fun a b =>
          (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq)
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }

/-- The original cyclic subgroup inside its element centralizer. -/
abbrev centralizerCyclic {G : Type*} [Group G] (c : G) :
    Subgroup (centralizer ({c} : Set G)) :=
  zpowers ⟨c,mem_centralizer_singleton_iff.mpr rfl⟩

theorem centralizerCyclic_le_center {G : Type*} [Group G] (c : G) :
    centralizerCyclic c ≤ center (centralizer ({c} : Set G)) := by
  apply zpowers_le.mpr
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)

instance centralizerCyclic_normal {G : Type*} [Group G] (c : G) : (centralizerCyclic c).Normal :=
  ⟨fun x hx g => by simpa [mem_center_iff.mp (centralizerCyclic_le_center c hx) g] using hx⟩

/-- The literal quotient C_G(c)/⟨c⟩, used in source 5.2.15. -/
abbrev cubicCentralizerQuotient {G : Type*} [Group G] (c : G) :=
  centralizer ({c} : Set G) ⧸ centralizerCyclic c

/-- Swap the two centralizer restrictions, keeping every ambient element. -/
def commutingCentralizerEquiv {G : Type*} [Group G]
    (c t : G) (h : Commute c t) :
    centralizer ({(⟨t,mem_centralizer_singleton_iff.mpr h.symm.eq⟩ : centralizer ({c} : Set G))} :
      Set (centralizer ({c} : Set G))) ≃*
    centralizer ({(⟨c,mem_centralizer_singleton_iff.mpr h.eq⟩ : centralizer ({t} : Set G))} :
      Set (centralizer ({t} : Set G))) where
  toFun x := ⟨⟨x.val.val,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
  invFun x := ⟨⟨x.val.val,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The restriction swap preserves the original ambient element. -/
theorem commutingCentralizerEquiv_coe {G : Type*} [Group G]
    (c t : G) (h : Commute c t)
    (x : centralizer ({(⟨t,mem_centralizer_singleton_iff.mpr h.symm.eq⟩ : centralizer ({c} : Set G))} :
      Set (centralizer ({c} : Set G)))) :
    ((commutingCentralizerEquiv c t h x).val : G) = (x.val : G) := by rfl
end Theory.GroupTheory.QuasithinM23
