module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.NoncyclicOrder.PrimeSupport
public import Mathlib.RingTheory.IntegralDomain
public import Theory.GroupAction.FourAutomorphismOrbit
public import Theory.GroupTheory.CyclicFifteen
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Noncyclic odd complements have prime-cube order

The actual local inverter and the marked involution generate a four-group V
normalizing A. Any two-subgroup of N_G(A) containing V centralizes the mark
and therefore normalizes C_A(z) = ⟨x⟩. Its action on this prime-order group
has cyclic image of exponent two, and its kernel has order at most two by
the A₅ × C₂ common-centralizer calculation. Thus V is Sylow in N_G(A).

The three fixed orders lie in {1,3,5} and multiply to |A|. Noncyclicity forces
a repeated nontrivial prime among them. Remarking A at that prime gives
fusion of two distinct involutions inside N_G(A). Burnside fusion lifts
this to the normalizer of V, whose odd automizer is then transitive on the
three nonidentity elements. All fixed orders equal the marked prime p,
and consequently |A| = p³.

The only independent input retained is universal commutativity of the odd
complements, exactly as authorized by the parent assembly. No Sylow status,
recognition theorem, prescribed complement order, or exceptional normalizer
configuration is assumed.

Source: Bender, *Finite groups with large subgroups* (1974), proof of (4.1),
printed p.225 (PDF p.3), citing Janko (1966), proof of Lemma 3.1. This proves
the prime-cube restriction; exclusion of 125 remains with the parent.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

/-- Every two-subgroup normalizing the complement and containing the marked
involution has order at most four. Its action on the marked prime subgroup
has cyclic image of exponent two and kernel of order at most two. -/
public theorem OddCentralizerComplement.normalizing_two_card_le_four
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (B : Subgroup G) (hB : IsPGroup 2 B) (hBN : B ≤ normalizer (A : Set G))
    (hzB : h.z ∈ B) : Nat.card B ≤ 4 := by
  obtain ⟨S, hBS⟩ := hB.exists_le_sylow
  let _ := h.any_sylow_elementaryAbelian S
  have hsquare (b : B) : b ^ 2 = 1 := by
    exact Subtype.ext (congrArg (fun u : S => (u : G)) (h.any_sylow_square S ⟨b, hBS b.property⟩))
  have hBC : B ≤ centralizer ({h.z} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨b, hBS hb⟩ : S) ⟨h.z, hBS hzB⟩))
  let U := zpowers x
  have hBU : B ≤ normalizer (U : Set G) := by
    rw [show U = A ⊓ centralizer ({h.z} : Set G) from
      (a.inf_centralizer_eq_zpowers h p hp hxC hx).symm]
    exact (le_inf hBN (hBC.trans (centralizer ({h.z} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let f : B →* MulAut U := U.normalizerMonoidHom.comp (inclusion hBU)
  have hpprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  have hUc : Nat.card U = p := (Nat.card_zpowers x).trans hx
  let _ : Fact (Nat.card U).Prime := ⟨hUc.symm ▸ hpprime⟩
  let _ : IsCyclic (MulAut U) := isCyclic_of_injective
    (IsCyclic.mulAutMulEquiv U).toMonoidHom (IsCyclic.mulAutMulEquiv U).injective
  have hr : Nat.card f.range ≤ 2 := by
    apply Nat.le_of_dvd (by decide)
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨u, b, rfl⟩
    apply Subtype.ext
    change f b ^ 2 = 1
    rw [← map_pow, hsquare, map_one]
  let D := f.ker.map B.subtype
  have hDC : D ≤ centralizer ({h.z} : Set G) ⊓ centralizer ({x} : Set G) := by
    rintro u ⟨b, hb, rfl⟩
    refine ⟨hBC b.property, ?_⟩
    have he := congrArg (fun e : MulAut U => (e ⟨x, mem_zpowers x⟩ : G)) hb
    change (b : G) * x * (b : G)⁻¹ = x at he
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have hd8 : Nat.card f.ker ∣ 8 := by
    have hd := (card_dvd_of_le (show D ≤ (S : Subgroup G) from
      (map_subtype_le f.ker).trans hBS))
    rwa [card_map_of_injective Subtype.val_injective, h.any_sylow_card S] at hd
  have hd2p : Nat.card f.ker ∣ 2 * p := by
    have hd := card_dvd_of_le hDC
    rwa [card_map_of_injective Subtype.val_injective,
      h.odd_prime_common_centralizer_card p hp x hxC hx] at hd
  have hk : Nat.card f.ker ≤ 2 := by
    have hd := Nat.dvd_gcd hd8 hd2p
    have hgcd : Nat.gcd 8 (2 * p) = 2 := by rcases hp with rfl | rfl <;> decide
    rw [hgcd] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hm := f.ker.card_mul_index
  rw [index_ker] at hm
  nlinarith

/-- A normalizing four-group containing the marked involution is Sylow in
its actual normalizer. -/
public theorem OddCentralizerComplement.four_is_sylow_in_normalizer
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (V : Subgroup G) (hV : Nat.card V = 4)
    (hVN : V ≤ normalizer (A : Set G)) (hzV : h.z ∈ V) :
    ∃ P : Sylow 2 (normalizer (A : Set G)),
      (P : Subgroup (normalizer (A : Set G))) =
        V.subgroupOf (normalizer (A : Set G)) := by
  let N := normalizer (A : Set G)
  let W := V.subgroupOf N
  have hW : Nat.card W = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv).trans hV
  obtain ⟨P, hWP⟩ := (IsPGroup.of_card (p := 2) (n := 2) hW).exists_le_sylow
  have hPc : Nat.card P ≤ 4 := by
    let B := (P : Subgroup N).map N.subtype
    have hb := a.normalizing_two_card_le_four p hp hxC hx B
      (P.isPGroup'.map N.subtype) (map_subtype_le _) ?_
    · rwa [card_map_of_injective Subtype.val_injective] at hb
    · exact mem_map.mpr ⟨⟨h.z, hVN hzV⟩, hWP hzV, rfl⟩
  exact ⟨P, (eq_of_le_of_card_ge hWP (by rw [hW]; exact hPc)).symm⟩

/-- The local inverter constructs a genuine Sylow four-group in N(A). -/
public theorem OddCentralizerComplement.exists_normalizing_sylow_four
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    ∃ V : Subgroup G, IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
      h.z ∈ V ∧ V ≤ normalizer (A : Set G) ∧
      ∃ P : Sylow 2 (normalizer (A : Set G)),
        (P : Subgroup (normalizer (A : Set G))) =
          V.subgroupOf (normalizer (A : Set G)) := by
  obtain ⟨t, htC, ht, htz, hti⟩ := h.exists_local_inverter p hp x hxC hx
  have hzt : h.z ≠ t := fun he => htz (he ▸ mem_zpowers h.z)
  let V := closure ({h.z, t} : Set G)
  let _ : IsKleinFour V := isKleinFour_closure_pair_of_orderOf h.z t h.involution ht
    hzt (mem_centralizer_singleton_iff.mp htC).symm
  have hVe : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  have hVc : Nat.card V = 4 := IsKleinFour.card_four
  have hzV : h.z ∈ V := subset_closure (by simp)
  have hVN : V ≤ normalizer (A : Set G) := by
    rw [closure_le]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact a.z_mem_normalizer
    · exact a.inverter_mem_normalizer _ hti
  exact ⟨V, hVe, hVc, hzV, hVN,
    a.four_is_sylow_in_normalizer p hp hxC hx V hVc hVN hzV⟩

end CFSG.Quasithin.Janko1CentralizerData

open Subgroup
open scoped IsMulCommutative

private theorem odd_abelian_sylow_automizer
    {H : Type*} [Group H] [Finite H] (P : Sylow 2 H) [IsMulCommutative P] :
    Odd (Nat.card (P : Subgroup H).normalizerMonoidHom.range) := by
  let W := (P : Subgroup H)
  let M := normalizer (W : Set H)
  let f := W.normalizerMonoidHom
  have hle : W.subgroupOf M ≤ f.ker := by
    rw [normalizerMonoidHom_ker]
    intro u hu
    exact le_centralizer W hu
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd, ← index_ker f]
  intro hd
  exact (P.subtype W.le_normalizer).not_dvd_index (hd.trans (index_dvd_of_le hle))

private theorem four_sylow_fusion
    {H : Type*} [Group H] [Finite H] (P : Sylow 2 H)
    [IsElementaryAbelian 2 P] (hP : Nat.card P = 4)
    (s t : H) (hs : s ∈ P) (ht : t ∈ P) (hst : s ≠ t)
    (g : H) (hg : g * s * g⁻¹ = t) :
    ∀ u v : P, u ≠ 1 → v ≠ 1 →
      ∃ n ∈ normalizer (P : Set H), n * (u : H) * n⁻¹ = v := by
  let W := (P : Subgroup H)
  let f := W.normalizerMonoidHom
  obtain ⟨n, hn, he⟩ := P.conj_eq_normalizer_conj_of_mem s g⁻¹ hs
    (by simpa only [inv_inv, hg] using ht)
  have hnmove : f ⟨n, hn⟩ ≠ 1 := by
    intro hn1
    have hnfix := congrArg (fun e : MulAut W => (e ⟨s, hs⟩ : H)) hn1
    change n * s * n⁻¹ = s at hnfix
    have hncomm : n * s = s * n := mul_inv_eq_iff_eq_mul.mp hnfix
    have hnf : n⁻¹ * s * n = s := by
      rw [mul_assoc, ← hncomm, inv_mul_cancel_left]
    have he' : t = s := by
      simpa only [inv_inv, hg, hnf] using he
    exact hst he'.symm
  have hc : 1 < Nat.card f.range := by
    apply Finite.one_lt_card_iff_nontrivial.mpr
    exact ⟨⟨⟨f ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩⟩, 1,
      fun he => hnmove (congrArg Subtype.val he)⟩⟩
  have ho : Odd (Nat.card f.range) := odd_abelian_sylow_automizer P
  have hc2 : 2 < Nat.card f.range := by
    obtain ⟨k, hk⟩ := ho
    omega
  intro u v hu hv
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.nonidentity_mem_orbit_of_four_automorphism_subgroup hP f.range hc2 u hu v hv)
  obtain ⟨n, hn⟩ := b.property
  refine ⟨n, n.property, ?_⟩
  have hh : (b : MulAut W) u = v := hb
  rw [← hn] at hh
  exact congrArg Subtype.val hh

namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Conjugation inside N(A) preserves the literal involution fixed order. -/
private theorem fixed_card_conjugate (A : Subgroup G) (g : G)
    (hg : g ∈ normalizer (A : Set G)) (s : G) :
    Nat.card (A ⊓ centralizer ({s} : Set G) : Subgroup G) =
      Nat.card (A ⊓ centralizer ({g * s * g⁻¹} : Set G) : Subgroup G) := by
  let e := MulAut.conj g
  apply Nat.card_congr (e.toEquiv.subtypeEquiv ?_)
  intro y
  change y ∈ A ⊓ centralizer ({s} : Set G) ↔
    e y ∈ A ⊓ centralizer ({e s} : Set G)
  simp only [mem_inf, mem_centralizer_singleton_iff, ← map_mul, e.injective.eq_iff]
  exact and_congr (mem_normalizer_iff.mp hg y) Iff.rfl

/-- Equal nontrivial prime fixed orders fuse inside the actual complement normalizer. -/
public theorem OddCentralizerComplement.fuse_equal_prime_fixed
    [IsSimpleGroup G] {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (ha : IsMulCommutative A)
    (allComm : ∀ (k : Janko1CentralizerData G) (q : ℕ), (q = 3 ∨ q = 5) →
      ∀ y : G, y ∈ centralizer ({k.z} : Set G) → orderOf y = q →
        ∀ B : Subgroup G, OddCentralizerComplement k y B → IsMulCommutative B)
    (s t : G) (hs : orderOf s = 2) (ht : orderOf t = 2)
    (q : ℕ) (hq : q = 3 ∨ q = 5)
    (hsc : Nat.card (A ⊓ centralizer ({s} : Set G) : Subgroup G) = q)
    (htc : Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) = q) :
    ∃ g ∈ normalizer (A : Set G), g * t * g⁻¹ = s := by
  have hprime : q.Prime := by rcases hq with rfl | rfl <;> decide
  let _ : Fact q.Prime := ⟨hprime⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(A ⊓ centralizer ({s} : Set G))) q (hsc ▸ dvd_refl q)
  have hyG : orderOf (y : G) = q := (Subgroup.orderOf_mk _ _).symm.trans hy
  obtain ⟨k, hk, b⟩ := a.remark_at_fixed_prime ha allComm s hs q hq y
    y.property.1 y.property.2 hyG
  obtain ⟨g, hg, he⟩ := b.exists_normalizer_conj_of_fixed_card ha q hq
    (hk.symm ▸ y.property.2) hyG t ht htc
  exact ⟨g, hg, he.trans hk⟩

end CFSG.Quasithin.Janko1CentralizerData

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_orders_equal_of_fusion
    (A V : Subgroup G) [IsElementaryAbelian 2 V] (hV : Nat.card V = 4)
    (hVN : V ≤ normalizer (A : Set G))
    (P : Sylow 2 (normalizer (A : Set G)))
    (hP : (P : Subgroup (normalizer (A : Set G))) =
      V.subgroupOf (normalizer (A : Set G)))
    (s t : G) (hsV : s ∈ V) (htV : t ∈ V) (hst : s ≠ t)
    (g : G) (hgN : g ∈ normalizer (A : Set G)) (hg : g * s * g⁻¹ = t) :
    ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      Nat.card (A ⊓ centralizer ({u} : Set G) : Subgroup G) =
        Nat.card (A ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  let N := normalizer (A : Set G)
  let _ : IsElementaryAbelian 2 P := by
    rw [hP]
    exact IsElementaryAbelian.subgroupOf hVN
  have hPc : Nat.card P = 4 := by
    rw [hP, Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv, hV]
  have memP (v : G) (hv : v ∈ V) : (⟨v, hVN hv⟩ : N) ∈ P := by
    change (⟨v, hVN hv⟩ : N) ∈ (P : Subgroup N)
    rw [hP]
    exact hv
  have hmove := four_sylow_fusion P hPc
    ⟨s, hVN hsV⟩ ⟨t, hVN htV⟩ (memP s hsV) (memP t htV)
    (fun he => hst (congrArg Subtype.val he)) ⟨g, hgN⟩ (Subtype.ext hg)
  intro u hu hune v hv hvne
  let uP : P := ⟨⟨u, hVN hu⟩, memP u hu⟩
  let vP : P := ⟨⟨v, hVN hv⟩, memP v hv⟩
  obtain ⟨n, _, hn⟩ := hmove uP vP
    (fun he => hune (congrArg (fun b : P => ((b : N) : G)) he))
    (fun he => hvne (congrArg (fun b : P => ((b : N) : G)) he))
  have hnG : (n : G) * u * (n : G)⁻¹ = v := congrArg (fun b : N => (b : G)) hn
  simpa only [hnG] using fixed_card_conjugate A n n.property u

/-- Under the universal commutativity input, a noncyclic odd complement has
exactly the cube of its marked prime as its order. -/
public theorem OddCentralizerComplement.card_eq_prime_cube_of_noncyclic
    [IsSimpleGroup G] {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A)
    (allComm : ∀ (k : Janko1CentralizerData G) (q : ℕ), (q = 3 ∨ q = 5) →
      ∀ y : G, y ∈ centralizer ({k.z} : Set G) → orderOf y = q →
        ∀ B : Subgroup G, OddCentralizerComplement k y B → IsMulCommutative B)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hncyc : ¬ IsCyclic A) : Nat.card A = p ^ 3 := by
  have ha := allComm h p hp x hxC hx A a
  obtain ⟨t, htC, ht, htz, hti⟩ := h.exists_local_inverter p hp x hxC hx
  have hzt : h.z ≠ t := fun he => htz (he ▸ mem_zpowers h.z)
  have htne : t ≠ 1 := by intro he; simp [he] at ht
  have hprods : h.z * t ≠ h.z ∧ h.z * t ≠ t ∧ h.z * t ≠ 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
      mul_notMem_of_orderOf_eq_two h.involution ht hzt
  have hprodne := hprods.2.2
  have hprodt := hprods.2.1.symm
  have hzprod := hprods.1.symm
  let V := closure ({h.z, t} : Set G)
  let _ : IsKleinFour V := isKleinFour_closure_pair_of_orderOf h.z t h.involution ht
    hzt (mem_centralizer_singleton_iff.mp htC).symm
  let _ : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  have hVc : Nat.card V = 4 := IsKleinFour.card_four
  have hzV : h.z ∈ V := subset_closure (by simp)
  have htV : t ∈ V := subset_closure (by simp)
  have hprodV : h.z * t ∈ V := V.mul_mem hzV htV
  have hprodorder : orderOf (h.z * t) = 2 := by
    apply orderOf_eq_prime _ hprodne
    exact congrArg (fun b : V => (b : G))
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) ⟨h.z * t, hprodV⟩)
  have hVN : V ≤ normalizer (A : Set G) := by
    rw [closure_le]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact a.z_mem_normalizer
    · exact a.inverter_mem_normalizer _ hti
  obtain ⟨P, hP⟩ := a.four_is_sylow_in_normalizer p hp hxC hx V hVc hVN hzV
  let q := Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G)
  let r := Nat.card (A ⊓ centralizer ({h.z * t} : Set G) : Subgroup G)
  have hpc : Nat.card (A ⊓ centralizer ({h.z} : Set G) : Subgroup G) = p := by
    rw [a.inf_centralizer_eq_zpowers h p hp hxC hx, Nat.card_zpowers, hx]
  obtain ⟨hq, hr⟩ := a.four_fixed_orders t htC ht htz
  change q = 1 ∨ q = 3 ∨ q = 5 at hq
  change r = 1 ∨ r = 3 ∨ r = 5 at hr
  have hcard : Nat.card A = p * q * r := a.four_fixed_card p hp hxC hx t htC ht htz hti
  have hn3 : Nat.card A ≠ 3 := fun he => hncyc (isCyclic_of_prime_card (p := 3) he)
  have hn5 : Nat.card A ≠ 5 := by
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact fun he => hncyc (isCyclic_of_prime_card (p := 5) he)
  have hn15 : Nat.card A ≠ 15 := fun he => hncyc (isCyclic_of_card_eq_fifteen he)
  have hrepeat : p = q ∨ p = r ∨ (q = r ∧ (q = 3 ∨ q = 5)) := by
    rcases hp with rfl | rfl <;>
      rcases hq with hq | hq | hq <;> rcases hr with hr | hr | hr <;>
      simp_all
  have hfuse : ∃ s u : G, s ∈ V ∧ u ∈ V ∧ s ≠ u ∧
      ∃ g ∈ normalizer (A : Set G), g * s * g⁻¹ = u := by
    rcases hrepeat with hpq | hpr | ⟨hqr, hqprime⟩
    · obtain ⟨g, hg, he⟩ := a.fuse_equal_prime_fixed ha allComm h.z t h.involution ht
        p hp hpc hpq.symm
      exact ⟨t, h.z, htV, hzV, hzt.symm, g, hg, he⟩
    · obtain ⟨g, hg, he⟩ := a.fuse_equal_prime_fixed ha allComm h.z (h.z * t)
        h.involution hprodorder p hp hpc hpr.symm
      exact ⟨h.z * t, h.z, hprodV, hzV, hzprod.symm, g, hg, he⟩
    · obtain ⟨g, hg, he⟩ := a.fuse_equal_prime_fixed ha allComm t (h.z * t)
        ht hprodorder q hqprime rfl hqr.symm
      exact ⟨h.z * t, t, hprodV, htV, hprodt.symm, g, hg, he⟩
  obtain ⟨s, u, hsV, huV, hsu, g, hgN, hg⟩ := hfuse
  have heq := fixed_orders_equal_of_fusion A V hVc hVN P hP s u hsV huV hsu g hgN hg
  have hqp : q = p := (heq t htV htne h.z hzV h.z_ne_one).trans hpc
  have hrp : r = p := (heq (h.z * t) hprodV hprodne h.z hzV h.z_ne_one).trans hpc
  rw [hcard, hqp, hrp]
  ring

/-- The exact order alternatives consumed by the noncyclic-order assembly.
The parent independently excludes 125. -/
public theorem OddCentralizerComplement.card_eq_twenty_seven_or_one_twenty_five_of_noncyclic
    [IsSimpleGroup G] {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A)
    (allComm : ∀ (k : Janko1CentralizerData G) (q : ℕ), (q = 3 ∨ q = 5) →
      ∀ y : G, y ∈ centralizer ({k.z} : Set G) → orderOf y = q →
        ∀ B : Subgroup G, OddCentralizerComplement k y B → IsMulCommutative B)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hncyc : ¬ IsCyclic A) : Nat.card A = 27 ∨ Nat.card A = 125 := by
  have hc := a.card_eq_prime_cube_of_noncyclic allComm p hp hxC hx hncyc
  rcases hp with rfl | rfl
  · exact Or.inl hc
  · exact Or.inr hc

end CFSG.Quasithin.Janko1CentralizerData
