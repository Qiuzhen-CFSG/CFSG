module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.LocalCentralizers
public import Theory.GroupTheory.FocalTransfer
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupAction.ThreeOnElementaryEight
public import Theory.GroupTheory.ConjugacyClassSize

/-!
# Involution fusion from the J₁ local hypotheses

The self-centralizing elementary Sylow subgroup has order eight. Its
normalizer induces an odd subgroup of its automorphism group of order 168.
Burnside fusion and the focal subgroup theorem make the displacement subgroup
the whole Sylow subgroup, since the ambient simple group is perfect. Actions
of order one or three cannot do this in dimension three. The automizer
therefore contains a subgroup of order seven, transitive on the nonidentity
Sylow elements. Sylow conjugacy proves that all ambient involutions fuse.

This supplies hypothesis (i), which Bender assumes at the start of §4 of
*Finite groups with large subgroups*, Illinois J. Math. 18 (1974), pp.225–228,
from the original hypotheses of Aschbacher–Smith I.4.9, printed p.418.
The final class-size identity connects fusion to Bender's involution count;
the count itself is a separate source argument.
-/

open Subgroup MulAction
open scoped IsMulCommutative

namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- The normalizer action on the Sylow subgroup has odd order. -/
public theorem sylow_automizer_odd : Odd (Nat.card (h.sylow : Subgroup G).normalizerMonoidHom.range) := by
  let S := (h.sylow : Subgroup G)
  let N := normalizer (S : Set G)
  let f := S.normalizerMonoidHom
  have hi : f.ker.index = Nat.card f.range := index_ker f
  have hk : f.ker = S.subgroupOf N := by
    have hc : centralizer (S : Set G) = S := h.sylow_centralizer_eq
    rw [normalizerMonoidHom_ker, hc]
  have hodd := (h.sylow.subtype S.le_normalizer).not_dvd_index
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd, ← hi, hk]
  exact hodd

include h in
/-- The source simple group is perfect: an abelian group cannot have this proper centralizer. -/
public theorem commutator_eq_top [IsSimpleGroup G] : _root_.commutator G = ⊤ := by
  rcases (inferInstance : (_root_.commutator G).Normal).eq_bot_or_eq_top with hb | ht
  · have hc := (commutator_eq_bot_iff_center_eq_top G).mp hb
    exact (h.centralizer_ne_top (eq_top_iff.mpr (by
      intro x _
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hc ▸ mem_top h.z) x)))).elim
  · exact ht

private theorem automizer_full_commutator [IsSimpleGroup G]
    (hperfect : _root_.commutator G = ⊤) :
    commutatorAction (h.sylow : Subgroup G).normalizerMonoidHom.range h.sylow = ⊤ := by
  let S := (h.sylow : Subgroup G)
  let N := normalizer (S : Set G)
  let f := S.normalizerMonoidHom
  let A := f.range
  let D := commutatorAction A S
  let _ := h.sylow_elementaryAbelian
  have hfocal : S.focalSubgroup = S := by
    rw [← commutator_inf_eq_focalSubgroup h.sylow, hperfect, top_inf_eq]
  have hle : S.focalSubgroup ≤ D.map S.subtype := by
    rw [focalSubgroup_def, closure_le]
    rintro w ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    obtain ⟨n, hn, heq⟩ := h.sylow.conj_eq_normalizer_conj_of_mem x g⁻¹ hx
      (by rw [inv_inv]; exact hy)
    let a : A := f.rangeRestrict ⟨n⁻¹, N.inv_mem hn⟩
    let s : S := ⟨x, hx⟩
    have hd : s⁻¹ * (a • s) ∈ D := by
      change s⁻¹ * (a • s) ∈ commutatorAction A S
      rw [commutatorAction_eq_closure]
      exact subset_closure ⟨a, s, rfl⟩
    refine ⟨s⁻¹ * (a • s), hd, ?_⟩
    change x⁻¹ * (n⁻¹ * x * (n⁻¹)⁻¹) = x⁻¹ * (g * x * g⁻¹)
    simpa only [inv_inv] using congrArg (x⁻¹ * ·) heq.symm
  change D = ⊤
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨d, hd, heq⟩ := (hfocal ▸ hle) x.property
  exact (S.subtype_injective heq) ▸ hd

private theorem automizer_seven_dvd [IsSimpleGroup G]
    (hfull : commutatorAction (h.sylow : Subgroup G).normalizerMonoidHom.range h.sylow = ⊤)
    (hodd : Odd (Nat.card (h.sylow : Subgroup G).normalizerMonoidHom.range)) :
    7 ∣ Nat.card (h.sylow : Subgroup G).normalizerMonoidHom.range := by
  let _ := h.sylow_elementaryAbelian
  let A := (h.sylow : Subgroup G).normalizerMonoidHom.range
  have hd : Nat.card A ∣ 168 :=
    (card_mulAut_of_elementary_eight h.sylow h.sylow_card) ▸ A.card_subgroup_dvd_card
  have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hs : (168 : ℕ).divisors =
      {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by decide
  rw [hs] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hn2 := hodd.not_two_dvd_nat
  change ¬ 2 ∣ Nat.card A at hn2
  have hc : Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 7 ∨ Nat.card A = 21 := by omega
  have hD : Nat.card (commutatorAction A h.sylow) = 8 := by
    rw [hfull, card_top, h.sylow_card]
  rcases hc with hc | hc | hc | hc
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hc).1
    have hb : commutatorAction A h.sylow = ⊥ := by
      apply bot_unique
      rw [commutatorAction_eq_closure, closure_le]
      rintro x ⟨a, s, rfl⟩
      rw [Subsingleton.elim a 1, one_smul, inv_mul_cancel]
      exact one_mem _
    rw [hb, card_bot] at hD
    omega
  · have hn : commutatorAction A h.sylow ≠ ⊥ := by
      intro hb
      rw [hb, card_bot] at hD
      omega
    have he := (card_three_action_on_eight_fixed_commutator_card hc h.sylow_card hn).2
    omega
  · exact hc ▸ dvd_refl _
  · rw [hc]; decide

private theorem seven_transitive {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 8)
    (B : Subgroup (MulAut V)) (hB : Nat.card B = 7) (x y : V)
    (hx : x ≠ 1) (hy : y ≠ 1) : ∃ b : B, b • x = y := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let F := FixedPoints.subgroup B V
  have hp : IsPGroup 7 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hm := hp.card_modEq_card_fixedPoints V
  change Nat.card V % 7 = Nat.card F % 7 at hm
  rw [hV] at hm
  have hle : Nat.card F ≤ 8 := hV ▸ F.card_le_card_group
  have hFne : Nat.card F ≠ 8 := by
    intro h8
    have htop : F = ⊤ := F.eq_top_of_card_eq (h8.trans hV.symm)
    have hbot : B = ⊥ := by
      apply eq_bot_iff.mpr
      intro b hb
      apply MulEquiv.ext
      intro v
      have hv : v ∈ F := htop ▸ mem_top v
      exact hv ⟨b, hb⟩
    rw [hbot, card_bot] at hB
    omega
  have hF : F = ⊥ := card_eq_one.mp (by omega)
  have hOn1 : Nat.card (orbit B x) ≠ 1 := by
    let _ := Fintype.ofFinite (orbit B x)
    intro ho
    have hfix : x ∈ F := mem_fixedPoints_iff_card_orbit_eq_one.mpr
      (by rwa [← Nat.card_eq_fintype_card])
    rw [hF] at hfix
    exact hx hfix
  have hOdvd : Nat.card (orbit B x) ∣ 7 := by
    have he := Nat.card_congr (orbitProdStabilizerEquivGroup B x)
    rw [Nat.card_prod, hB] at he
    exact ⟨_, he.symm⟩
  have hO : Nat.card (orbit B x) = 7 := ((Nat.dvd_prime (by decide)).mp hOdvd).resolve_left hOn1
  have hsub : orbit B x ⊆ ({1} : Set V)ᶜ := by
    rintro v ⟨b, rfl⟩
    exact fun he => hx ((b : MulAut V).injective (he.trans (map_one _).symm))
  have heq : orbit B x = ({1} : Set V)ᶜ :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_compl, Set.ncard_singleton, hV]; exact hO.ge)
  exact mem_orbit_iff.mp (heq.symm ▸ hy)

/-- The Sylow automizer contains a subgroup of order seven. -/
public theorem sylow_automizer_seven_dvd [IsSimpleGroup G] :
    7 ∣ Nat.card (h.sylow : Subgroup G).normalizerMonoidHom.range :=
  h.automizer_seven_dvd (h.automizer_full_commutator h.commutator_eq_top)
    h.sylow_automizer_odd

/-- The Sylow normalizer is transitive on its seven nonidentity elements. -/
public theorem sylow_normalizer_transitive [IsSimpleGroup G]
    (x y : h.sylow) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ n ∈ normalizer (h.sylow : Set G), n * (x : G) * n⁻¹ = y := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let f := (h.sylow : Subgroup G).normalizerMonoidHom
  let A := f.range
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 7 h.sylow_automizer_seven_dvd
  let B := zpowers (a : MulAut h.sylow)
  have hB : Nat.card B = 7 := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective A.subtype A.subtype_injective a).trans ha
  obtain ⟨b, hb⟩ := seven_transitive h.sylow_card B hB x y hx hy
  have hbA : (b : MulAut h.sylow) ∈ A := (zpowers_le.mpr a.property) b.property
  obtain ⟨n, hn⟩ := hbA
  refine ⟨n, n.property, ?_⟩
  have heq : f n x = y := by rw [hn]; exact hb
  exact congrArg Subtype.val heq

/-- All involutions are conjugate to the distinguished involution, from the
original finite simple group hypotheses. -/
public theorem involutions_conjugate [IsSimpleGroup G] (x : G) (hx : orderOf x = 2) :
    ∃ g : G, g * x * g⁻¹ = h.z := by
  obtain ⟨S, hxS, _⟩ := h.involution_is_two_central x hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S h.sylow
  have hx' : g * x * g⁻¹ ∈ (h.sylow : Subgroup G) := by
    rw [← hg]
    exact ⟨x, hxS, rfl⟩
  have hx1 : x ≠ 1 := by intro he; simp [he] at hx
  have hxne : (⟨g * x * g⁻¹, hx'⟩ : h.sylow) ≠ 1 := by
    intro he
    have he' : (MulAut.conj g) x = 1 := congrArg Subtype.val he
    exact hx1 ((MulAut.conj g).injective (he'.trans (map_one _).symm))
  have hz : (⟨h.z, h.z_mem⟩ : h.sylow) ≠ 1 :=
    fun he => h.z_ne_one (congrArg Subtype.val he)
  obtain ⟨n, _, hn⟩ := h.sylow_normalizer_transitive ⟨g * x * g⁻¹, hx'⟩
    ⟨h.z, h.z_mem⟩ hxne hz
  exact ⟨n * g, by simpa only [mul_inv_rev, mul_assoc] using hn⟩

include h in
/-- Every involution centralizer has the source centralizer order. -/
public theorem involution_centralizer_card [IsSimpleGroup G] (x : G) (hx : orderOf x = 2) :
    Nat.card (centralizer ({x} : Set G)) = 120 := by
  obtain ⟨g, hg⟩ := h.involutions_conjugate x hx
  let e := MulAut.conj g
  have he : e x = h.z := hg
  let ec : centralizer ({x} : Set G) ≃ centralizer ({h.z} : Set G) :=
    e.toEquiv.subtypeEquiv (fun y => by
      rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← he]
      change y * x = x * y ↔ e y * e x = e x * e y
      rw [← map_mul, ← map_mul, e.injective.eq_iff])
  exact (Nat.card_congr ec).trans h.centralizer_card

/-- Fusion identifies the complete involution set with one actual conjugacy class. -/
public theorem involution_count_eq_index [IsSimpleGroup G] :
    Nat.card {x : G // orderOf x = 2} = (centralizer ({h.z} : Set G)).index := by
  have he : (ConjClasses.mk h.z).carrier = {x : G | orderOf x = 2} := by
    ext x
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    constructor
    · intro hx
      obtain ⟨g, hg⟩ := isConj_iff.mp hx
      have hc := (MulAut.conj g).orderOf_eq x
      rw [show (MulAut.conj g) x = h.z from hg, h.involution] at hc
      exact hc.symm
    · intro hx
      exact isConj_iff.mpr (h.involutions_conjugate x hx)
  change Nat.card ({x : G | orderOf x = 2} : Set G) = _
  rw [← he]
  exact ConjClasses.nat_card_carrier_eq_index_centralizer h.z

include h in
/-- The group order is 120 times the number of involutions. -/
public theorem card_eq_involution_count_mul [IsSimpleGroup G] :
    Nat.card G = Nat.card {x : G // orderOf x = 2} * 120 := by
  rw [h.involution_count_eq_index, ← h.centralizer_card]
  exact (centralizer ({h.z} : Set G)).index_mul_card.symm

end CFSG.Quasithin.Janko1CentralizerData
