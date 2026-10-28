module

public import Theory.SpecificGroups.ProjectiveLinear.EvenOddTori.Coverage
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.Tactic

/-!
# Odd subgroups of PSL₂ in characteristic two

For a finite field of order q = 2^n, n ≥ 2, every odd-order subgroup of
PSL₂(F) lies in a cyclic torus of order q−1 or q+1. A normalizing involution
inverts every nontrivial subgroup of such a torus. If the normalizer of an
odd subgroup H is contained in H⟨t⟩, the torus is exhausted by H, and the
relative centralizer index [H : C_H(t)] equals its torus order.

The proof uses the actual matrix tori and element partition of Huppert
II.8.3–5. Inside an odd subgroup, a cyclic subgroup's normalizer lies in its
torus. Sylow centers then show that every Sylow subgroup is cyclic. The
finite Z-group commutator theorem forces the entire odd subgroup to be
cyclic, completing the passage from element coverage to subgroup coverage.
The final saturation and index calculations use `OddInvolutionNormalizer`.

Sources: GLS, Volume 4, Chapter 4, Lemma 3.7 (odd-order clause), and
Chapter 2, Lemma 17.5. This module proves the concrete linear model input;
the Section 17 numerical choice between q−1 and q+1 remains with its consumer.
-/

open Subgroup
open scoped IsMulCommutative
namespace BenderSuzuki.MatrixGroups.EvenOddTori

-- The center of each Sylow gives a cyclic subgroup normalized by that Sylow.
private theorem cyclic_of_cyclic_normalizers {G : Type*} [Group G] [Finite G]
    (h : ∀ C : Subgroup G, C ≠ ⊥ → IsCyclic C → IsCyclic (normalizer (C : Set G))) :
    IsCyclic G := by
  classical
  have hz : IsZGroup G := by
    constructor
    intro p hp P
    let : Fact p.Prime := ⟨hp⟩
    rcases subsingleton_or_nontrivial P with hP | hP
    · infer_instance
    · have := P.isPGroup'.center_nontrivial
      obtain ⟨z, hz⟩ := exists_ne (1 : center P)
      have hzG : ((z : P) : G) ≠ 1 := fun hh => hz (Subtype.ext (Subtype.ext hh))
      have hC : zpowers ((z : P) : G) ≠ ⊥ := by simpa using hzG
      have hn := h _ hC inferInstance
      have hPN : (P : Subgroup G) ≤ normalizer (zpowers ((z : P) : G)) := by
        apply (le_centralizer_iff.mpr ?_).trans (centralizer_le_normalizer _)
        apply zpowers_le.mpr
        intro x hx
        have hc := (mem_center_iff.mp z.property) (⟨x, hx⟩ : P)
        exact congrArg Subtype.val hc
      exact Subgroup.isCyclic_of_le hPN
  have hc := IsZGroup.isCyclic_commutator G
  by_cases hb : commutator G = ⊥
  · have := (commutator_eq_bot_iff G).mp hb
    infer_instance
  · have hn := h (commutator G) hb hc
    rw [normalizer_eq_top] at hn
    exact isCyclic_of_surjective (topEquiv : (⊤ : Subgroup G) ≃* G) topEquiv.surjective

/-- Every odd-order subgroup of the actual characteristic-two PSL₂ is cyclic. -/
public theorem isCyclic_of_odd {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (H : Subgroup (PSL2MatrixGroup F)) (hodd : Odd (Nat.card H)) : IsCyclic H := by
  apply cyclic_of_cyclic_normalizers
  intro C hCne hCc
  let D := C.map H.subtype
  have hDC : Nat.card D = Nat.card C := card_map_of_injective H.subtype_injective
  have hDo : Odd (Nat.card D) := hDC ▸ hodd.of_dvd_nat C.card_subgroup_dvd_card
  have hDc : IsCyclic D := by
    let := hCc
    exact isCyclic_of_surjective (C.equivMapOfInjective H.subtype H.subtype_injective)
      (C.equivMapOfInjective H.subtype H.subtype_injective).surjective
  have hDne : D ≠ ⊥ := by
    intro hd
    apply hCne
    apply eq_bot_iff.mpr
    intro x hx
    have hm : (x : PSL2MatrixGroup F) ∈ D := mem_map.mpr ⟨x, hx, rfl⟩
    rw [hd, mem_bot] at hm
    exact Subtype.ext hm
  obtain ⟨T, hDT, dT, _⟩ := exists_torus_of_cyclic hF hn D hDc hDo
  have hNT : (normalizer (C : Set H)).map H.subtype ≤ T := by
    rintro x ⟨y, hy, rfl⟩
    apply dT.odd_mem hDT hDne
    · exact le_normalizer_map H.subtype (mem_map.mpr ⟨y, hy, rfl⟩)
    · change Odd (orderOf (y : PSL2MatrixGroup F))
      simpa only [Subgroup.orderOf_coe] using hodd.of_dvd_nat (orderOf_dvd_natCard y)
  have : IsCyclic ((normalizer (C : Set H)).map H.subtype) := by
    let := dT.cyclic
    exact Subgroup.isCyclic_of_le hNT
  let e := (normalizer (C : Set H)).equivMapOfInjective H.subtype H.subtype_injective
  exact isCyclic_of_surjective e.symm e.symm.surjective

/-- An arbitrary odd subgroup lies in a full torus of order q−1 or q+1.
The witness includes normalizers of all its nontrivial subgroups. -/
public theorem exists_torus {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (H : Subgroup (PSL2MatrixGroup F)) (hodd : Odd (Nat.card H)) :
    ∃ T : Subgroup (PSL2MatrixGroup F), H ≤ T ∧ ReflectionData T ∧
      (Nat.card T = Nat.card F - 1 ∨ Nat.card T = Nat.card F + 1) :=
  exists_torus_of_cyclic hF hn H (isCyclic_of_odd hF hn H hodd) hodd

/-- The torus containing an odd subgroup transports through an actual model
isomorphism, retaining its order and reflection action. -/
public theorem exists_torus_of_equiv {G F : Type*} [Group G] [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (e : G ≃* PSL2MatrixGroup F) (H : Subgroup G) (hodd : Odd (Nat.card H)) :
    ∃ T : Subgroup G, H ≤ T ∧ ReflectionData T ∧
      (Nat.card T = Nat.card F - 1 ∨ Nat.card T = Nat.card F + 1) := by
  have hmap : Nat.card (H.map e.toMonoidHom) = Nat.card H :=
    card_map_of_injective e.injective
  obtain ⟨T, hHT, dT, hcT⟩ := exists_torus hF hn (H.map e.toMonoidHom) (hmap ▸ hodd)
  refine ⟨T.map e.symm.toMonoidHom, ?_, dT.map e.symm, ?_⟩
  · intro x hx
    exact mem_map.mpr ⟨e x, hHT (mem_map.mpr ⟨x, hx, rfl⟩), e.symm_apply_apply x⟩
  · simpa only [card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective] using hcT

/-- A normalizing involution inverts a nontrivial subgroup of a full torus;
in fact it inverts the whole torus. -/
public theorem involution_inverts_torus {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (T R : Subgroup (PSL2MatrixGroup F)) (hTc : IsCyclic T)
    (hc : Nat.card T = Nat.card F - 1 ∨ Nat.card T = Nat.card F + 1)
    (hRT : R ≤ T) (hRne : R ≠ ⊥) {t : PSL2MatrixGroup F}
    (ht : orderOf t = 2) (htN : t ∈ normalizer R) :
    ∀ x ∈ T, t * x * t⁻¹ = x⁻¹ :=
  (reflectionData_of_cyclic_card hF hn T hTc hc).involution_inverts hRT hRne ht htN

/-- The exact saturation and relative-centralizer calculation used in GLS4,
2.17.5: under the source normalizer bound, the odd subgroup is a full torus.
The hypothesis and index are in the actual model carrier, via the given equivalence. -/
public theorem odd_normalizer_of_equiv {G F : Type*} [Group G] [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (e : G ≃* PSL2MatrixGroup F) (H : Subgroup G) (hodd : Odd (Nat.card H))
    {t : G} (ht : orderOf t = 2) (htN : t ∈ normalizer H)
    (hnc : ¬ H ≤ centralizer ({t} : Set G))
    (hN : normalizer H ≤ H ⊔ zpowers t) :
    IsCyclic H ∧ (Nat.card H = Nat.card F - 1 ∨ Nat.card H = Nat.card F + 1) ∧
      (∀ x ∈ H, t * x * t⁻¹ = x⁻¹) ∧
      (centralizer ({t} : Set G)).relIndex H = Nat.card H := by
  let : Finite G := Finite.of_equiv (PSL2MatrixGroup F) e.symm.toEquiv
  obtain ⟨T, hHT, dT, hcT⟩ := exists_torus_of_equiv hF hn e H hodd
  have hHne : H ≠ ⊥ := fun h => hnc (h ▸ bot_le)
  have hinv := dT.involution_inverts hHT hHne ht htN
  let := dT.cyclic
  have he := eq_odd_abelian_overgroup_of_normalizer_le H T hHT dT.odd ht htN hN
  subst T
  exact ⟨dT.cyclic, hcT, hinv, centralizer_relIndex_eq_card_of_odd_inverted H hodd t hinv⟩

/-- Concrete PSL₂ form of the Section 17 normalizer calculation. -/
public theorem odd_normalizer {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (H : Subgroup (PSL2MatrixGroup F)) (hodd : Odd (Nat.card H))
    {t : PSL2MatrixGroup F} (ht : orderOf t = 2) (htN : t ∈ normalizer H)
    (hnc : ¬ H ≤ centralizer ({t} : Set (PSL2MatrixGroup F)))
    (hN : normalizer H ≤ H ⊔ zpowers t) :
    IsCyclic H ∧ (Nat.card H = Nat.card F - 1 ∨ Nat.card H = Nat.card F + 1) ∧
      (∀ x ∈ H, t * x * t⁻¹ = x⁻¹) ∧
      (centralizer ({t} : Set (PSL2MatrixGroup F))).relIndex H = Nat.card H :=
  odd_normalizer_of_equiv hF hn (MulEquiv.refl _) H hodd ht htN hnc hN

end BenderSuzuki.MatrixGroups.EvenOddTori
