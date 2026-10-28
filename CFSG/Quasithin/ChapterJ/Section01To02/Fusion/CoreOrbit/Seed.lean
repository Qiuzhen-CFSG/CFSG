module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Definitions

/-!
# Constructing the representative in U_alpha intersect Q

The actual H/Q homomorphism has kernel Q. Its restriction to U_alpha has
image of order two by J.2.2(5), so D_alpha = U_alpha intersect Q has order 16.
Since U_alpha intersect HC = V has order eight, D_alpha contains w outside HC.
The representative is an involution because U_alpha is elementary abelian.

The order inequality |L| > |H| supplies ell in L minus H; J.2.3(9) makes
its conjugate of U distinct. The construction therefore requires only the
specified earlier-source statements, not a seed or involution-orbit assumption.

Source: Aschbacher–Smith, J.2.8, opening paragraph, printed p.437 / PDF p.448.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
variable {G : Type*} [Group G] [Finite G]

/-- The chosen representative is an involution because it lies in a conjugate of E32. -/
theorem ConjugateSeed.order_two (d : TypeRuSetup G) (s : ConjugateSeed d)
    (hZ : Nat.card d.Z = 2) : orderOf (s.w : G) = 2 := by
  let := d.elementary_U_of_card_Z hZ
  obtain ⟨u, hu, he⟩ := s.mem_conjugate
  apply orderOf_eq_prime
  · rw [← he, ← map_pow, elemPow_eq_one_of_isElementaryAbelian u hu, map_one]
  · exact fun he => s.outside (he.symm ▸ d.HC.one_mem)

/-- An order-32 subgroup with image of order two in H/Q meets Q in order 16. -/
theorem card_conjugate_intersection_Q (d : TypeRuSetup G) (A : Subgroup G)
    (hAH : A ≤ d.H) (hA : Nat.card A = 32)
    (himage : Nat.card ((A.subgroupOf d.H).map d.ru2.quotientMap) = 2) :
    Nat.card (A ⊓ d.Q : Subgroup G) = 16 := by
  let f : A →* S5 := d.ru2.quotientMap.comp (inclusion hAH)
  have hr : f.range = (A.subgroupOf d.H).map d.ru2.quotientMap := by
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      exact mem_map.mpr ⟨⟨a, hAH a.property⟩, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hk : f.ker = d.Q.subgroupOf A := by
    ext a
    change d.ru2.quotientMap ⟨a, hAH a.property⟩ = 1 ↔ (a : G) ∈ d.Q
    change (⟨a, hAH a.property⟩ : d.H) ∈ d.ru2.quotientMap.ker ↔ _
    rw [d.ru2.quotient_kernel]
    rfl
  have hkc : Nat.card f.ker = Nat.card (A ⊓ d.Q : Subgroup G) := by
    rw [hk, ← inf_subgroupOf_left]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hc := f.ker.index_mul_card
  rw [index_ker, hr, himage, hkc, hA] at hc
  omega

/-- The order-16 intersection cannot lie in the order-eight intersection with HC. -/
theorem exists_seed_of_conjugate (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2)
    (l : d.L) (hAH : d.U.map (MulAut.conj (l : G)).toMonoidHom ≤ d.H)
    (himage : Nat.card (((d.U.map (MulAut.conj (l : G)).toMonoidHom).subgroupOf d.H).map
      d.ru2.quotientMap) = 2)
    (hinter : d.U.map (MulAut.conj (l : G)).toMonoidHom ⊓ d.HC = d.V) :
    Nonempty (ConjugateSeed d) := by
  let A := d.U.map (MulAut.conj (l : G)).toMonoidHom
  have hcA : Nat.card A = 32 := by
    rw [card_map_of_injective (MulAut.conj (l : G)).injective, d.ru2.card_U hZ]
  have hcD : Nat.card (A ⊓ d.Q : Subgroup G) = 16 :=
    card_conjugate_intersection_Q d A hAH hcA himage
  have hn : ¬ A ⊓ d.Q ≤ d.HC := by
    intro he
    have hle : A ⊓ d.Q ≤ d.V := hinter ▸ le_inf inf_le_left he
    have hc := card_le_of_le hle
    rw [hcD, d.ru1.card_V] at hc
    omega
  have hw : ∃ w : (A ⊓ d.Q : Subgroup G), (w : G) ∉ d.HC := by
    by_contra! he
    exact hn (fun w hw => he ⟨w, hw⟩)
  obtain ⟨w, hw⟩ := hw
  exact ⟨⟨l, ⟨w, w.property.2⟩, w.property.1, hw⟩⟩

/-- Construct the source representative from the literal earlier J.2.2(5) and J.2.3(9)
conclusions. These earlier-source premises remain with their existing producers. -/
theorem exists_conjugateSeed (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2)
    (h23 : ∀ l : d.L, (l : G) ∉ d.H →
      d.U ⊓ d.U.map (MulAut.conj (l : G)).toMonoidHom = d.V)
    (h22 : ∀ l : d.L, d.U.map (MulAut.conj (l : G)).toMonoidHom ≠ d.U →
      d.U.map (MulAut.conj (l : G)).toMonoidHom ≤ d.H ∧
      Nat.card (((d.U.map (MulAut.conj (l : G)).toMonoidHom).subgroupOf d.H).map
        d.ru2.quotientMap) = 2 ∧
      d.U.map (MulAut.conj (l : G)).toMonoidHom ⊓ d.HC = d.V) :
    Nonempty (ConjugateSeed d) := by
  have hl : ∃ l : d.L, (l : G) ∉ d.H := by
    by_contra! hn
    have hc := card_le_of_le (show d.L ≤ d.H from fun l hl => hn ⟨l, hl⟩)
    rw [d.ru1.card_L, d.ru2.card_H hZ] at hc
    omega
  obtain ⟨l, hl⟩ := hl
  have hne : d.U.map (MulAut.conj (l : G)).toMonoidHom ≠ d.U := by
    intro he
    have hinter := h23 l hl
    rw [he, inf_idem] at hinter
    have hc := d.ru2.card_U hZ
    change Nat.card d.U = 32 at hc
    rw [hinter, d.ru1.card_V] at hc
    omega
  obtain ⟨hAH, himage, hinter⟩ := h22 l hne
  exact exists_seed_of_conjugate d hZ l hAH himage hinter


end CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
