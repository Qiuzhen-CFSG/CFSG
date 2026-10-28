module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.SmallModelExclusion.Local
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The alternating-six and binary symplectic-derived exclusions

The local intersection contains a Sylow two-subgroup and has order divisible
by nine. In A₆ this would give a proper subgroup of index five, whose faithful
coset action contradicts 360 not dividing 5!. The binary symplectic-derived
case uses the explicit polar-representation equivalence PSp₄(2)′ ≃ A₆.

Source: Aschbacher--Smith, initial parabolic selection, printed p.1139,
with the small-derived convention in Theorem C and Remark A.2.4, p.33.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
open SmallModelExclusion
variable {X : Type*} [Group X] [Finite X]
variable {G : Type*} [Group G] [Finite G]
variable {L MI Y S : Subgroup G} [L.Normal]
private instance component_normal : (centralizerQuotientComponent L).Normal :=
  (inferInstance : L.Normal).map (centralizerQuotientMap L) (QuotientGroup.mk'_surjective _)

omit [Finite X] in
private theorem a6_sylow_local_nine (e : X ≃* alternatingGroup (Fin 6))
    (H : Subgroup X) (P : Sylow 2 X) (hP : (P : Subgroup X) ≤ H)
    (hH : H ≠ ⊤) (h9 : 9 ∣ Nat.card H) : False := by
  let : Finite X := Finite.of_equiv _ e.toEquiv.symm
  have hcard : Nat.card X = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num [Nat.factorial]
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup X := (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  have h8 : 8 ∣ Nat.card H :=
    (P.pow_dvd_card_of_pow_dvd_card (n := 3) (by rw [hcard]; decide)).trans (card_dvd_of_le hP)
  have h72 : 72 ∣ Nat.card H := (by decide : Nat.Coprime 8 9).mul_dvd_of_dvd_of_dvd h8 h9
  have hi : H.index ∣ 5 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 72)).mp
    have hd := Nat.mul_dvd_mul_right h72 H.index
    rw [card_mul_index, hcard] at hd
    exact hd
  have hi5 : H.index = 5 := ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hi).resolve_left
    (fun hi1 => hH (index_eq_one.mp hi1))
  have hb : H.normalCore = ⊥ := by
    rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (hH (top_unique (h ▸ H.normalCore_le)))
  have hd : H.normalCore.index ∣ H.index.factorial := by
    rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
    exact card_subgroup_dvd_card (MulAction.toPermHom X (X ⧸ H)).range
  rw [hb, index_bot, hcard, hi5] at hd
  norm_num at hd

/-- A₆ is excluded by the actual Sylow intersection and its faithful coset action. -/
theorem Setup.not_alternating_six (d : Setup L MI Y S) (hp : QuotientParabolic L MI S)
    (hm : Nonempty (centralizerQuotientComponent L ≃* alternatingGroup (Fin 6))) : False := by
  obtain ⟨e⟩ := hm
  obtain ⟨Q, hQ⟩ := local_sylow d.quotient_local
  exact a6_sylow_local_nine e _ Q hQ (local_proper d hp)
    (local_nine d.quotient_local (quotient_two d))

/-- The actual commutator of the binary projective symplectic carrier is excluded. -/
theorem Setup.not_symplectic_derived (d : Setup L MI Y S) (hp : QuotientParabolic L MI S)
    (hm : Nonempty (centralizerQuotientComponent L ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : False := by
  obtain ⟨e⟩ := hm
  exact d.not_alternating_six hp
    ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
