module

public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.SylowStructure
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.BinaryPrimeDisplacement
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Central fixed spaces and degree divisibility for triple-M₂₂

For the actual equality F*(G) = L, normality of L makes its cubic center
normal in G. Faithfulness and G-irreducibility force its fixed space to vanish;
no irreducibility of the restricted L-module is assumed. The genuine
extraspecial Sylow subgroup then makes the binary dimension divisible by six.
A cubic central actor moves the whole space, and an element inverting it
moves at least half the space.

Source: Aschbacher–Smith H.12.1, proof on printed p.394 (combined 1 March 2004
manuscript). The noncentral cubic displacement formula and the construction
of inversion witnesses are separate obligations in the remaining argument.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The center of L has no fixed vectors on a faithful irreducible G-module. -/
theorem center_fixedSpace_eq_bot (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) : fixedSpace ρ ((center L).map L.subtype) = ⊥ := by
  let : L.Normal := hF ▸ inferInstance
  by_contra h
  have hk := Representation.le_ker_of_normal_invariants_ne_bot ρ
    ((center L).map L.subtype) h
  have he : (center L).map L.subtype = ⊥ :=
    le_bot_iff.mp ((ρ.ker_eq_bot_iff.mpr hρ) ▸ hk)
  have hc := Subgroup.card_map_of_injective (K := center L) L.subtype_injective
  rw [he, Subgroup.card_bot, hL.center_card] at hc
  omega

/-- Transport vanishing to the actual Sylow center. -/
theorem sylow_center_invariants_eq_bot (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L) (P : Sylow 3 L)
    (hcenter : (center (P : Subgroup L)).map (P : Subgroup L).subtype = center L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) :
    invariants ((ρ.comp (L.subtype.comp (P : Subgroup L).subtype)).comp
      (center (P : Subgroup L)).subtype) = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have hvZ : v ∈ fixedSpace ρ ((center L).map L.subtype) := by
    intro z
    obtain ⟨a, ha, haz⟩ := z.property
    have haP : a ∈ (center (P : Subgroup L)).map (P : Subgroup L).subtype :=
      hcenter.symm ▸ ha
    obtain ⟨b, hb, hba⟩ := haP
    change ρ (z : G) v = v
    rw [← haz, ← hba]
    exact hv ⟨b, hb⟩
  rwa [center_fixedSpace_eq_bot L hL hF ρ hρ] at hvZ

variable [FiniteDimensional (ZMod 2) V]

/-- An extraspecial Sylow witness gives degree divisibility by six. -/
theorem six_dvd_finrank_of_sylow (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L) (P : Sylow 3 L)
    [IsExtraspecial 3 (P : Subgroup L)] (hcard : Nat.card P = 27)
    (hcenter : (center (P : Subgroup L)).map (P : Subgroup L).subtype = center L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) : 6 ∣ Module.finrank (ZMod 2) V :=
  BinaryCoprimeDegree.six_dvd_finrank_of_extraspecial_twentySeven
    (ρ.comp (L.subtype.comp (P : Subgroup L).subtype)) hcard
    (sylow_center_invariants_eq_bot L hL hF P hcenter ρ hρ)

/-- Every faithful irreducible binary G-module in the source setup has
 dimension divisible by six. -/
theorem six_dvd_finrank (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) : 6 ∣ Module.finrank (ZMod 2) V := by
  let P : Sylow 3 L := Classical.choice inferInstance
  obtain ⟨hc, he, hz⟩ := sylow_three_structure hL P
  let : IsExtraspecial 3 (P : Subgroup L) := he
  exact six_dvd_finrank_of_sylow L hL hF P hc hz ρ hρ

/-- A nonidentity element of Z(L) moves the whole module. -/
theorem central_three_fixedCodim (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (z : G)
    (hz : z ∈ (center L).map L.subtype) (ho : orderOf z = 3) :
    fixedCodim ρ (zpowers z) = Module.finrank (ZMod 2) V := by
  have he : zpowers z = (center L).map L.subtype := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz)
    rw [Nat.card_zpowers, ho,
      Subgroup.card_map_of_injective L.subtype_injective, hL.center_card]
  have h := fixedCodim_add_finrank ρ (zpowers z)
  rw [he, center_fixedSpace_eq_bot L hL hF ρ hρ, finrank_bot, Nat.add_zero] at h
  simpa only [he] using h

/-- Inverting the cubic center forces displacement at least half the degree. -/
theorem finrank_le_twice_of_inverts_center (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (z t : G)
    (hz : z ∈ (center L).map L.subtype) (ho : orderOf z = 3)
    (hi : t * z * t⁻¹ = z⁻¹) :
    Module.finrank (ZMod 2) V ≤ 2 * fixedCodim ρ (zpowers t) := by
  rw [← central_three_fixedCodim L hL hF ρ hρ z hz ho]
  exact fixedCodim_three_le_twice_of_inverted ρ z t ho hi
end CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement
