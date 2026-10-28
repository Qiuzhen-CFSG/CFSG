module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActions
public import Theory.GroupTheory.PResidual.PrimeToIntersection

/-!
# Residual identities for the source small-action argument

The literal orbit span Kc = ⟨O²(H)^Mc⟩ equals O^{3′}(Mc). Intersecting
with I therefore recovers Kc as O^{3′}(Mc ∩ I) whenever Kc lies in I.
This is the residual conclusion of 15.2.21(1), on MI = Mc ∩ I.

When K = Kc, the earlier M ∩ K = O₂(K) identity kills O^{3′}(M ∩ Mc).
Monotonicity then proves 15.2.21(2). No residual-collapse callback is used.
The companion ComponentModels module discharges the intersection identity
from the original wreath quotient of H. The action splitting and centralization
parts of 15.2.21(1) remain separate obligations of this source family.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.8, 15.2.12(4), and 15.2.21(1--2), printed pp.1110--1114;
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The residual identity of 15.2.21(1) uses MI = Mc ∩ I. -/
theorem orbit_eq_residual_intersection
    (hKc : smallActionKc H Mc ≤ I) :
    smallActionKc H Mc =
      (primeToResidual 3 (Mc ⊓ I : Subgroup G)).map (Mc ⊓ I).subtype := by
  have he := embedded_primeToResidual_intersection 3 Mc I
  rw [← d.orbit_residual, inf_eq_left.mpr hKc] at he
  have hid := congrArg (Subgroup.map Mc.subtype)
    (embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 Mc) le_rfl)
  rw [map_embedded_primeToResidual_of_hom, ← d.orbit_residual] at hid
  exact hid.symm.trans he

/-- The source centralization conclusion places Kc in the correct intersection. -/
theorem orbit_eq_residual_MI_of_centralizes (hI : PlaneEscapes Mc ZS I)
    (hc : smallActionKc H Mc ≤ centralizer (ZS : Set G)) :
    smallActionKc H Mc =
      (primeToResidual 3 (Mc ⊓ I : Subgroup G)).map (Mc ⊓ I).subtype :=
  orbit_eq_residual_intersection d
    (hc.trans ((d.centralizer_le_intersection hI).trans inf_le_right))

omit d in
private theorem threeResidual_eq_bot_of_twoGroup (A : Subgroup G) (hA : IsPGroup 2 A) :
    primeToResidual 3 A = ⊥ := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  apply bot_unique
  apply primeToResidual_le
  rw [index_bot, hn]
  exact (by decide : Nat.Coprime 3 2).pow_right n

/-- The intersection computation in 15.2.8 proves the residual collapse in 15.2.21(2). -/
theorem intersection_threeResidual_eq_bot
    (hK : smallActionK H = smallActionKc H Mc)
    (hMK : M ⊓ smallActionK H = (smallActionK H).pCoreIn 2) :
    primeToResidual 3 (M ⊓ Mc : Subgroup G) = ⊥ := by
  have he := embedded_primeToResidual_intersection 3 Mc M
  have hKr : smallActionK H = (primeToResidual 3 Mc).map Mc.subtype :=
    hK.trans d.orbit_residual
  rw [← hKr, inf_comm (smallActionK H) M, hMK,
    threeResidual_eq_bot_of_twoGroup _ (isPGroup_pCoreIn 2 _), Subgroup.map_bot,
    inf_comm Mc M] at he
  exact ((primeToResidual 3 (M ⊓ Mc : Subgroup G)).map_eq_bot_iff_of_injective
    (M ⊓ Mc).subtype_injective).mp he.symm

/-- 15.2.21(2), with only the genuine preceding intersection clause of 15.2.8 explicit. -/
theorem source_15_2_21_2
    (hK : smallActionK H = smallActionKc H Mc)
    (hMK : M ⊓ smallActionK H = (smallActionK H).pCoreIn 2) :
    IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)) := by
  have hCA : M ⊓ centralizer (V : Set G) ≤ M ⊓ Mc := by
    rw [d.intersection]
    exact le_sup_left
  have hm := embedded_primeToResidual_mono 3 hCA
  rw [intersection_threeResidual_eq_bot d hK hMK, Subgroup.map_bot] at hm
  exact ((primeToResidual 3 (M ⊓ centralizer (V : Set G) : Subgroup G)).map_eq_bot_iff_of_injective
    (M ⊓ centralizer (V : Set G)).subtype_injective).mp (bot_unique hm)
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
