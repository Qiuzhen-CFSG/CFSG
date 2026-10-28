module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.Choices
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.Witnesses

/-!
# The cubic-centralizer reduction for 15.3.60–61(1)

The actual swapped action on `U/Z` constructs a conjugate of `D_H`
centralized by `t`. Normalizer control promotes the local Sylow two-group
of `C_M(D_M)` to the ambient centralizer. Its order eight separates `D_M`
from `D_H`, whose centralizer contains a two-group of order sixteen.
The marked Sylow three-groups then give both involution nonfusion claims.

`source_cubic_witnesses` constructs `D_M`, `D_H`, `J_M`, the marked
generators and the separating involution from the genuine earlier local
conclusions and the exact recognition of 15.3.58. It proves the local
centralizer orders and all three nonfusion conclusions. The four clauses
of 15.3.59 remain explicit earlier inputs for the Fusion assembly to supply.
The original conditional reduction below is preserved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.60 and 15.3.61(1), printed p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

/-- Assemble the nonfusion conclusions from local cubic centralizers and the
actual swapped action. The centralized conjugate of `D_H` is derived. -/
theorem nonfusion_of_swapped_action [Finite G]
    (Z ZS M DM P2 R : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hZS : ZS ≤ centralizerH Z) (hZZS : Z ≤ ZS) (hZ : Nat.card Z = 2)
    (hU : closureU Z ZS = coreQ Z) (hactor : Nat.card (ActorQuotient Z) = 336)
    (t : centralizerH Z) (ht : (t : G) ^ 2 = 1)
    (z v : G) (hz : zpowers z = Z) (hv : orderOf v = 2)
    (e : VectorQuotient Z ZS ≃* Multiplicative W) (s : W ≃ₗ[ZMod 2] W)
    (he : ∀ q, e (quotientAction Z ZS t q) = Multiplicative.ofAdd (s (e q).toAdd))
    (A B : Submodule (ZMod 2) W) (hAB : IsCompl A B)
    (hA : ∀ w ∈ A, s w ∈ B) (hB : ∀ w ∈ B, s w ∈ A)
    (D : Subgroup (ActorQuotient Z)) (hD : Nat.card D = 3)
    (hDC : D ≤ centralizer ({QuotientGroup.mk' (pCore 2 (centralizerH Z)) t} :
      Set (ActorQuotient Z)))
    (PH : Sylow 3 (centralizerH Z))
    (hDM : Nat.card DM = 3) (htM : DM ≤ centralizer ({(t : G)} : Set G))
    (hP2 : IsPGroup 2 P2) (hP2card : Nat.card P2 = 8)
    (hP2D : P2 ≤ centralizer (DM : Set G))
    (hlocal : ¬ 2 ∣ P2.relIndex (M ⊓ centralizer (DM : Set G)))
    (hcenter : (center P2).map P2.subtype = zpowers v)
    (hcontrol : centralizer ({v} : Set G) ≤ M)
    (hR : IsPGroup 2 R) (hRcard : Nat.card R = 16)
    (hRDH : R ≤ centralizer
      ((PH : Subgroup (centralizerH Z)).map (centralizerH Z).subtype : Set G))
    (Pv : Sylow 3 (centralizer ({v} : Set G)))
    (hPv : (Pv : Subgroup (centralizer ({v} : Set G))).map
      (centralizer ({v} : Set G)).subtype = DM) :
    ¬ SubgroupConjugate DM ((PH : Subgroup (centralizerH Z)).map (centralizerH Z).subtype) ∧
      ¬ IsConj (t : G) z ∧ ¬ IsConj (t : G) v := by
  have hPH := sylow_three_card_of_actor_card Z hactor PH
  have hDH : Nat.card ((PH : Subgroup (centralizerH Z)).map (centralizerH Z).subtype) = 3 := by
    rw [card_map_of_injective (centralizerH Z).subtype_injective]
    exact hPH
  have htH := source_centralizes_conjugate Z ZS hZS hZZS hZ hU t ht
    e s he A B hAB hA hB D hD hDC PH hPH
  obtain ⟨Pz, hPz⟩ := sylow_of_marked_generator Z z hz PH
  obtain ⟨PM, hPMmap⟩ := centralizer_sylow_of_center_involution M DM P2 v hv
    hP2 hP2D hlocal hcenter hcontrol
  have hPM : Nat.card PM = 8 := by
    rw [← hP2card, ← hPMmap, card_map_of_injective (centralizer (DM : Set G)).subtype_injective]
  exact nonfusion_of_local_centralizers DM _ R t z v PM hPM hR hRcard hRDH
    Pz hPz Pv hPv hDM hDH htM htH

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
