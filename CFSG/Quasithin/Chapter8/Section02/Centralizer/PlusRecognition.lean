module
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.Definitions
public import Theory.GroupTheory.DihedralCentralProductFourSix

/-!
# The intrinsic plus-type deduction in 8.2.12

Let `E` be the normal closure of `V_z` inside the literal involution centralizer
`C_G(z)`. The local self-centralizer bound puts `Z(E)` in `V_z`. Transporting
`V_z` along its inclusion in its normal closure preserves its elementary
structure and order. Intrinsic dihedral recognition now gives the fourfold
or sixfold quotient from extraspeciality and the two source orders.

This discharges the plus-type step of Aschbacher–Smith 8.2.12(1), printed
p.722 (PDF p.739). The centralizer assembly owner `qt-8-02-centralizer` retains
the earlier local-action calculations, extraspeciality, orders and
self-centralizer bound, and the rest of 8.2.11–13.
-/

namespace CFSG.Quasithin.Chapter8.Section02.Centralizer
open Subgroup

variable {G : Type*} [Group G]

/-- The source self-centralizer calculation implies the center containment
needed for the intrinsic plus-type recognition. -/
public theorem center_le_restricted_Vz (z : G)
    (Vz : Subgroup (centralizer ({z} : Set G)))
    (hself : centralizer (Vz.subgroupOf (centralizerClosure z Vz) :
      Set (centralizerClosure z Vz)) ≤ Vz.subgroupOf (centralizerClosure z Vz)) :
    center (centralizerClosure z Vz) ≤ Vz.subgroupOf (centralizerClosure z Vz) :=
  (center_le_centralizer _).trans hself

variable [Finite G]

/-- Recognition of the literal closure from its already established source
premises; `n + 1` is the number of dihedral factors. -/
public noncomputable def centralizerClosureRecognition (n : ℕ) (z : G)
    (Vz : Subgroup (centralizer ({z} : Set G))) [IsElementaryAbelian 2 Vz]
    [IsExtraspecial 2 (centralizerClosure z Vz)]
    (hE : Nat.card (centralizerClosure z Vz) = 2 ^ (1 + 2 * (n + 1)))
    (hVz : Nat.card Vz = 2 ^ (n + 2))
    (hself : centralizer (Vz.subgroupOf (centralizerClosure z Vz) :
      Set (centralizerClosure z Vz)) ≤ Vz.subgroupOf (centralizerClosure z Vz)) :
    centralizerClosure z Vz ≃* DihedralCentralProductFourSix.Model n := by
  have hle : Vz ≤ centralizerClosure z Vz := le_normalClosure
  let : IsElementaryAbelian 2 (Vz.subgroupOf (centralizerClosure z Vz)) :=
    IsElementaryAbelian.subgroupOf hle
  have hcard : Nat.card (Vz.subgroupOf (centralizerClosure z Vz)) = 2 ^ (n + 2) :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hVz
  exact DihedralCentralProductFourSix.recognition n hE _ hcard
    (center_le_restricted_Vz z Vz hself)

/-- The two `e = 4` cases in 8.2.12(1), with target the literal fourfold quotient. -/
public noncomputable def centralizerClosureFourRecognition (z : G)
    (Vz : Subgroup (centralizer ({z} : Set G))) [IsElementaryAbelian 2 Vz]
    [IsExtraspecial 2 (centralizerClosure z Vz)]
    (hE : Nat.card (centralizerClosure z Vz) = 2 ^ (1 + 2 * 4))
    (hVz : Nat.card Vz = 2 ^ (4 + 1))
    (hself : centralizer (Vz.subgroupOf (centralizerClosure z Vz) :
      Set (centralizerClosure z Vz)) ≤ Vz.subgroupOf (centralizerClosure z Vz)) :
    centralizerClosure z Vz ≃* DihedralCentralProductFourSix.FourModel :=
  centralizerClosureRecognition 3 z Vz hE hVz hself

/-- The `e = 6` case in 8.2.12(1), with target the existing sixfold quotient. -/
public noncomputable def centralizerClosureSixRecognition (z : G)
    (Vz : Subgroup (centralizer ({z} : Set G))) [IsElementaryAbelian 2 Vz]
    [IsExtraspecial 2 (centralizerClosure z Vz)]
    (hE : Nat.card (centralizerClosure z Vz) = 2 ^ (1 + 2 * 6))
    (hVz : Nat.card Vz = 2 ^ (6 + 1))
    (hself : centralizer (Vz.subgroupOf (centralizerClosure z Vz) :
      Set (centralizerClosure z Vz)) ≤ Vz.subgroupOf (centralizerClosure z Vz)) :
    centralizerClosure z Vz ≃* DihedralCentralProductSix.Model :=
  (centralizerClosureRecognition 5 z Vz hE hVz hself).trans
    DihedralCentralProductFourSix.sixModelEquiv

/-- Application to the literal `V_z = [V,O₂(L_z)]` and `E = ⟨V_z^C⟩`.
The normalization and `z ∈ V` premises supply the original embedding in `C`;
all orders here are those of the actual source subgroups. -/
public noncomputable def sourceClosureRecognition (n : ℕ)
    (L V : Subgroup G) [IsMulCommutative V] (z : G)
    (hz : z ∈ V) (hn : L ≤ normalizer (V : Set G))
    [IsElementaryAbelian 2 (commutatorSpace L V z)]
    [IsExtraspecial 2 (sourceClosure L V z)]
    (hE : Nat.card (sourceClosure L V z) = 2 ^ (1 + 2 * (n + 1)))
    (hVz : Nat.card (commutatorSpace L V z) = 2 ^ (n + 2))
    (hself : centralizer
      (((commutatorSpace L V z).subgroupOf (centralizer ({z} : Set G))).subgroupOf
        (sourceClosure L V z) : Set (sourceClosure L V z)) ≤
      ((commutatorSpace L V z).subgroupOf (centralizer ({z} : Set G))).subgroupOf
        (sourceClosure L V z)) :
    sourceClosure L V z ≃* DihedralCentralProductFourSix.Model n := by
  have hle := commutatorSpace_le_centralizer L V z hz hn
  let : IsElementaryAbelian 2
      ((commutatorSpace L V z).subgroupOf (centralizer ({z} : Set G))) :=
    IsElementaryAbelian.subgroupOf hle
  let : IsExtraspecial 2 (centralizerClosure z
      ((commutatorSpace L V z).subgroupOf (centralizer ({z} : Set G)))) :=
    (inferInstance : IsExtraspecial 2 (sourceClosure L V z))
  have hcard : Nat.card
      ((commutatorSpace L V z).subgroupOf (centralizer ({z} : Set G))) = 2 ^ (n + 2) :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hVz
  exact centralizerClosureRecognition n z _ hE hcard hself

end CFSG.Quasithin.Chapter8.Section02.Centralizer
