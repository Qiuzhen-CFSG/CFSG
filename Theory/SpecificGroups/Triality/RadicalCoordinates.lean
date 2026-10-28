module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.FixedPoints
public import Theory.SpecificGroups.Triality.RadicalCoordinates.ParabolicSplitting
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators

/-!
# Coordinates and local structure of genuine triality radicals

The Geck root products are normal in their split parabolics, identifying them
with the original radical candidates. Their faithful graph-field coordinates
survive elementary restriction and the actual central quotient. Thus the arms
radical is a two-group of order q^9 with center of order q equal to its derived
and Frattini subgroups; the central radical is a two-group of order q^11.

The imported splitting theorem gives `localFactor = radical ⊔ levi` and
disjointness, retaining the torus when treating the full parabolic. For q > 2,
the concrete Levi commutators generate the radical; relative normality gives
the reverse inclusion. The arms radical center and the unipotent center have
the same highest-root image in the carrier, centralized by the arms local
factor. All statements except commutator generation include q = 2.

This supplies the radical calculations and center orientation used in
F.1.12(I)(4). Identifying the radicals with the two-cores, the Levi quotients,
and the solvable residuals belongs to the consuming local-structure assembly.

Source: Aschbacher–Smith F.1.11–12 (`refs/quasithin.pdf`, printed pp.262–264);
GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.PositiveCoordinates
namespace Triality.Standard.RadicalCoordinates
open Parabolics

theorem radical_card_of_root_normal (P : Parameters) (hp : P.prime = 2) (a : Node)
    (hN : ((rootSubgroup P a).subgroupOf (splitParabolic P a)).Normal) :
    Nat.card (radical P a) = P.q ^ fixedDimension a := by
  rw [radical, splitRadical_eq_rootSubgroup_of_normal P hp a hN]
  exact card_descendedRootSubgroup P hp a

theorem radical_isPGroup_of_root_normal (P : Parameters) (hp : P.prime = 2) (a : Node)
    (hN : ((rootSubgroup P a).subgroupOf (splitParabolic P a)).Normal) :
    IsPGroup 2 (radical P a) := by
  rw [radical, splitRadical_eq_rootSubgroup_of_normal P hp a hN]
  exact isPGroup_descendedRootSubgroup P hp a

/-- An unconditional divisibility statement for the originally defined radical. -/
theorem source_order_dvd_radical_card (P : Parameters) (hp : P.prime = 2) (a : Node) :
    P.q ^ fixedDimension a ∣ Nat.card (radical P a) := by
  rw [← card_descendedRootSubgroup P hp a]
  exact Subgroup.card_dvd_of_le (descendedRootSubgroup_le_radical P hp a)

/-- Faithful ordered coordinates for the originally defined radical, through
the fixed root product and the actual central quotient. -/
def radicalEquiv (P : Parameters) (hp : P.prime = 2) (a : Node) :
    RootOrbitParameters P a ≃ radical P a :=
  (rootOrbitEquiv P a).trans ((fixedRootEquiv P hp a).trans
    ((descendedRootEquiv P hp a).toEquiv.trans
      (MulEquiv.subgroupCongr (radical_eq_descendedRootSubgroup P hp a).symm).toEquiv))

theorem radical_card (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Nat.card (radical P a) = P.q ^ fixedDimension a := by
  rw [radical_eq_descendedRootSubgroup P hp a]
  exact card_descendedRootSubgroup P hp a

theorem radical_arms_card (P : Parameters) (hp : P.prime = 2) :
    Nat.card (radical P .arms) = P.q ^ 9 :=
  radical_card P hp .arms

theorem radical_central_card (P : Parameters) (hp : P.prime = 2) :
    Nat.card (radical P .central) = P.q ^ 11 :=
  radical_card P hp .central

theorem radical_isPGroup (P : Parameters) (hp : P.prime = 2) (a : Node) :
    IsPGroup 2 (radical P a) := by
  rw [radical_eq_descendedRootSubgroup P hp a]
  exact isPGroup_descendedRootSubgroup P hp a

theorem card_center_radical_arms (P : Parameters) (hp : P.prime = 2) :
    Nat.card (Subgroup.center (radical P .arms)) = P.q := by
  rw [radical_eq_descendedRootSubgroup P hp .arms]
  exact Centers.card_center_arms P hp

theorem center_radical_arms_eq_commutator (P : Parameters) (hp : P.prime = 2) :
    Subgroup.center (radical P .arms) = _root_.commutator (radical P .arms) := by
  rw [radical_eq_descendedRootSubgroup P hp .arms]
  exact Centers.center_arms_eq_commutator P hp

theorem center_radical_arms_eq_frattini (P : Parameters) (hp : P.prime = 2) :
    Subgroup.center (radical P .arms) = frattini (radical P .arms) := by
  rw [radical_eq_descendedRootSubgroup P hp .arms]
  exact Centers.center_arms_eq_frattini P hp

/-- The intrinsic arms radical center has the actual highest-root image
in the genuine triality carrier. -/
theorem embedded_center_radical_arms (P : Parameters) (hp : P.prime = 2) :
    (Subgroup.center (radical P .arms)).map (radical P .arms).subtype =
      Centers.highestRoot P := by
  rw [radical_eq_descendedRootSubgroup P hp .arms]
  exact Centers.embedded_center_arms P hp

theorem embedded_center_radical_arms_eq_center_unipotent
    (P : Parameters) (hp : P.prime = 2) :
    (Subgroup.center (radical P .arms)).map (radical P .arms).subtype =
      (Subgroup.center (unipotent P)).map (unipotent P).subtype := by
  rw [embedded_center_radical_arms P hp, Centers.embedded_center_unipotent P hp]

/-- The source's arms orientation, with the unipotent center embedded in
the same ambient group as the local factor. -/
theorem localFactor_arms_le_centralizer_center_unipotent
    (P : Parameters) (hp : P.prime = 2) :
    localFactor P .arms ≤ Subgroup.centralizer
      ((Subgroup.center (unipotent P)).map (unipotent P).subtype : Set (Carrier P)) := by
  rw [localFactor_eq_root_sup_levi P hp .arms]
  exact Centers.arms_sup_levi_le_centralizer_center_unipotent P hp

theorem localFactor_arms_commutator_center_unipotent
    (P : Parameters) (hp : P.prime = 2) :
    ⁅localFactor P .arms,
      (Subgroup.center (unipotent P)).map (unipotent P).subtype⁆ = ⊥ :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (localFactor_arms_le_centralizer_center_unipotent P hp)

/-- Only normality inside the parabolic is used, not ambient normality. -/
theorem commutator_radical_levi_le (P : Parameters) (a : Node) :
    ⁅radical P a, levi P a⁆ ≤ radical P a := by
  apply Subgroup.le_normalizer_iff_commutator_le_left.mp
  exact (levi_le_parabolic P a).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P a)).mp
      (radical_normal P a))

/-- For q > 2 the actual Levi action generates the entire radical by
commutators, supplying the radical part of local-factor perfectness. -/
theorem commutator_radical_levi_eq (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (a : Node) : ⁅radical P a, levi P a⁆ = radical P a := by
  apply le_antisymm (commutator_radical_levi_le P a)
  rw [radical_eq_descendedRootSubgroup P hp a]
  exact LeviCommutators.descendedRootSubgroup_le_commutator P hp hq a

end Triality.Standard.RadicalCoordinates
