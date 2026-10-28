module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.SpecialFromFormulas
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Multiplication
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Unipotent

/-!
# Special arms radical and unipotent center in the genuine triality carrier

The highest-root subgroup is defined by the actual curve at position 11,
descended through elementary graph-field fixed points. It has order q and
lies in the embedded centers of the arms root radical and the unipotent group.
The cubic trace pairing has no noncentral radical, including when q = 2.

The actual Geck multiplication and commutator formulas discharge the premises
of `SpecialFromFormulas`: the arms radical has center of order q, equal to its
commutator and Frattini subgroups. Together with `FixedPoints`, this is the
special two-group of order q^9 denoted q^(1+8) in F.1.11.

The embedded unipotent center lies in the arms radical, hence in its center,
and therefore equals the same highest-root subgroup. The arms radical and
arms Levi subgroup both centralize it. All statements include q = 2 and concern
the actual descended root subgroup; identification with the separately defined
parabolic radical and local factor is left to the parabolic assembly.

Source: Aschbacher–Smith F.1.11–12 (`refs/quasithin.pdf`, pp.262–264),
and GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

noncomputable section
namespace Triality.Standard.RadicalCoordinates.Centers
open Parabolics

/-- The center consists exactly of the descended highest-root parameters. -/
theorem mem_center_arms_iff (P : Parameters) (hp : P.prime = 2) (x : armsSubgroup P) :
    x ∈ Subgroup.center (armsSubgroup P) ↔
      ∃ z : fixedField P, armsEquiv P hp (centralParameters P z) = x :=
  mem_center_arms_iff_of_commutator P hp (armsEquiv_commutator P hp) x

/-- The center of the arms radical, embedded in the genuine carrier, is the
descent of the actual curve at root position 11. -/
theorem embedded_center_arms (P : Parameters) (hp : P.prime = 2) :
    (Subgroup.center (armsSubgroup P)).map (armsSubgroup P).subtype = highestRoot P :=
  embedded_center_arms_of_commutator P hp (armsEquiv_commutator P hp)

theorem card_center_arms (P : Parameters) (hp : P.prime = 2) :
    Nat.card (Subgroup.center (armsSubgroup P)) = P.q :=
  card_center_arms_of_commutator P hp (armsEquiv_commutator P hp)

theorem center_arms_eq_commutator (P : Parameters) (hp : P.prime = 2) :
    Subgroup.center (armsSubgroup P) = _root_.commutator (armsSubgroup P) :=
  center_arms_eq_commutator_of_formula P hp (armsEquiv_commutator P hp)

/-- The finite two-group Frattini formula applies to the actual squares and
commutators, with no additional coordinate or specialness premise. -/
theorem center_arms_eq_frattini (P : Parameters) (hp : P.prime = 2) :
    Subgroup.center (armsSubgroup P) = frattini (armsSubgroup P) :=
  center_arms_eq_frattini_of_formulas P hp (armsEquiv_commutator P hp)
    (armsEquiv_square P hp)

private theorem embedded_center_le_of_le {G : Type*} [Group G]
    {U S : Subgroup G} (hUS : U ≤ S)
    (hZU : (Subgroup.center S).map S.subtype ≤ U) :
    (Subgroup.center S).map S.subtype ≤ (Subgroup.center U).map U.subtype := by
  rintro g ⟨z, hz, rfl⟩
  refine ⟨⟨z.val, hZU ⟨z, hz, rfl⟩⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro y
  apply Subtype.ext
  exact congrArg (fun x : S => x.val)
    (Subgroup.mem_center_iff.mp hz (⟨y.val, hUS y.property⟩ : S))

/-- The unipotent center, with its actual embedding in the carrier, is the
same highest-root subgroup as the arms radical center. -/
theorem embedded_center_unipotent (P : Parameters) (hp : P.prime = 2) :
    (Subgroup.center (unipotent P)).map (unipotent P).subtype = highestRoot P := by
  apply le_antisymm
  · rw [← embedded_center_arms P hp]
    exact embedded_center_le_of_le
      (descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .arms))
      (center_unipotent_le_descendedRootSubgroup P hp)
  · exact highestRoot_le_center_unipotent P hp

theorem card_center_unipotent (P : Parameters) (hp : P.prime = 2) :
    Nat.card (Subgroup.center (unipotent P)) = P.q := by
  rw [← Subgroup.card_map_of_injective (unipotent P).subtype_injective,
    embedded_center_unipotent P hp]
  exact card_highestRoot P hp

private theorem le_centralizer_embedded_center {G : Type*} [Group G] (U : Subgroup G) :
    U ≤ Subgroup.centralizer ((Subgroup.center U).map U.subtype : Set G) := by
  intro x hx
  apply Subgroup.mem_centralizer_iff.mpr
  rintro z ⟨z, hz, rfl⟩
  exact (congrArg (fun y : U => y.val)
    (Subgroup.mem_center_iff.mp hz (⟨x, hx⟩ : U))).symm

theorem arms_sup_levi_le_centralizer_highestRoot (P : Parameters) (hp : P.prime = 2) :
    armsSubgroup P ⊔ levi P .arms ≤
      Subgroup.centralizer (highestRoot P : Set (Carrier P)) := by
  apply sup_le
  · rw [← embedded_center_arms P hp]
    exact le_centralizer_embedded_center _
  · exact levi_le_centralizer_highestRoot P hp

/-- The source orientation: the arms radical together with its Levi subgroup
centralizes the embedded center of the full unipotent subgroup. -/
theorem arms_sup_levi_le_centralizer_center_unipotent (P : Parameters) (hp : P.prime = 2) :
    armsSubgroup P ⊔ levi P .arms ≤ Subgroup.centralizer
      ((Subgroup.center (unipotent P)).map (unipotent P).subtype : Set (Carrier P)) := by
  rw [embedded_center_unipotent P hp]
  exact arms_sup_levi_le_centralizer_highestRoot P hp

end Triality.Standard.RadicalCoordinates.Centers
