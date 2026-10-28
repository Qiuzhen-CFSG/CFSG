module

public import Theory.AtlasPort.LinearGroups.G2.BinaryException
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions

/-!
# Ordinary components of G₂ cannot be PSL₃(2)

For field order greater than two, simplicity makes every nontrivial subnormal
subgroup the whole octonion group, whose order exceeds 168. At field order
two, perfectness puts each component inside the actual commutator subgroup;
its proved simplicity then identifies the component with G₂(2)′, of order
6048. Coefficient transport covers every field of order two.

These statements retain ordinary, relative componenthood and the distinction
between full G₂(2) and its derived subgroup. They apply to the smaller fixed
G₂ groups in the field-involution case of Aschbacher--Smith, proof of 15.3.38,
printed p.1137; see also 16.1.4(4), p.1171, and p.1191.
The actual carriers and group calculations come from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.PSL3TwoObstructions

private theorem component_eq_commutator {G : Type*} [Group G]
    [IsSimpleGroup (commutator G)] (L : Subgroup G)
    (hL : IsComponent G L) [Nontrivial L] : L = commutator G := by
  let : IsQuasisimple L := hL.2
  have hle : L ≤ commutator G := by
    calc
      L = ⁅L, L⁆ := (commutator_eq_self (H := L)).symm
      _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := commutator_mono le_top le_top
  rcases hL.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
    (inferInstance : IsSimpleGroup (commutator G)) with hb | ht
  · have hbot : L = ⊥ := by
      have he := congrArg (Subgroup.map (commutator G).subtype) hb
      simpa only [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using he
    exact ((nontrivial_iff_ne_bot L).mp inferInstance hbot).elim
  · exact le_antisymm hle (subgroupOf_eq_top.mp ht)

/-- The actual binary full group has no component isomorphic to PSL₃(2). -/
theorem no_binary_component (L : Subgroup (Model (ZMod 2)))
    (hL : IsComponent (Model (ZMod 2)) L) :
    ¬ Nonempty (L ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨e⟩
  let : Nontrivial L := e.toEquiv.nontrivial
  let : IsSimpleGroup (commutator (Model (ZMod 2))) := isSimple_commutator_binary
  have he := component_eq_commutator L hL
  have hc := Nat.card_congr e.toEquiv
  rw [he, LieAutomorphismExtensions.card_binaryDerived, Matrix.PSL3Two.card_PSL] at hc
  omega

/-- Every full finite-field G₂ carrier has order greater than 168. -/
theorem card_model_gt_component {F : Type*} [Field F] [Finite F] :
    168 < Nat.card (Model F) := by
  rw [card_Model]
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  calc
    168 < 2 ^ 6 * (2 ^ 6 - 1) * (2 ^ 2 - 1) := by norm_num
    _ ≤ Nat.card F ^ 6 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) := by gcongr

/-- There is no ordinary PSL₃(2) component of a full finite-field G₂ group.
The binary endpoint uses its actual proper commutator subgroup. -/
theorem no_component {F : Type*} [Field F] [Finite F]
    (L : Subgroup (Model F)) (hL : IsComponent (Model F) L) :
    ¬ Nonempty (L ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨e⟩
  let : Nontrivial L := e.toEquiv.nontrivial
  by_cases hq : 2 < Nat.card F
  · let : IsSimpleGroup (Model F) := isSimple hq
    rcases hL.1.eq_bot_or_top_of_isSimpleGroup inferInstance with hb | ht
    · exact ((nontrivial_iff_ne_bot L).mp inferInstance hb).elim
    · have hc := Nat.card_congr e.toEquiv
      rw [ht, Nat.card_congr topEquiv.toEquiv, Matrix.PSL3Two.card_PSL] at hc
      exact (Nat.ne_of_gt (card_model_gt_component (F := F))) hc
  · have hcard : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
    let d := fieldEquiv (binaryFieldEquiv hcard)
    exact no_binary_component (L.map d.toMonoidHom) (hL.map_equiv d)
      ⟨(d.subgroupMap L).symm.trans e⟩

/-- Any actual fixed-group equivalence with a smaller G₂ carrier excludes
an ordinary PSL₃(2) component; no Levi quotient is used. -/
theorem no_fixed_component_of_equiv {G F : Type*} [Group G] [Field F] [Finite F]
    (a : MulAut G) (d : a.fixedSubgroup ≃* Model F)
    (L : Subgroup a.fixedSubgroup) (hL : IsComponent a.fixedSubgroup L) :
    ¬ Nonempty (L ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨e⟩
  exact no_component (L.map d.toMonoidHom) (hL.map_equiv d)
    ⟨(d.subgroupMap L).symm.trans e⟩
end Atlas.G2.PSL3TwoObstructions
