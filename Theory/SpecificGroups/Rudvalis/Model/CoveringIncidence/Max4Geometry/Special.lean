module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Basic
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Words
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Structure
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Generation
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Center

/-!
# Special structure of the literal Rudvalis max4 core

The eleven fixed words generate the actual core P: their 2048 binary products
are distinguished by their point actions. Their checked squares and commutators
identify both P' and the Frattini subgroup with the original marked eight-group.
The nondegenerate commutator pairing identifies that subgroup with Z(P).
Thus P is special of order 2^11, with center of order 8 and elementary central
quotient of order 256. All generation and center premises are discharged here;
the earlier conditional interfaces are retained for existing consumers.

Source: Aschbacher--Smith I.2.2(7), printed pp.412--413; GLS3 Table 5.3r and
its justification, printed pp.291--292. All embeddings are the original ones.
-/

namespace Rudvalis.CoveringIncidence
open Subgroup SylowOvergroups.RadicalCoverage.LocalCover

public theorem max4Core_commutator_eq_center_of_generation_of_center_eq
    (hgen : closure (Set.range Max4Words.generator) = max4Core)
    (hcenter : max4CoreCenter = elementary 2) :
    _root_.commutator max4Core = center max4Core := by
  apply map_injective max4Core.subtype_injective
  change (_root_.commutator max4Core).map max4Core.subtype = max4CoreCenter
  rw [Max4Special.mapped_derived_eq_marked_of_generation hgen, hcenter]

public theorem max4Core_frattini_eq_center_of_generation_of_center_eq
    (hgen : closure (Set.range Max4Words.generator) = max4Core)
    (hcenter : max4CoreCenter = elementary 2) :
    frattini max4Core = center max4Core := by
  apply map_injective max4Core.subtype_injective
  change (frattini max4Core).map max4Core.subtype = max4CoreCenter
  rw [Max4Special.mapped_frattini_eq_marked_of_generation hgen, hcenter]

public theorem max4CentralQuotient_elementary_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    IsElementaryAbelian 2 (max4Core ⧸ center max4Core) :=
  Max4Special.centralQuotient_elementary_of_generation hgen

/-- The exact eleven words used by the quotient-action calculation generate P. -/
public theorem max4Core_generated_by_words :
    closure (Set.range Max4Words.generator) = max4Core :=
  Max4Special.closure_generators_eq_core

/-- The center, embedded in the ambient Rudvalis model, is the marked eight-group. -/
public theorem max4CoreCenter_eq_marked : max4CoreCenter = elementary 2 :=
  Max4Special.max4CoreCenter_eq_marked_of_generation max4Core_generated_by_words

/-- The same center equality inside the literal ambient image of the core. -/
public theorem max4Core_center_eq_marked :
    center max4Core = (elementary 2).subgroupOf max4Core :=
  Max4Special.center_eq_marked_of_generation max4Core_generated_by_words

public theorem max4Core_commutator_eq_center :
    _root_.commutator max4Core = center max4Core :=
  max4Core_commutator_eq_center_of_generation_of_center_eq
    max4Core_generated_by_words max4CoreCenter_eq_marked

public theorem max4Core_frattini_eq_center :
    frattini max4Core = center max4Core :=
  max4Core_frattini_eq_center_of_generation_of_center_eq
    max4Core_generated_by_words max4CoreCenter_eq_marked

/-- Derived subgroup equality with the original ambient embedding. -/
public theorem max4Core_mapped_commutator_eq_marked :
    (_root_.commutator max4Core).map max4Core.subtype = elementary 2 :=
  Max4Special.mapped_derived_eq_marked_of_generation max4Core_generated_by_words

/-- Frattini subgroup equality with the original ambient embedding. -/
public theorem max4Core_mapped_frattini_eq_marked :
    (frattini max4Core).map max4Core.subtype = elementary 2 :=
  Max4Special.mapped_frattini_eq_marked_of_generation max4Core_generated_by_words

public theorem max4Core_mapped_commutator_eq_center :
    (_root_.commutator max4Core).map max4Core.subtype = max4CoreCenter := by
  rw [max4Core_mapped_commutator_eq_marked, max4CoreCenter_eq_marked]

public theorem max4Core_mapped_frattini_eq_center :
    (frattini max4Core).map max4Core.subtype = max4CoreCenter := by
  rw [max4Core_mapped_frattini_eq_marked, max4CoreCenter_eq_marked]

public instance max4CentralQuotient_elementary :
    IsElementaryAbelian 2 (max4Core ⧸ center max4Core) :=
  max4CentralQuotient_elementary_of_generation max4Core_generated_by_words

public theorem max4Core_center_card : Nat.card (center max4Core) = 8 :=
  (Nat.card_congr (centerEquivMarked max4CoreCenter_eq_marked).toEquiv).trans
    RankOneEightCharacteristic.elementary_two_card

public theorem max4CentralQuotient_card : Nat.card Max4CentralQuotient = 256 :=
  max4CentralQuotient_card_of_center_eq max4CoreCenter_eq_marked

end Rudvalis.CoveringIncidence
