module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.ModuleStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NormalizationTransfer

/-!
# Binary MS93 Section 3 and the local module reduction

At critical distance two, the source dichotomy gives either core = U_alpha
or trivial Frattini subgroup of the core. Elementary structure of U_alpha
and the finite two-group Frattini criterion then give core abelianness.

For b > 2, the natural-structure theorem excludes the doubled and nonsplit
binary alternatives and identifies the actual moving subgroup with one marked
natural module. Its fixed/moving decomposition, the proved full commutation,
and the critical-module calculations construct every field of ModuleFacts.
Together with Geometry.Z_triple_commutator, this expands the source notation
c(Z_alpha) = 1; NaturalU.card gives the moving subgroup order eight.

The re-exported LocalSource.normalizationTransfer proves (4.2)(ii) directly
from the source and b > 2, retaining normality relative to the vertex
stabilizer. No ModuleFacts premise is needed for that transfer. The core in
(3.6) and the radius-two V in (3.9) and (4.2)(ii) remain distinct groups.

Source: MS93 (1993), (3.5)--(3.6), (3.9), (4.1)--(4.2), printed pp.869--872,
879, 881--882. Construction of CommonFacts, including critical escape, remains
with the parent reduction.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Assemble the published output after proving the natural structure and
both critical-pair formulas and the radius-two class bound. -/
def BinaryNaturalStructure.toModuleFacts {source : LocalSource L R}
    (structureData : BinaryNaturalStructure source) (geometry : Geometry R)
    (hb : 2 < geometry.b R)
    (hindex : ∀ a (ha : color R a = false) a',
      CriticalPair R a a' (geometry.exists_critical a ha) →
        (Q R a').relIndex (U R a) = (Q R a).relIndex (U R a'))
    (hcard : ∀ a (ha : color R a = false) a',
      CriticalPair R a a' (geometry.exists_critical a ha) →
        (Q R a').relIndex (Z R a) = 4 →
          Nat.card (⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) = 2)
    (hclass : geometry.b R = 4 → ∀ a, color R a = false →
      ⁅⁅V R a, V R a⁆, V R a⁆ = ⊥) : ModuleFacts source geometry where
  X_eq_Z := structureData.X_eq_Z
  natural := structureData.natural
  full_commutation := geometry.U_full_commutation (by omega) (alpha R) rfl
  decomposition := structureData.decomposition
  disjoint := structureData.disjoint
  critical_U_index := hindex
  critical_Z_commutator_card := hcard
  b_four_class_two := hclass

/-- Binary MS93 (3.6): critical distance two forces the actual commutator
core to be abelian. Both source alternatives are proved from LocalSource. -/
theorem LocalSource.core_commutative_of_b_two
    (source : LocalSource L R) (geometry : Geometry R) (hb : geometry.b R = 2) :
    IsMulCommutative (core R (alpha R)) :=
  source.core_commutative_of_b_two_alternative geometry hb
    (source.core_eq_U_or_frattini_eq_bot_of_b_two geometry hb)

/-- The complete binary module output of Section 3 and (4.1), with all
natural-structure and critical-module premises discharged. The natural action
uses the specified source projection and a single marking of its quotient. -/
theorem LocalSource.moduleFacts
    (source : LocalSource L R) (geometry : Geometry R) (hb : 2 < geometry.b R) :
    Nonempty (ModuleFacts source geometry) := by
  obtain ⟨structureData⟩ := source.binaryNaturalStructure geometry hb
  exact ⟨structureData.toModuleFacts geometry hb
    (structureData.critical_U_index geometry hb)
    (structureData.critical_Z_commutator_card geometry hb)
    (structureData.b_four_class_two geometry)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
