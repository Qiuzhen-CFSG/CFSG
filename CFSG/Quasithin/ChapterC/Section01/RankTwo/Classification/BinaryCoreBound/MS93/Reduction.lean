module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.ModuleFacts
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape

/-!
# The common binary MS93 reduction

The core clauses of (3.1) and (3.6), together with evenness, force b > 2 for
a nonabelian commutator core. Section 3 constructs the actual marked natural
module and its fixed/moving decomposition, and proves the critical-pair
formulas and radius-two class bound. Its normalization transfer then feeds
the common escape argument (4.3), at the second predecessor of every critical
endpoint. These results construct every field of `CommonFacts` from the
literal source and geometry, with no remaining module or escape premise.

The `InputSetup` application transports nonabelianness through the actual
isomorphism between the reduced amalgam core and the original commutator
core. The center conclusions in the two distance branches remain separate.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2), Sections 3 and 4.1--4.3,
printed pp.856--890.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The distance reduction with the b=2 clause explicit. The source application
`LocalSource.large_distance` discharges that clause using Section 3. -/
theorem LocalSource.large_distance_of_two_case (source : LocalSource L R)
    (geometry : Geometry R) (hnonabelian : ¬ IsMulCommutative (core R (alpha R)))
    (htwo : geometry.b R = 2 → IsMulCommutative (core R (alpha R))) :
    2 < geometry.b R := by
  have hzero : geometry.b R ≠ 0 := by
    intro hb
    apply hnonabelian
    rw [source.core_eq_bot_of_b_zero geometry hb]
    infer_instance
  have heven := geometry.even (alpha R) rfl
  change Even (geometry.b R) at heven
  obtain ⟨n, hn⟩ := heven
  by_contra hlarge
  exact hnonabelian (htwo (by omega))

/-- The actual core is trivial at b = 0 and abelian at b = 2, so its
nonabelianness and evenness of the critical distance give source 4.0's b > 2. -/
theorem LocalSource.large_distance (source : LocalSource L R)
    (geometry : Geometry R) (hnonabelian : ¬ IsMulCommutative (core R (alpha R))) :
    2 < geometry.b R :=
  source.large_distance_of_two_case geometry hnonabelian
    (source.core_commutative_of_b_two geometry)

/-- Binary MS93 (4.3) from the source data: the actual radius-two subgroup
escapes the kernel two steps before every critical endpoint. Section 3
supplies all module and normalization-transfer inputs. -/
theorem LocalSource.criticalEscape (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) : CriticalEscape R geometry := by
  obtain ⟨modules⟩ := source.moduleFacts geometry hb
  exact Escape.criticalEscape source geometry hb modules
    (source.normalizationTransfer geometry hb)

/-- All common source consequences under the distance hypothesis of 4.0.
The natural model uses the source projection and one consistent marking;
the centralizer, relative normality and critical-pair clauses retain the
literal amalgam subgroups. -/
theorem LocalSource.commonFacts_of_large_distance (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) :
    Nonempty (CommonFacts R source geometry) := by
  obtain ⟨modules⟩ := source.moduleFacts geometry hb
  have transfer := source.normalizationTransfer geometry hb
  exact ⟨{
    large_distance := hb
    centralizer := source.adjacent_centralizer geometry.radical_ne_bot
    X_eq_Z := modules.X_eq_Z
    natural := modules.natural
    full_commutation := modules.full_commutation
    decomposition := modules.decomposition
    disjoint := modules.disjoint
    normalization_transfer := transfer
    X_bound := source.X_le_Q_of_dist_lt geometry
    critical_noncommutation := fun a ha _ hc => source.critical_noncommutation geometry a ha hc
    critical_reverse := source.critical_reverse geometry
    escape := Escape.criticalEscape source geometry hb modules transfer
  }⟩

/-- The complete common reduction for a nonabelian binary MS93 core.
Both small distances and every extra premise of the common escape theorem
are discharged here. -/
theorem LocalSource.commonFacts (source : LocalSource L R)
    (geometry : Geometry R) (hnonabelian : ¬ IsMulCommutative (core R (alpha R))) :
    Nonempty (CommonFacts R source geometry) :=
  source.commonFacts_of_large_distance geometry (source.large_distance geometry hnonabelian)

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {K T : Subgroup J}

/-- Apply the common reduction to the actual characteristic replacement of
an original binary MS input. The core isomorphism transfers the original
nonabelianness; no odd-index condition on the replacement is needed. -/
theorem InputSetup.commonFacts {h : Input κ K T} (s : InputSetup h)
    (hD : ¬ IsMulCommutative (commutatorCore K)) :
    Nonempty (CommonFacts s.reduction.radical s.source s.geometry) := by
  apply s.source.commonFacts s.geometry
  intro hc
  apply hD
  apply isMulCommutative_iff.mpr
  intro x y
  apply s.coreEquiv.symm.injective
  simpa only [map_mul] using
    isMulCommutative_iff.mp hc (s.coreEquiv.symm x) (s.coreEquiv.symm y)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
