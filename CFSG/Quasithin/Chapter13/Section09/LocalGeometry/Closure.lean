module
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Axes
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.CoreQuotient

/-!
# The source marked four-group and the centralizer consumers

The native normal four-group ⟨t,z⟩ transports to every matching original
PairData. This discharges all ClosureData fields, then applies the actual
Q-normality and C_G(z)-solvability theorems using only the preceding PairData
and condition (E). No separate closure or coordinate premise remains.

Source: Aschbacher–Smith 13.9.7–8, printed pp.971–972 (PDF pp.988–989).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath CentralizerStructure
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)
variable (p : PairData d) (hz : p.z=m.z) (ht : p.t=m.t)

omit [Finite G] in
include hz ht in
private theorem markedFour_image :
    (zpowers SymmetricFourWreath.t⊔zpowers SymmetricFourWreath.z : Subgroup W).map m.embedding=p.V := by
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
  change zpowers m.t⊔zpowers m.z=zpowers p.t⊔zpowers p.z
  rw [ht,hz]

omit [Finite G] in
include hz ht in
theorem closureData : p.ClosureData where
  elementary := by
    rw [←m.markedFour_image p hz ht]
    let := marked_four_elementary
    exact IsElementaryAbelian.map _
  card_four := by
    rw [←m.markedFour_image p hz ht,card_map_of_injective m.embedding_injective,card_marked_four]
  normalized := by
    rw [←m.markedFour_image p hz ht,←m.image_standardSylow]
    exact (map_mono standardSylow_normalizes_marked_four).trans ((zpowers SymmetricFourWreath.t⊔zpowers SymmetricFourWreath.z : Subgroup W).le_normalizer_map m.embedding)

include hz ht in
theorem core_normal_of_pair (hE : IsEvenCharacteristicAt d.T) : (m.core.subgroupOf p.C).Normal :=
  m.core_normal p hz ht (m.closureData p hz ht) hE

include hz ht in
theorem centralizer_z_solvable_of_pair (hE : IsEvenCharacteristicAt d.T) : Group.IsSolvable p.C :=
  m.centralizer_z_solvable p hz ht (m.closureData p hz ht) hE
end CFSG.Quasithin.Chapter13.Section09.Marking
