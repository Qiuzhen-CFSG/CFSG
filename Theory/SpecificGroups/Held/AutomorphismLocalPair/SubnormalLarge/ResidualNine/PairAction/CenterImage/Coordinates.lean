module
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.PairAction.WordOrder

/-!
# A concrete central sixteen-set in the pure Held word core

The four words q₀, q₁, q₂q₃ and q₄q₅ commute with the eight residual
 generators. Their sixteen binary products are distinguished by the existing
word decoder. The centrality certificates use the unchanged, previously
certified degree-2058 permutation tables; all checks are kernel reductions.

Sources: the literal ATLAS pair (false,0), GLS3 Table 5.3p, and the model
calculation used in Aschbacher--Smith 15.3.41–42 (printed p.1138).

Extracted from `CFSG/Quasithin/Chapter15/Section03/ComponentUniqueness/RankTwo/NonCharacteristicTwo/SporadicSieve/HeldExclusion/ProperExtensionProfile/Quotients/PureInnerCore/CenterImage/Coordinates.lean`, preserving the literal words,
permutation tables and conjugation convention. Original ATLAS attribution and
license remain in `Theory/SpecificGroups/Held/Model/Source`.

-/

set_option Elab.async false
@[expose] public section
open Subgroup
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry
open Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
open ResidualRoots.Pair00
namespace Held.AutomorphismLocalPair.ResidualNine.PairActionCertificate.CenterImageCertificate
open PureCoreCount
attribute [local irreducible] ResidualRoots.generator ResidualRoots.pairGenerator

def basisWord : Fin 4 → List (Fin 8) := ![[0], [1], [2,3], [4,5]]
def basis (k : Fin 4) : pureWordCore :=
  ⟨⟨ResidualRoots.product false 0 (basisWord k),
    pureWordGroup_le (ResidualRoots.product_mem_group false 0 _)⟩,
    ResidualRoots.product_mem_group false 0 _⟩
def basisTable (k : Fin 4) : Equiv.Perm (Fin 2058) := ![q0, q1, q2*q3, q4*q5] k

theorem basisTable_eq (k : Fin 4) : basisTable k =
    Held.representation ((basis k : pairGroup) : Held.He) := by
  fin_cases k <;>
    simp [basisTable, basis, basisWord, ResidualRoots.product, map_mul,
      ← q0_eq, ← q1_eq, ← q2_eq, ← q3_eq, ← q4_eq, ← q5_eq]

private theorem comm_0_0 :
    generatorTable 0 * basisTable 0 = basisTable 0 * generatorTable 0 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_0_1 :
    generatorTable 1 * basisTable 0 = basisTable 0 * generatorTable 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_0_2 :
    generatorTable 2 * basisTable 0 = basisTable 0 * generatorTable 2 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_0_3 :
    generatorTable 3 * basisTable 0 = basisTable 0 * generatorTable 3 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_0_4 :
    generatorTable 4 * basisTable 0 = basisTable 0 * generatorTable 4 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_0_5 :
    generatorTable 5 * basisTable 0 = basisTable 0 * generatorTable 5 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_0_6 :
    generatorTable 6 * basisTable 0 = basisTable 0 * generatorTable 6 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_0_7 :
    generatorTable 7 * basisTable 0 = basisTable 0 * generatorTable 7 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_1_0 :
    generatorTable 0 * basisTable 1 = basisTable 1 * generatorTable 0 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_1_1 :
    generatorTable 1 * basisTable 1 = basisTable 1 * generatorTable 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_1_2 :
    generatorTable 2 * basisTable 1 = basisTable 1 * generatorTable 2 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_1_3 :
    generatorTable 3 * basisTable 1 = basisTable 1 * generatorTable 3 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_1_4 :
    generatorTable 4 * basisTable 1 = basisTable 1 * generatorTable 4 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_1_5 :
    generatorTable 5 * basisTable 1 = basisTable 1 * generatorTable 5 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_1_6 :
    generatorTable 6 * basisTable 1 = basisTable 1 * generatorTable 6 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_1_7 :
    generatorTable 7 * basisTable 1 = basisTable 1 * generatorTable 7 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_2_0 :
    generatorTable 0 * basisTable 2 = basisTable 2 * generatorTable 0 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_2_1 :
    generatorTable 1 * basisTable 2 = basisTable 2 * generatorTable 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_2_2 :
    generatorTable 2 * basisTable 2 = basisTable 2 * generatorTable 2 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_2_3 :
    generatorTable 3 * basisTable 2 = basisTable 2 * generatorTable 3 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_2_4 :
    generatorTable 4 * basisTable 2 = basisTable 2 * generatorTable 4 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_2_5 :
    generatorTable 5 * basisTable 2 = basisTable 2 * generatorTable 5 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_2_6 :
    generatorTable 6 * basisTable 2 = basisTable 2 * generatorTable 6 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_2_7 :
    generatorTable 7 * basisTable 2 = basisTable 2 * generatorTable 7 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_3_0 :
    generatorTable 0 * basisTable 3 = basisTable 3 * generatorTable 0 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_3_1 :
    generatorTable 1 * basisTable 3 = basisTable 3 * generatorTable 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_3_2 :
    generatorTable 2 * basisTable 3 = basisTable 3 * generatorTable 2 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_3_3 :
    generatorTable 3 * basisTable 3 = basisTable 3 * generatorTable 3 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_3_4 :
    generatorTable 4 * basisTable 3 = basisTable 3 * generatorTable 4 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_3_5 :
    generatorTable 5 * basisTable 3 = basisTable 3 * generatorTable 5 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_3_6 :
    generatorTable 6 * basisTable 3 = basisTable 3 * generatorTable 6 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem comm_3_7 :
    generatorTable 7 * basisTable 3 = basisTable 3 * generatorTable 7 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

theorem basisTable_comm (k : Fin 4) (j : Fin 8) :
    generatorTable j * basisTable k = basisTable k * generatorTable j := by
  fin_cases k <;> fin_cases j
  · exact comm_0_0
  · exact comm_0_1
  · exact comm_0_2
  · exact comm_0_3
  · exact comm_0_4
  · exact comm_0_5
  · exact comm_0_6
  · exact comm_0_7
  · exact comm_1_0
  · exact comm_1_1
  · exact comm_1_2
  · exact comm_1_3
  · exact comm_1_4
  · exact comm_1_5
  · exact comm_1_6
  · exact comm_1_7
  · exact comm_2_0
  · exact comm_2_1
  · exact comm_2_2
  · exact comm_2_3
  · exact comm_2_4
  · exact comm_2_5
  · exact comm_2_6
  · exact comm_2_7
  · exact comm_3_0
  · exact comm_3_1
  · exact comm_3_2
  · exact comm_3_3
  · exact comm_3_4
  · exact comm_3_5
  · exact comm_3_6
  · exact comm_3_7

theorem basis_central (k : Fin 4) : basis k ∈ center pureWordCore := by
  have hc : ((basis k : pairGroup) : Held.He) ∈
      centralizer (Set.range (ResidualRoots.generator false 0)) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨j, rfl⟩
    apply Held.representation_injective
    simpa only [map_mul, ← basisTable_eq, ← generatorTable_eq] using basisTable_comm k j
  rw [← centralizer_closure] at hc
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact mem_centralizer_iff.mp hc _ x.property

def centralBasis (k : Fin 4) : center pureWordCore := ⟨basis k, basis_central k⟩

def centralWord (v : Fin 16) : center pureWordCore :=
  (List.ofFn (fun k : Fin 4 => centralBasis k ^ (v.val / 2 ^ k.val % 2))).prod

def centralTable (v : Fin 16) : Equiv.Perm (Fin 2058) :=
  (List.ofFn (fun k : Fin 4 => basisTable k ^ (v.val / 2 ^ k.val % 2))).prod

def centerRepresentation : center pureWordCore →* Equiv.Perm (Fin 2058) :=
  Held.representation.comp ((pairGroup).subtype.comp
    (pureWordCore.subtype.comp (center pureWordCore).subtype))

theorem centralTable_eq (v : Fin 16) :
    centralTable v = centerRepresentation (centralWord v) := by
  simp only [centralTable, centralWord, map_list_prod, List.map_ofFn,
    Function.comp_def, map_pow]
  congr 2
  funext k
  rw [basisTable_eq]
  rfl

def coordinateIndex : Fin 16 → Fin 256 :=
  ![0,1,2,3,12,13,14,15,48,49,50,51,60,61,62,63]

private theorem decode_central : ∀ v : Fin 16,
    decode (centralTable v) = (coordinateIndex v).val := by
  decide +kernel

private theorem coordinateIndex_injective : Function.Injective coordinateIndex := by
  decide +kernel

theorem centralWord_injective : Function.Injective centralWord := by
  intro v w h
  apply coordinateIndex_injective
  apply Fin.ext
  rw [← decode_central v, ← decode_central w, centralTable_eq, centralTable_eq, h]

end Held.AutomorphismLocalPair.ResidualNine.PairActionCertificate.CenterImageCertificate
