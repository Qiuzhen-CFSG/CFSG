module

public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.FieldEmbeddings
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank.CubicWitness
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.QuasithinBasic

/-!
# Three-rank in derived symplectic and G₂ groups in characteristic two

Binary witnesses suffice over every larger characteristic-two field. The
faithful six-letter polar representation identifies Sp₄(2)′ with A₆, whose
two disjoint three-cycles give rank two. The explicit nonabelian three-subgroup
of G₂(2)′ rules out cyclic Sylow three-subgroups, hence rules out rank one.

The coefficient embeddings restrict injectively to the actual commutator
subgroups, so both inequalities transfer without identifying either derived
group with its ambient group. No perfection assumption is used.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 13.8.20(a), printed p.954 (PDF p.971), the elimination of Sp₄ and G₂
from the higher-field list when the three-rank is one. Attribution for the
concrete octonion witnesses and symplectic polar representation is retained
in their imported modules.
-/

namespace Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
open Theory.GroupTheory
open scoped IsMulCommutative

private noncomputable def derivedMap {G H : Type*} [Group G] [Group H] (f : G →* H) :
    commutator G →* commutator H :=
  (f.comp (commutator G).subtype).codRestrict (commutator H) (by
    have hc : (commutator G).map f ≤ commutator H := by
      rw [map_commutator_eq]
      exact Subgroup.commutator_mono le_top le_top
    intro x
    exact hc ⟨x, x.property, rfl⟩)

private theorem derivedMap_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) : Function.Injective (derivedMap f) := by
  intro x y h
  exact Subtype.ext (hf (congrArg Subtype.val h))

private noncomputable def binaryDerivedEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

/-- Two independent binary three-cycles give rank two in the actual derived
symplectic group over every finite characteristic-two field. -/
public theorem symplectic {F : Type*} [Field F] [Finite F] [CharP F 2] :
    2 ≤ primeRank 3 (commutator (Matrix.symplecticGroup (Fin 2) F)) := by
  have hb : 2 ≤ primeRank 3 (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) := by
    rw [primeRank_equiv 3 binaryDerivedEquiv]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by norm_num)
  exact hb.trans (primeRank_le_of_injective 3
    (derivedMap (FieldEmbeddings.symplectic (ZMod.castHom (dvd_refl 2) F)))
    (derivedMap_injective _ (FieldEmbeddings.symplectic_injective _)))

private theorem binary_g2_rank : 2 ≤ primeRank 3 (commutator (Atlas.G2.Model (ZMod 2))) := by
  by_contra! h
  have hr : primeRank 3 (commutator (Atlas.G2.Model (ZMod 2))) ≤ 1 := by omega
  obtain ⟨P, hP, x, y, _, hxy⟩ := Atlas.G2.BinaryThreeRank.exists_noncentral_cubic_three_subgroup
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  let := S.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  have he : (Subgroup.inclusion hS x) * (Subgroup.inclusion hS y) =
      (Subgroup.inclusion hS y) * (Subgroup.inclusion hS x) := mul_comm _ _
  exact hxy (Subgroup.inclusion_injective hS (by simpa only [map_mul] using he))

/-- The nonabelian binary three-subgroup embeds in the actual derived G₂
carrier over every finite characteristic-two field, forcing three-rank at least two. -/
public theorem g2 {F : Type*} [Field F] [Finite F] [CharP F 2] :
    2 ≤ primeRank 3 (commutator (Atlas.G2.Model F)) :=
  binary_g2_rank.trans (primeRank_le_of_injective 3
    (derivedMap (FieldEmbeddings.g2 (ZMod.castHom (dvd_refl 2) F)))
    (derivedMap_injective _ (FieldEmbeddings.g2_injective _)))

end Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
