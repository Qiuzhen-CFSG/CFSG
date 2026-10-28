module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.Setup
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.CyclicCore
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.ExceptionalFusion
public import Theory.GroupTheory.CyclicIndexFourActorCentralizer
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Reselecting the whole outer four-group from cyclic-core geometry

An outer involution in the actor either inverts the cyclic core already,
or is one of the exceptional pair. In the second case the marked inner
involution and the exceptional involution generate the entire original
actor. Fusion of the exceptional involution therefore moves that entire
actor back into the supplied Sylow, preserving the marked involution.
In either case the cyclic-index-four centralizer lemma proves abelianness.

The conditional reduction is applied to the actual unitary cyclic core and
its exceptional fusion, proving reselection for every odd prime congruent
to one modulo four. No SQTK, supplement or intersection-cardinality
hypothesis is needed. The separate application leaf passes the literal
conjugate of the whole actor to the existing coordinate consumer.

Source application: Aschbacher--Smith E.1.1--2, E.1.5 and E.1.14(7),
printed pp.209--210,214; A.3.21(b), p.55; Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection
variable {G : Type*} [Group G] [Finite G]

private theorem closure_pair_eq (L A : Subgroup G) [IsElementaryAbelian 2 A]
    (hfour : Nat.card A = 4) {z t : G} (hzA : z ∈ A) (htA : t ∈ A)
    (hz : orderOf z = 2) (hzL : z ∈ L) (htL : t ∉ L) :
    closure ({z, t} : Set G) = A := by
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
  have ht1 : t ≠ 1 := fun h => htL (h ▸ L.one_mem)
  have hzt : Commute z t :=
    congrArg Subtype.val (mul_comm (⟨z, hzA⟩ : A) (⟨t, htA⟩ : A))
  let : IsKleinFour (closure ({z, t} : Set G)) :=
    isKleinFour_closure_pair_of_orderOf z t hz (orderOf_eq_prime ht2 ht1)
      (fun h => htL (h ▸ hzL)) hzt
  apply eq_of_le_of_card_ge
  · apply (closure_le A).mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨hzA, htA⟩
  · rw [hfour, IsKleinFour.card_four]

private theorem select_exceptional {L T : Subgroup G} {z : G}
    (d : CyclicCoreData L T z) (hf : ExceptionalFusion d)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hfour : Nat.card A = 4)
    (hz : orderOf z = 2) (hzA : z ∈ A) (hcA : d.exceptional ∈ A) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ T ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      IsMulCommutative (T ⊓ centralizer
        (A.map (MulAut.conj g).toMonoidHom : Set G) : Subgroup G) := by
  obtain ⟨g, hgz, hgc, hinv⟩ := hf
  let f := (MulAut.conj g).toMonoidHom
  let B := A.map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  let : IsCyclic d.core := d.cyclic
  have hgen := closure_pair_eq L A hfour hzA hcA hz
    (d.core_le_inner d.z_mem) d.exceptional_not_inner
  have hBT : B ≤ T := by
    change A.map f ≤ T
    rw [← hgen, map_le_iff_le_comap, closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_comap]
    refine ⟨?_, hgc⟩
    change MulAut.conj g z ∈ T
    rw [hgz]
    exact d.core_le_sylow d.z_mem
  have hzB : z ∈ B := by
    have h := mem_map_of_mem f hzA
    change MulAut.conj g z ∈ B at h
    rwa [hgz] at h
  have hcard : Nat.card B = 4 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hfour
  exact ⟨g, hBT, hzB,
    four_actor_centralizer_isMulCommutative_of_inverts_cyclic T d.core B
      hBT hcard d.core_relIndex (mem_map_of_mem f hcA) hinv⟩

/-- The full original actor can be reselected once the cyclic-core dichotomy
and exceptional involution fusion have been supplied. -/
theorem exists_abelian_reselection_of_cyclicCoreData
    {L T : Subgroup G} {z : G}
    (d : CyclicCoreData L T z) (hf : ExceptionalFusion d)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ T) (hfour : Nat.card A = 4) (hout : ¬ A ≤ L)
    (hz : orderOf z = 2) (hzA : z ∈ A) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ T ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      IsMulCommutative (T ⊓ centralizer
        (A.map (MulAut.conj g).toMonoidHom : Set G) : Subgroup G) := by
  obtain ⟨t, htA, htL⟩ := SetLike.not_le_iff_exists.mp hout
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
  rcases d.dichotomy t (hAT htA) htL ht2 with ht | ht | hinv
  · exact select_exceptional d hf A hfour hz hzA (ht ▸ htA)
  · have hzz : z * z = 1 := by
      simpa only [pow_two, hz] using pow_orderOf_eq_one z
    have hcA : d.exceptional ∈ A := by
      have hm := A.mul_mem hzA htA
      rwa [ht, ← mul_assoc, hzz, one_mul] at hm
    exact select_exceptional d hf A hfour hz hzA hcA
  · let : IsCyclic d.core := d.cyclic
    have hcomm := four_actor_centralizer_isMulCommutative_of_inverts_cyclic
      T d.core A hAT hfour d.core_relIndex htA hinv
    refine ⟨1, ?_⟩
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    have hmap : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
      rw [hid, map_id]
    rw [hmap]
    exact ⟨hAT, hzA, hcomm⟩

/-- Reselect the whole positioned outer four-group in an odd-prime PSU₃
extension so that its centralizer in the supplied Sylow is abelian. Both
the cyclic-core construction and exceptional fusion are discharged from
the actual unitary model; no assumption on the initial centralizer is made. -/
theorem exists_abelian_reselection_of_isPSU
    [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hfour : Nat.card A = 4)
    (hout : ¬ A ≤ generalizedFitting G)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G) (hzA : z ∈ A)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      IsMulCommutative ((T : Subgroup G) ⊓ centralizer
        (A.map (MulAut.conj g).toMonoidHom : Set G) : Subgroup G) := by
  obtain ⟨d⟩ := nonempty_cyclicCoreData_four_actor hp ho hmod hmodel T A hAT hout
    hz hzL hzA hTz
  exact exists_abelian_reselection_of_cyclicCoreData d
    (exceptionalFusion_of_isPSU hp ho hmod hmodel T hz hzL hTz d)
    A hAT hfour hout hz hzA

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection
