module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.SylowOrbit
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.SolvableBlockCentralization
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.Factors
public import Theory.GroupTheory.Commutator.PerfectSolvableCover
/-!
# The χ₀ type of a component generating a C.1.29 overgroup

If all factors in the literal block decomposition were solvable A₃ blocks,
C.1.9 makes their join centralize the perfect generating component. The ordered
factorization would then put that component inside M, a contradiction. A
nonsolvable factor is a C-component, and the proved A.3.8 orbit exhaustion
identifies it with a Sylow conjugate of the original generating component.

Only the genuine C.1.9 block-commutation input remains explicit. The selected
factor's module and actual quotient transport with the conjugation isomorphism.

Source: Aschbacher–Smith, C.1.29 and Lemma 2.4.6, printed pp.134 and 528.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
open ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
open ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass} {M S H : Subgroup G}

private theorem centralizes_three_factor
    (hc : BlockCommutationInput G) (hsq : IsSQTK κ H)
    (hf : generalizedFitting H = pCore 2 H)
    {K B : Subgroup H} (hK : K.IsCComponent) (hB : ChapterC.IsBlock B)
    (hthree : ChapterC.IsAlternatingBlock B 3) : K ≤ centralizer (B : Set H) := by
  let : Group.IsPerfect K := hK.perfect
  have h19 : C19Condition H := by
    apply twoThreeCore_generalizedFitting
    show centralizer (pCore 2 H : Set H) ≤ pCore 2 H
    simpa only [hf] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := H))
  apply perfect_centralizes_normalized_three_block hthree
  exact perfect_normalizes_of_commuting_three_conjugates B K hB.short
    (exists_order_three (Or.inr (Or.inl hthree)))
    (hsq.stronglyQuasithin 3 Nat.prime_three (by decide))
    (fun g h hne => hc H (fun _ => h19) _ _
      (hB.map_equiv (MulAut.conj g)) (hB.map_equiv (MulAut.conj h)) hne)

private theorem exists_non_three_factor
    (d : BlockDecomposition M S H) (hc : BlockCommutationInput G)
    (hsq : IsSQTK κ H) (hf : generalizedFitting H = pCore 2 H)
    {K : Subgroup H} (hK : K.IsCComponent) (hout : ¬ K ≤ M.subgroupOf H) :
    ∃ i, ¬ ChapterC.IsAlternatingBlock (d.block i) 3 := by
  classical
  by_contra! hall
  let D := iSup d.block
  have hDK : D ≤ centralizer (K : Set H) := iSup_le fun i =>
    le_centralizer_iff.mp (centralizes_three_factor hc hsq hf hK (d.allowed i).1 (hall i))
  have hDrad : D ≤ solvableRadical H := by
    apply iSup_le
    intro i
    let : Group.IsSolvable (d.block i) := three_solvable (hall i)
    have hh := map_solvableRadical_subtype_le_of_isSubnormal (d.allowed i).1.subnormal
    have ht : solvableRadical (d.block i) = ⊤ :=
      top_unique (le_solvableRadical ⊤ inferInstance inferInstance)
    rw [ht, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective (inclusion_injective hDrad)
  let : Group.IsPerfect K := hK.perfect
  apply hout
  apply perfect_le_of_commuting_solvable_cover K (M.subgroupOf H) D hDK
  intro k _
  obtain ⟨m,b,he⟩ := d.factorization k
  refine ⟨m,m.property,(List.ofFn fun i => (b i : H)).prod,?_,he.symm⟩
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact (le_iSup d.block i) (b i).property

/-- C.1.29 recognizes the generating component itself as a χ₀ block. -/
theorem BlockDecomposition.chiZero_of_cComponent_generated
    (d : BlockDecomposition M S H) (hc : BlockCommutationInput G)
    (hsq : IsSQTK κ H) (hf : generalizedFitting H = pCore 2 H)
    (P : Sylow 2 H) {K : Subgroup H} (hK : K.IsCComponent)
    (hgen : K ⊔ P = ⊤) (hout : ¬ K ≤ M.subgroupOf H) :
    ChapterC.IsChiZeroBlock K := by
  obtain ⟨i,hi⟩ := exists_non_three_factor d hc hsq hf hK hout
  have hBi : (d.block i).IsCComponent := by
    let : IsQuasisimple ((d.block i) ⧸ pCore 2 (d.block i)) :=
      quotient_quasisimple_of_not_three (d.allowed i).2 hi
    exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (d.allowed i).1.subnormal (d.allowed i).1.short.twoPerfect
  have h38 : SylowOrbitSource κ := by
    intro X _ _ hs ho Q C hC hg D hD
    exact ChapterA.Section03.SourceComponents.sylow_orbit_of_generated hs ho Q hC hg hD
  obtain ⟨s,he⟩ := cComponent_conjugate_of_generated h38 hsq P hK hgen hBi
  let e : K ≃* d.block i := ((MulAut.conj (s : H)).subgroupMap K).trans
    (MulEquiv.subgroupCongr he.symm)
  exact chiZero_of_mulEquiv (d.allowed i).2 e.symm
end CFSG.Quasithin.Chapter2.ComponentRefinement
