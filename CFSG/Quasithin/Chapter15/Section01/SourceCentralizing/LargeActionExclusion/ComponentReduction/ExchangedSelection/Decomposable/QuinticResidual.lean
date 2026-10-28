module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.ResidualGeometry
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.QuinticResidual

/-!
# The quintic marked-centralizer residual

The full marked-centralizer residual fixes the first original support.
Restriction to the opposite support is therefore faithful, and embeds
it in that support's cyclic residual of order dividing fifteen. The
original opposite five-kernel already lies in the residual, leaving
exactly the orders five and fifteen. Transport through the original
action proves the same alternatives in C_M(Z₁)/C_M(V).

The actual eight-dimensional consumer in the parent Decomposable module
combines this with the prime-three calculation and retains both original
sixteen-element supports. The order-fifteen alternative must still be
excluded using the ambient source hypotheses before constructing the
prime-five marker. This module does not supply that exclusion.

Source: Aschbacher--Smith 15.1.16(a)--18, printed pp.1092--1093,
with the linear overgroup calculation on pp.1087--1088.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- Restriction to the opposite support identifies a cyclic residual of order five or fifteen. -/
theorem ThompsonPair.full_image_residual_of_prime_five
    {T : Sylow 2 G}
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5) :
    let ρ := imageRepresentation M V hn
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let K := subspaceKernel ρ W ⊤
    IsCyclic (pResidual 2 K) ∧
      (Nat.card (pResidual 2 K) = 5 ∨ Nat.card (pResidual 2 K) = 15) := by
  intro ρ W K
  let D := internalActionImage M V hn
  let F := c.ambientFactor d s.first
  let B := c.ambientFactor d s.second
  let R := (pResidual 2 K).map K.subtype
  let P := (s.marking s.second).kernel.map B.embedding.groupMap
  have hfix : F.space ≤ fixedSpace ρ R :=
    s.full_residual_fixes_first hTM hn c d π hp hs hJ
  have hKP : K ≤ normalizer (P : Set D) :=
    (s.full_image_residual hTM hn c d hJ).2.1
  have hKB : K ≤ subspaceStabilizer ρ B.space := by
    rw [←s.kernel_moved s.second]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hKP
  have hcompl : IsCompl F.space B.space := by
    have hodd : Odd (Nat.card P) := by rw [s.kernel_card,hfive]; decide
    rw [←s.kernel_fixed s.second s.first s.distinct.symm,←s.kernel_moved s.second]
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd)
  let q := (subgroupActionHom ρ B.space K hKB).comp (pResidual 2 K).subtype
  have hq : Function.Injective q := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    apply imageRepresentation_injective M V hn
    have hA : F.space ≤ LinearMap.eqLocus (ρ (x : K)) (ρ (y : K)) := by
      intro w hw
      exact (hfix hw ⟨x,mem_map_of_mem K.subtype x.property⟩).trans
        (hfix hw ⟨y,mem_map_of_mem K.subtype y.property⟩).symm
    have hB : B.space ≤ LinearMap.eqLocus (ρ (x : K)) (ρ (y : K)) := by
      intro w hw
      exact congrArg (fun a => (subspaceImageRepresentation ρ B.space a ⟨w,hw⟩ : Additive V)) he
    have hall : (⊤ : Submodule (ZMod 2) (Additive V)) ≤
        LinearMap.eqLocus (ρ (x : K)) (ρ (y : K)) :=
      hcompl.sup_eq_top ▸ sup_le hA hB
    apply LinearMap.ext
    intro w
    exact hall (Submodule.mem_top)
  have hm := s.dihedral s.second
  rw [hfive] at hm
  obtain ⟨hdiv,hcyc⟩ := B.support_residual_of_five
    (c.support_stabilizer_normalizes_actor d π hp hs s.second) (s.marking s.second) hm
  let Q := pResidual 2 (subspaceActionImage ρ B.space)
  let f : pResidual 2 K →* Q := q.codRestrict Q (by
    intro x
    exact map_pResidual_le 2 (subgroupActionHom ρ B.space K hKB)
      (mem_map_of_mem _ x.property))
  have hf : Function.Injective f := fun x y he => hq (congrArg Subtype.val he)
  let : IsCyclic Q := hcyc
  refine ⟨isCyclic_of_injective f hf,?_⟩
  have hd : Nat.card (pResidual 2 K) ∣ 15 := (card_dvd_of_injective f hf).trans hdiv
  have hlo : 5 ∣ Nat.card (pResidual 2 K) :=
    hfive ▸ (s.full_image_residual hTM hn c d hJ).2.2.2
  have hh := Nat.mem_divisors.mpr ⟨hd,(by decide : 15 ≠ 0)⟩
  rw [show Nat.divisors 15 = {1,3,5,15} by decide] at hh
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with hh | hh | hh | hh
  · rw [hh] at hlo
    norm_num at hlo
  · rw [hh] at hlo
    norm_num at hlo
  · exact Or.inl hh
  · exact Or.inr hh

/-- Descend cyclicity and the order alternatives through the literal module centralizer. -/
theorem ThompsonPair.full_quotient_residual_of_prime_five
    {T : Sylow 2 G}
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    letI := caseI_module_centralizer_normal (Z1 := Z) hn
    let Q := pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)
    IsCyclic Q ∧ (Nat.card Q = 5 ∨ Nat.card Q = 15) := by
  let ρ := imageRepresentation M V hn
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)
  let K := subspaceKernel ρ W ⊤
  let qdata (A : Subgroup G) : Prop :=
    let C := M ⊓ centralizer (A : Set G)
    letI := caseI_module_centralizer_normal (Z1 := A) hn
    let Q := pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)
    IsCyclic Q ∧ (Nat.card Q = 5 ∨ Nat.card Q = 15)
  have hW : plane V W = thompsonPlane T V (c.ambientFactor d s.first).space :=
    plane_thompson_intersection hTM hn _
  have hh : qdata (plane V W) := by
    let C := M ⊓ centralizer (plane V W : Set G)
    let := caseI_module_centralizer_normal (Z1 := (binarySubgroup W).map V.subtype) hn
    obtain ⟨q,hq,hker,_⟩ := ExtraspecialMarker.stabilizer_projection M V hn W
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    have he := map_pResidual_of_surjective 2 e.toMonoidHom e.surjective
    let er := ((pResidual 2 _).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr he)
    obtain ⟨hcyc,hcard⟩ := s.full_image_residual_of_prime_five hTM hn c d π hp hs hJ hfive
    refine ⟨er.isCyclic.mpr hcyc,?_⟩
    exact hcard.elim (fun hc => Or.inl ((Nat.card_congr er.toEquiv).trans hc))
      (fun hc => Or.inr ((Nat.card_congr er.toEquiv).trans hc))
  change qdata (thompsonPlane T V (c.ambientFactor d s.first).space)
  rwa [hW] at hh

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
