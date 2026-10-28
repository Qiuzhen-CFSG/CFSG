module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source.Sylow
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.SelectedCoordinates
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.SelectedPermutation

/-!
# Full solvable Thompson factorization B.2.16

For a finite solvable group with F*(G)=O₂(G), the actual normal closure
V=⟨Ω₁Z(T)^G⟩ belongs to R₂(G). If J(T) centralizes V, the Frattini
argument gives the prescribed normalizer-centralizer product. Otherwise
B.1.8 on the faithful star action and the genuine stable maximum-elementary
image family give a selected product of natural PSL₂(2) factors.

The selected group and linear equivalences agree with every original
inclusion. The fixed complement and conjugation permutation are built
on the same selected indices, and the original J(T) image is Sylow in
the original J(G) image. Both final rank assertions are derived from
B.2.4 and the proved absence of strong solvable offenders.

This inhabits the unchanged universal `TheoremB216` source contract;
no exceptional witness, selected-factor or action premise remains.
Source: Aschbacher--Smith B.2.16, printed p.79.
-/

public section
open scoped IsMulCommutative
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_exceptional (hs : Group.IsSolvable G)
    (hf : generalizedFitting G = pCore 2 G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 (closure T)]
    (hn : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (closure T : Set G)) :
    Nonempty (Exceptional T) := by
  classical
  let := hs
  let V := closure T
  let q := starMap V
  let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  let P := ChapterB.maxOffenderImages (⊤ : Subgroup G) V q
  have hr := (closure_elementary_reduced hs hf T).2
  obtain ⟨d,_,_,_,hgen⟩ := ChapterB.thompson_factors_of_solvable_action V q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) T hn inferInstance hr
  let I := d.toSolvableFFFactors.stableFactorSet P
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let f : Fin n → Fin d.count := fun i => (e i).val
  have hfinj : Function.Injective f := Subtype.val_injective.comp e.injective
  let L := (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q
  have hI : (⨆ i ∈ I, d.factor i) = L := hgen.symm
  have hF : (⨆ i, d.factor (f i)) = L := by
    rw [← hI,iSup_subtype']
    apply le_antisymm
    · exact iSup_le fun i => le_iSup (fun i : I => d.factor i) (e i)
    · apply iSup_le
      intro i
      obtain ⟨j,rfl⟩ := e.surjective i
      exact le_iSup (fun i => d.factor (f i)) j
  let : (elementaryAbelianMaxJ (⊤ : Subgroup G)).Characteristic :=
    elementaryAbelianMaxJ_top_characteristic
  have hnI : (⨆ i ∈ I, d.factor i : Subgroup (CentralQuotient V)).Normal := by
    rw [hI]
    exact Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let eg := (d.toSolvableFFFactors.selectedGroupProduct f hfinj).trans
    (MulEquiv.subgroupCongr hF)
  let ef : fixedSpace ρ L ≃ₗ[ZMod 2] fixedSpace ρ (⨆ i, d.factor (f i)) :=
    LinearEquiv.ofEq _ _ (congrArg (fixedSpace ρ) hF.symm)
  let em := (ef.prodCongr (LinearEquiv.refl (ZMod 2) _)).trans
    (d.toSolvableFFFactors.selectedModuleSum f hfinj)
  refine ⟨{
    noncentral := hn
    sylow := source_thompson_sylow hs hf T hn
    representation := ρ
    conjugation := ?_
    count := n
    factor := fun i => d.factor (f i)
    groupProduct := eg
    groupProduct_single := ?_
    factorModel := fun i => d.toSolvableFFFactors.factorProjectiveModel (f i)
    moduleSum := em
    moduleSum_fixed := ?_
    moduleSum_single := ?_
    naturalEquiv := fun i => d.naturalEquiv (f i)
    naturalEquiv_action := ?_
    permutes := ?_ }⟩
  · intro g v
    exact NormalElementaryQuotient.representation_apply V q _ _ g (Additive.ofMul v)
  · intro i g
    exact d.toSolvableFFFactors.selectedGroupProduct_single f hfinj i g
  · intro v
    change d.toSolvableFFFactors.selectedModuleSum f hfinj (ef v,0) = v
    rw [d.toSolvableFFFactors.selectedModuleSum_fixed]
    rfl
  · intro i v
    change d.toSolvableFFFactors.selectedModuleSum f hfinj (ef 0,Pi.single i v) = v
    rw [map_zero,d.toSolvableFFFactors.selectedModuleSum_single]
  · intro i g v
    simpa only [ChapterB.SolvableFFFactors.factorProjectiveModel, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] using d.naturalEquiv_action (f i) g v
  · intro g
    let σ : Equiv.Perm (Fin n) := (e.trans
      (d.toSolvableFFFactors.selectedPermutation I hnI g)).trans e.symm
    have hσ (i : Fin n) : f (σ i) = d.toSolvableFFFactors.factorConjugation g (f i) := by
      exact (congrArg Subtype.val (e.apply_symm_apply
        (d.toSolvableFFFactors.selectedPermutation I hnI g (e i)))).trans
          (d.toSolvableFFFactors.selectedPermutation_apply I hnI g (e i))
    refine ⟨σ,?_,?_⟩
    · intro i
      rw [hσ]
      exact d.toSolvableFFFactors.factor_map_conj g (f i)
    · intro i
      rw [hσ]
      exact d.toSolvableFFFactors.support_map_conj g (f i)

theorem source_conclusion (hs : Group.IsSolvable G)
    (hf : generalizedFitting G = pCore 2 G) (T : Sylow 2 G) : Conclusion T := by
  obtain ⟨he,hr⟩ := closure_elementary_reduced hs hf T
  obtain ⟨hR,hJ⟩ := source_rank_assertions hs hf T
  refine ⟨he,hr,?_,hR,hJ⟩
  let := he
  by_cases hn : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (closure T : Set G)
  · exact Or.inl ⟨hn,factorization_of_central_thompson T hn⟩
  · exact Or.inr (source_exceptional hs hf T hn)

theorem source_theoremB216 : TheoremB216.{u} := by
  intro G _ _ hs hf T
  exact source_conclusion hs hf T
end CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource
