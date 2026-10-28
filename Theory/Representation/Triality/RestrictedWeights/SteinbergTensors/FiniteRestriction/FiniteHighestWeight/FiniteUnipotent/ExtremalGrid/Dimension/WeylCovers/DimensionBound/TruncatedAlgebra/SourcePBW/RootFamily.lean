module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.SourcePBW.FilteredWords
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.SourcePBW.Blocks
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs

/-!
# Truncated PBW spanning for a closed family of D4 roots

The actual higher-coefficient exchange relation has one reordered term;
every other term has smaller total coefficient degree. Root-sum closure
keeps its three coefficients in the same family. Degree induction and the
one-root binary carry law therefore span its algebra by one truncated
coefficient from each root, in the specified order.

Source: Steinberg (1963), section 2; the parameter relations retain the
actual arbitrary nonzero scaling constants supplied by the geometry.
-/

open Theory.AlgebraicGroup CoefficientPBW
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.SourcePBW
@[expose] public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

lemma rootFamily_commutator_lower (S : Geometry K) (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    {m q : ℕ} (r : Fin m → S.roots.Root)
    (hop : ∀i j,r j ≠ S.roots.neg (r i))
    (hclosed : ∀i j c,RootSum S (r i) (r j) c → ∃l,r l=c)
    (a b : Fin m × Fin q) :
    rootCoefficient S rho hr (r a.1) a.2 * rootCoefficient S rho hr (r b.1) b.2 -
      rootCoefficient S rho hr (r b.1) b.2 * rootCoefficient S rho hr (r a.1) a.2 ∈
      lowerWords (k:=k) (fun p:Fin m × Fin q=>rootCoefficient S rho hr (r p.1) p.2)
        (fun p=>p.2.val) (a.2.val+b.2.val) := by
  let U := lowerWords (k:=k) (fun p:Fin m × Fin q=>rootCoefficient S rho hr (r p.1) p.2)
    (fun p=>p.2.val) (a.2.val+b.2.val)
  by_cases he : r a.1=r b.1
  · have hh : Commute (rootCoefficient S rho hr (r a.1) a.2)
        (rootCoefficient S rho hr (r b.1) b.2) := by
      rw [he]
      apply curveCoefficient_commute
      intro s t
      change _ * _ = _ * _
      rw [←map_mul,←map_mul,kPlusPoint_mul,kPlusPoint_mul,add_comm s t]
    rw [hh.eq,sub_self]
    exact U.zero_mem
  by_cases hs : ∃c,RootSum S (r a.1) (r b.1) c
  · obtain ⟨c,hc⟩ := hs
    obtain ⟨l,rfl⟩ := hclosed a.1 b.1 c hc
    obtain ⟨κ,_,heq⟩ := rootCoefficient_exchange_of_parameterRelations S hrel rho hr _ _ _ hc
    rw [heq a.2 b.2,Finset.sum_range_succ']
    simp only [pow_zero,one_smul,Nat.sub_zero,rootCoefficient,curveCoefficient_zero,mul_one,
      add_sub_cancel_right]
    change (∑j∈Finset.range (min a.2.val b.2.val),κ^(j+1) •
      (rootCoefficient S rho hr (r b.1) (b.2.val-(j+1)) *
        rootCoefficient S rho hr (r l) (j+1) *
        rootCoefficient S rho hr (r a.1) (a.2.val-(j+1))))∈U
    apply U.sum_mem
    intro j hj
    have hja : j+1≤a.2.val := by have := Finset.mem_range.mp hj; omega
    have hjb : j+1≤b.2.val := by have := Finset.mem_range.mp hj; omega
    apply U.smul_mem
    apply Submodule.subset_span
    refine ⟨[(b.1,⟨b.2.val-(j+1),by omega⟩),(l,⟨j+1,by omega⟩),
      (a.1,⟨a.2.val-(j+1),by omega⟩)],?_,?_⟩
    · simp only [wordDegree_cons,wordDegree_nil]
      omega
    · simp only [wordValue_cons,wordValue_nil,mul_one,mul_assoc]
  · have hh := rootCoefficient_commute_of_parameterRelations S hrel rho hr _ _ he
      (hop a.1 b.1) hs a.2 b.2
    rw [hh.eq,sub_self]
    exact U.zero_mem

lemma rootFamily_algebra_spanned (S : Geometry K) (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    {m : ℕ} (r : Fin m → S.roots.Root) (n : ℕ)
    (hop : ∀i j,r j ≠ S.roots.neg (r i))
    (hclosed : ∀i j c,RootSum S (r i) (r j) c → ∃l,r l=c) :
    (Algebra.adjoin k (Set.range fun p:Fin m × Fin (2^n)=>
      rootCoefficient S rho hr (r p.1) p.2)).toSubmodule ≤
        orderedSpan (k:=k) (fun (i:Fin m) (j:Fin (2^n))=>rootCoefficient S rho hr (r i) j) := by
  let X : Fin m × Fin (2^n) → Module.End k V := fun p=>rootCoefficient S rho hr (r p.1) p.2
  let B : Fin m → Subalgebra k (Module.End k V) := fun i=>
    Algebra.adjoin k (Set.range fun j:Fin (2^n)=>rootCoefficient S rho hr (r i) j)
  have hb (i:Fin m) : (B i).toSubmodule=Submodule.span k
      (Set.range fun j:Fin (2^n)=>rootCoefficient S rho hr (r i) j) :=
    adjoin_curveCoefficients_toSubmodule rho hr (rootCurve S (r i)) n
  rw [←algebraBlockProduct_eq_span _ B _ hb]
  apply adjoin_le_of_words
  intro w
  apply word_mem_of_reordering X (fun p=>p.2.val) (algebraBlockProduct B)
    (rootFamily_commutator_lower S hrel rho hr r hop hclosed) _ w
  intro z
  exact ⟨blockWord Prod.fst z,(blockWord_perm Prod.fst z).symm,
    blockWord_value_mem X Prod.fst B (fun a=>Algebra.subset_adjoin ⟨a.2,rfl⟩) z⟩
end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.SourcePBW
