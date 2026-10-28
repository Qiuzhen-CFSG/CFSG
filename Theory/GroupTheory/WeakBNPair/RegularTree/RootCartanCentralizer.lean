module
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootRegularity
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# Cartan centralizers of path radicals

A complement fixing the chosen exit centralizes the path radical exactly
when it fixes the entire endpoint star. Transitivity proves one direction;
regularity makes conjugation trivial in the other. Thus the centralizer
uses the full local permutation kernel, without identifying that kernel
with the vertex two-core.

Source application: DGS, Groups and Graphs (1985), (14.3)(d) and
(14.5)(b), pp.212--213.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.Walk
open scoped Pointwise
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

/-- A pointwise path fixer normalizes the actual path radical. -/
theorem pathFixer_le_normalizer_pathRoot {a b : V} (p : Γ.Walk a b) :
    pathFixer (X := X) p ≤ normalizer (pathRoot (X := X) p : Set X) := by
  intro k hk
  exact mem_normalizer_iff_map_conj_eq.mpr (pathRoot_map_conj p p k rfl hk)

/-- Inside the path complement, centralizing the radical is exactly fixing
all neighbors of the endpoint. The kernel is the full permutation kernel. -/
theorem pathRoot_commute_iff_fixes_neighbors (htree : Γ.IsAcyclic)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {a b c : V} (p : Γ.Walk a b) (hp : p.IsPath)
    (htrans : BasedPathTransitive (X := X) Γ (p.length+1))
    (K : Subgroup X) (hK : K ≤ pathFixer (X := X) p)
    (hc : Γ.Adj b c) (hcprev : c ≠ p.penultimate)
    (hKc : ∀ k∈K, k • c=c)
    (hfactor : (pathFixer (X := X) p : Set X) =
      (pathRoot (X := X) p : Set X)*(K : Set X))
    (hodd : Odd (Nat.card (pathFixer (X := X) (p.concat hc))))
    (k : X) (hk : k∈K) :
    (∀ x∈pathRoot (X := X) p, Commute k x) ↔
      ∀ z, Γ.Adj b z → k • z=z := by
  constructor
  · intro hcomm z hz
    by_cases he : z=p.penultimate
    · rw [he]
      exact hK hk _ (Nat.sub_le _ _)
    obtain ⟨x,hx,hxc⟩ := pathRoot_transitive_exits htree p hp htrans K hc hcprev hKc hfactor z hz he
    rw [←hxc,←mul_smul,(hcomm x hx).eq,mul_smul,hKc k hk]
  · intro hstar x hx
    have hn := pathFixer_le_normalizer_pathRoot p (hK hk)
    have hconj : k*x*k⁻¹∈pathRoot (X := X) p :=
      (mem_normalizer_iff.mp hn x).mp hx
    have hkc : k⁻¹ • c=c := by
      calc
        k⁻¹ • c = k⁻¹ • (k • c) := congrArg (fun z => k⁻¹ • z) (hKc k hk).symm
        _ = c := inv_smul_smul k c
    have hxb : x • b=b := (pathRoot_fixes p hx).1
    have hxc : Γ.Adj b (x • c) := by simpa only [hxb] using hact x hc
    have he := pathRoot_smul_injective p hc hodd
      (a₁ := ⟨k*x*k⁻¹,hconj⟩) (a₂ := ⟨x,hx⟩)
      (by change (k*x*k⁻¹) • c=x • c; rw [mul_smul,mul_smul,hkc,hstar _ hxc])
    have hv := congrArg (fun y : pathRoot (X := X) p => (y:X)*k) he
    exact show k*x=x*k by simpa only [mul_assoc,inv_mul_cancel,mul_one] using hv
end Theory.GroupTheory.WeakBNPair.RegularTree
