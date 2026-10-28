module
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootRegularity
public import Theory.GroupAction.OddDegreeCore

/-!
# The core of two opposite path radicals fixes the midpoint star

Two long paths ending at the same vertex, with distinct preceding vertices,
supply complementary transitive root actions on its neighbors. The odd
extension fixer makes one root regular on its exits, so thickness makes
the valence an odd number. The join's normal two-core therefore fixes the
entire neighbor set. This requires no normality of the join in the full
vertex stabilizer.

Source: DGS, *Groups and Graphs* (1985), (14.1), (14.3), (14.9),
pp.210--212,215--216.
-/

public noncomputable section
open Subgroup Theory.GroupAction
open SimpleGraph SimpleGraph.Walk
open scoped Pointwise
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

/-- The own two-core of the join of opposite path radicals fixes every neighbor. -/
theorem opposite_pathRoots_core_fixes_neighbors (htree : Γ.IsAcyclic)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {a b v : V} [Finite (Γ.neighborSet v)] (p : Γ.Walk a v) (q : Γ.Walk b v)
    (hp : p.IsPath) (hq : q.IsPath) (hpnil : ¬p.Nil) (hqnil : ¬q.Nil)
    (hdiff : p.penultimate≠q.penultimate) (hval : 3≤Nat.card (Γ.neighborSet v))
    (htransp : BasedPathTransitive (X := X) Γ (p.length+1))
    (htransq : BasedPathTransitive (X := X) Γ (q.length+1))
    (K : Subgroup X)
    (hKp : ∀ k∈K, k • p.penultimate=p.penultimate)
    (hKq : ∀ k∈K, k • q.penultimate=q.penultimate)
    (hfactorp : (pathFixer (X := X) p : Set X)=(pathRoot (X := X) p : Set X)*(K : Set X))
    (hfactorq : (pathFixer (X := X) q : Set X)=(pathRoot (X := X) q : Set X)*(K : Set X))
    (hodd : Odd (Nat.card (pathFixer (X := X) (p.concat (q.adj_penultimate hqnil).symm)))) :
    ∀ x∈(pathRoot (X := X) p ⊔ pathRoot (X := X) q).pCoreIn 2,
      ∀ w, Γ.Adj v w → x • w=w := by
  let A := pathRoot (X := X) p ⊔ pathRoot (X := X) q
  have hAp : A ≤ MulAction.stabilizer X v :=
    sup_le (fun x hx => (pathRoot_fixes p hx).1) (fun x hx => (pathRoot_fixes q hx).1)
  let cp : pathExit p := ⟨q.penultimate,(q.adj_penultimate hqnil).symm,hdiff.symm⟩
  have : Finite (pathExit p) := Finite.of_injective
    (fun z : pathExit p => (⟨z.val,z.property.1⟩ : Γ.neighborSet v))
    (fun x y he => Subtype.ext (congrArg (fun z : Γ.neighborSet v => z.val) he))
  have hfinite : Finite (pathRoot (X := X) p) :=
    Finite.of_equiv (pathExit p) (pathRootExitEquiv htree hact p hp htransp K cp hKq hfactorp hodd).symm
  have hc := card_pathRoot_add_one htree hact p hp hpnil htransp K cp hKq hfactorp hodd
  obtain ⟨e,he⟩ := (pathRoot_isTwo (X := X) p).exists_card_eq
  have henz : e≠0 := by intro h; simp only [h,pow_zero] at he; omega
  have hoddval : Odd (Nat.card (Γ.neighborSet v)) := by
    rw [←hc,he]
    exact (even_two.pow_of_ne_zero henz).add_odd odd_one
  have hpair : ({p.penultimate,q.penultimate} : Set V).ncard≤2 := by
    simpa using Set.ncard_insert_le p.penultimate ({q.penultimate} : Set V)
  have hlarge : ({p.penultimate,q.penultimate} : Set V).ncard < (Γ.neighborSet v).ncard := by
    rw [←Nat.card_coe_set_eq (Γ.neighborSet v)]
    omega
  obtain ⟨c,hc,hcne⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlarge
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hcne
  apply pCoreIn_fixes_of_transitive_on A (Γ.neighborSet v)
  · intro g hg w hw
    have hgv : g • v=v := hAp hg
    change Γ.Adj v (g • w)
    simpa only [hgv] using hact g hw
  · apply transitive_on_of_two_complement_orbits A (pathRoot (X := X) p) (pathRoot (X := X) q)
      (Γ.neighborSet v) le_sup_left le_sup_right hc hcne.1 hcne.2
    · exact pathRoot_transitive_exits htree p hp htransp K cp.property.1 cp.property.2 hKq hfactorp
    · exact pathRoot_transitive_exits htree q hq htransq K
        (p.adj_penultimate hpnil).symm hdiff hKp hfactorq
  · exact hoddval
end Theory.GroupTheory.WeakBNPair.RegularTree
