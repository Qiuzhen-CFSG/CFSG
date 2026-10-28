module
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRoot

/-!
# Sharp transitivity of actual long-path radicals

The pointwise fixer of a one-step extension is the intersection of the
original path fixer and the new vertex stabilizer. If its order is odd,
its intersection with the original path two-core is trivial. Thus the
long-path root acts freely on exits. The Cartan factorization and path
transitivity proved in `PathRoot` then make this action sharply transitive.
Evaluation at an exit gives an explicit equivalence, so the root order is
exactly the endpoint valence minus one.

No faithfulness of the whole ambient action, or identification of the
vertex two-core with the full local permutation kernel, is used.
Source: DGS, *Groups and Graphs* (1985), Part II, (14.1) and the root-group
notation following (14.2), printed pp.210--211.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
open scoped Pointwise
variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

/-- A one-step extension adds exactly its new vertex stabilizer. -/
theorem pathFixer_concat_eq {a b c : V} (p : Γ.Walk a b) (h : Γ.Adj b c) :
    pathFixer (X := X) (p.concat h) = pathFixer p ⊓ MulAction.stabilizer X c := by
  ext x
  constructor
  · intro hx
    constructor
    · intro k hk
      have hh := hx k (by simpa only [length_concat] using (show k ≤ p.length+1 by omega))
      simpa only [concat_eq_append, getVert_append', if_pos hk] using hh
    · change x • c = c
      have hh := hx (p.concat h).length le_rfl
      simpa only [getVert_length] using hh
  · rintro ⟨hx, hc⟩ k hk
    rw [length_concat] at hk
    by_cases hle : k ≤ p.length
    · simpa only [concat_eq_append, getVert_append', if_pos hle] using hx k hle
    · have he : k = (p.concat h).length := by rw [length_concat]; omega
      change x • c = c at hc
      simpa only [he, getVert_length] using hc

/-- An odd extension fixer has trivial intersection with the original two-core. -/
theorem pathRoot_inf_stabilizer_eq_bot {a b c : V} (p : Γ.Walk a b)
    (hc : Γ.Adj b c) (hodd : Odd (Nat.card (pathFixer (X := X) (p.concat hc)))) :
    pathRoot (X := X) p ⊓ MulAction.stabilizer X c = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxF : x ∈ pathFixer (X := X) (p.concat hc) := by
    rw [pathFixer_concat_eq]
    exact ⟨(pathFixer p).pCoreIn_le 2 hx.1, hx.2⟩
  obtain ⟨k, hk⟩ := pathRoot_isTwo (X := X) p ⟨x, hx.1⟩
  have hp : orderOf x ∣ 2^k := by
    simpa only [Subgroup.orderOf_mk] using orderOf_dvd_of_pow_eq_one hk
  have ho : orderOf x ∣ Nat.card (pathFixer (X := X) (p.concat hc)) := by
    simpa only [Subgroup.orderOf_mk] using
      orderOf_dvd_natCard (⟨x, hxF⟩ : pathFixer (X := X) (p.concat hc))
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right k) ho hp)

/-- Evaluation at an odd extension is injective on the actual long-path radical. -/
theorem pathRoot_smul_injective {a b c : V} (p : Γ.Walk a b)
    (hc : Γ.Adj b c) (hodd : Odd (Nat.card (pathFixer (X := X) (p.concat hc)))) :
    Function.Injective (fun x : pathRoot (X := X) p => (x : X) • c) := by
  intro x y hxy
  change (x : X) • c = (y : X) • c at hxy
  apply Subtype.ext
  apply inv_mul_eq_one.mp
  have hm : (x : X)⁻¹ * y ∈ pathRoot (X := X) p ⊓ MulAction.stabilizer X c := by
    refine ⟨(pathRoot p).mul_mem ((pathRoot p).inv_mem x.property) y.property, ?_⟩
    change ((x : X)⁻¹ * y) • c = c
    rw [mul_smul, ← hxy, inv_smul_smul]
  rw [pathRoot_inf_stabilizer_eq_bot p hc hodd] at hm
  exact hm

/-- The long-path radical acts sharply transitively on the exits. -/
theorem pathRoot_sharply_transitive_exits (htree : Γ.IsAcyclic)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath)
    (htrans : BasedPathTransitive (X := X) Γ (p.length+1))
    (K : Subgroup X) {c : V} (hc : Γ.Adj b c) (hcprev : c ≠ p.penultimate)
    (hKc : ∀ k ∈ K, k • c = c)
    (hfactor : (pathFixer (X := X) p : Set X) =
      (pathRoot (X := X) p : Set X) * (K : Set X))
    (hodd : Odd (Nat.card (pathFixer (X := X) (p.concat hc)))) :
    ∀ z, Γ.Adj b z → z ≠ p.penultimate →
      ∃! x : pathRoot (X := X) p, (x : X) • c = z := by
  intro z hz hprev
  obtain ⟨x, hx, he⟩ := pathRoot_transitive_exits htree p hp htrans K hc hcprev hKc
    hfactor z hz hprev
  exact ⟨⟨x, hx⟩, he, fun y hy => pathRoot_smul_injective p hc hodd (hy.trans he.symm)⟩

/-- The actual exits are neighbors other than the preceding path vertex. -/
abbrev pathExit {a b : V} (p : Γ.Walk a b) := {z : V // Γ.Adj b z ∧ z ≠ p.penultimate}

/-- The root fixes the preceding vertex, and hence preserves its complement among neighbors. -/
theorem pathRoot_smul_exit
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {a b : V} (p : Γ.Walk a b) (c : pathExit p) (x : pathRoot (X := X) p) :
    Γ.Adj b ((x : X) • (c : V)) ∧ (x : X) • (c : V) ≠ p.penultimate := by
  have hx := pathRoot_fixes p x.property
  have hxb : (x : X) • b = b := hx.1
  have hxp : (x : X) • p.penultimate = p.penultimate := hx.2
  constructor
  · simpa only [hxb] using hact (x : X) c.property.1
  · intro he
    exact c.property.2 ((MulAction.toPerm (x : X)).injective (he.trans hxp.symm))

/-- Evaluating the root at an exit identifies its carrier with the entire exit set. -/
def pathRootExitEquiv (htree : Γ.IsAcyclic)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath)
    (htrans : BasedPathTransitive (X := X) Γ (p.length+1))
    (K : Subgroup X) (c : pathExit p)
    (hKc : ∀ k ∈ K, k • (c : V) = c)
    (hfactor : (pathFixer (X := X) p : Set X) =
      (pathRoot (X := X) p : Set X) * (K : Set X))
    (hodd : Odd (Nat.card (pathFixer (X := X) (p.concat c.property.1)))) :
    pathRoot (X := X) p ≃ pathExit p :=
  Equiv.ofBijective
    (fun x => ⟨(x : X) • (c : V), pathRoot_smul_exit hact p c x⟩)
    ⟨fun x y h => pathRoot_smul_injective p c.property.1 hodd (congrArg Subtype.val h), by
      intro z
      obtain ⟨x, hx, he⟩ := pathRoot_transitive_exits htree p hp htrans K
        c.property.1 c.property.2 hKc hfactor z z.property.1 z.property.2
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩⟩

@[simp] theorem pathRootExitEquiv_apply (htree : Γ.IsAcyclic)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath)
    (htrans : BasedPathTransitive (X := X) Γ (p.length+1))
    (K : Subgroup X) (c : pathExit p)
    (hKc : ∀ k ∈ K, k • (c : V) = c)
    (hfactor : (pathFixer (X := X) p : Set X) =
      (pathRoot (X := X) p : Set X) * (K : Set X))
    (hodd : Odd (Nat.card (pathFixer (X := X) (p.concat c.property.1))))
    (x : pathRoot (X := X) p) :
    (pathRootExitEquiv htree hact p hp htrans K c hKc hfactor hodd x : V) =
      (x : X) • (c : V) := rfl

/-- A nonempty path excludes exactly one neighbor from its exit set. -/
theorem card_pathExit {a b : V} [Finite (Γ.neighborSet b)]
    (p : Γ.Walk a b) (hpnil : ¬ p.Nil) :
    Nat.card (pathExit p) + 1 = Nat.card (Γ.neighborSet b) := by
  classical
  let v : Γ.neighborSet b := ⟨p.penultimate, (p.adj_penultimate hpnil).symm⟩
  let e : pathExit p ≃ {z : Γ.neighborSet b // z ≠ v} :=
    { toFun := fun z => ⟨⟨z, z.property.1⟩, by
        intro he; exact z.property.2 (congrArg Subtype.val he)⟩
      invFun := fun z => ⟨z.val, z.val.property, by
        intro he; exact z.property (Subtype.ext he)⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl }
  let := Fintype.ofFinite (Γ.neighborSet b)
  let := Fintype.ofFinite {z : Γ.neighborSet b // z ≠ v}
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h := Fintype.card_subtype_compl (fun z : Γ.neighborSet b => z = v)
  rw [Fintype.card_subtype_eq] at h
  rw [h]
  have hh : 0 < Fintype.card (Γ.neighborSet b) := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

/-- Odd one-step extensions make the root order exactly the number of exits. -/
theorem card_pathRoot_add_one (htree : Γ.IsAcyclic)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {a b : V} [Finite (Γ.neighborSet b)] (p : Γ.Walk a b)
    (hp : p.IsPath) (hpnil : ¬ p.Nil)
    (htrans : BasedPathTransitive (X := X) Γ (p.length+1))
    (K : Subgroup X) (c : pathExit p)
    (hKc : ∀ k ∈ K, k • (c : V) = c)
    (hfactor : (pathFixer (X := X) p : Set X) =
      (pathRoot (X := X) p : Set X) * (K : Set X))
    (hodd : Odd (Nat.card (pathFixer (X := X) (p.concat c.property.1)))) :
    Nat.card (pathRoot (X := X) p) + 1 = Nat.card (Γ.neighborSet b) := by
  rw [Nat.card_congr (pathRootExitEquiv htree hact p hp htrans K c hKc hfactor hodd)]
  exact card_pathExit p hpnil

end Theory.GroupTheory.WeakBNPair.RegularTree
