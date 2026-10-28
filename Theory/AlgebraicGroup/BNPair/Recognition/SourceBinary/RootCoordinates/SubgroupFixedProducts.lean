module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts

/-!
# Subgroup centralizers in unique ordered root products

If a subgroup normalizes every factor of an injective ordered product,
an element of that product centralizes the subgroup exactly when each of
its coordinates does. This applies to the whole Cartan three-core, without
choosing a generator or assuming it cyclic. The resulting product is used
in Fong--Seitz I (6F), printed p.46.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {Y : Type*} [Group Y]

private def fixedTupleAction (l : List (Subgroup Y)) (T : Subgroup Y)
    (hn : ∀ A ∈ l, T ≤ normalizer (A : Set Y)) (t : T) : RootTuple l → RootTuple l :=
  match l with
  | [] => id
  | A::l => fun p => (A.normalizerMonoidHom ⟨t, hn A (by simp) t.property⟩ p.1,
      fixedTupleAction l T (fun B hB => hn B (List.mem_cons_of_mem A hB)) t p.2)

private theorem fixedTupleAction_product (l : List (Subgroup Y)) (T : Subgroup Y)
    (hn : ∀ A ∈ l, T ≤ normalizer (A : Set Y)) (t : T) (p : RootTuple l) :
    rootProduct l (fixedTupleAction l T hn t p) = (t : Y)*rootProduct l p*(t : Y)⁻¹ := by
  induction l with
  | nil => simp [rootProduct]
  | cons A l ih =>
    change ((t : Y)*p.1*(t : Y)⁻¹)*rootProduct l (fixedTupleAction l T _ t p.2) =
      (t : Y)*(p.1*rootProduct l p.2)*(t : Y)⁻¹
    rw [ih]
    group

private theorem fixedTuple_product (l : List (Subgroup Y)) (T : Subgroup Y)
    (hn : ∀ A ∈ l, T ≤ normalizer (A : Set Y)) (p : RootTuple l)
    (hp : ∀ t : T, fixedTupleAction l T hn t p = p) :
    rootProduct l p ∈ (l.map (fun A => (↑(A ⊓ centralizer (T : Set Y)) : Set Y))).prod := by
  induction l with
  | nil => exact rfl
  | cons A l ih =>
    have hfirst : (p.1 : Y) ∈ centralizer (T : Set Y) := by
      intro t ht
      have hh := congrArg (fun q : RootTuple (A::l) => (q.1 : Y)) (hp ⟨t,ht⟩)
      exact mul_inv_eq_iff_eq_mul.mp hh
    have htail (t : T) := congrArg (fun q : RootTuple (A::l) => q.2) (hp t)
    exact ⟨p.1,⟨p.1.property,hfirst⟩,rootProduct l p.2,ih _ p.2 htail,rfl⟩

/-- Centralizing a normalizing subgroup is a coordinatewise condition in
an injective ordered product. No coprimality or cyclicity is required. -/
theorem unique_root_product_centralizer (l : List (Subgroup Y)) (T : Subgroup Y)
    (hn : ∀ A ∈ l, T ≤ normalizer (A : Set Y))
    (hinj : Function.Injective (rootProduct l)) :
    Set.range (rootProduct l) ∩ (centralizer (T : Set Y) : Set Y) =
      (l.map (fun A => (↑(A ⊓ centralizer (T : Set Y)) : Set Y))).prod := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨p,rfl⟩,hp⟩
    apply fixedTuple_product l T hn p
    intro t
    apply hinj
    rw [fixedTupleAction_product, mem_centralizer_iff.mp hp t t.property,
      mul_inv_cancel_right]
  · intro x hx
    have hm : ∀ K : List (Subgroup Y),
        (K.map (fun A => (↑(A ⊓ centralizer (T : Set Y)) : Set Y))).prod ⊆
          (K.map (fun A => (A : Set Y))).prod := by
      intro K
      induction K with
      | nil => exact Set.Subset.rfl
      | cons A K ih => exact Set.mul_subset_mul (fun _ h => h.1) ih
    have hC : ∀ K : List (Subgroup Y),
        (K.map (fun A => (↑(A ⊓ centralizer (T : Set Y)) : Set Y))).prod ⊆
          (centralizer (T : Set Y) : Set Y) := by
      intro K
      induction K with
      | nil => exact fun _ h => h ▸ one_mem _
      | cons A K ih =>
        rintro z ⟨a,ha,b,hb,rfl⟩
        exact mul_mem ha.2 (ih hb)
    exact ⟨(rootProduct_range l).symm ▸ hm l hx,hC l hx⟩

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The full subgroup centralizer in a reduced root interval is the
ordered product of its root centralizers in the same quotient. -/
theorem ordered_root_subgroup_centralizer (b : Bool) (n : ℕ)
    (hn : n ≤ rotationOrder Q) (T : Subgroup (X ⧸ Q.D))
    (hTH : T ≤ Q.tits.B ⊓ Q.tits.N) :
    (↑(rootIntersection split (longest Q) (alternatingWord Q b n)⁻¹ ⊓
      centralizer (T : Set (X ⧸ Q.D))) : Set (X ⧸ Q.D)) =
      ((orderedRoots Q split b n).map
        (fun A => (↑(A ⊓ centralizer (T : Set (X ⧸ Q.D))) : Set (X ⧸ Q.D)))).prod := by
  have hinj : Function.Injective (rootProduct (orderedRoots Q split b n)) := by
    intro p q he
    apply (orderedCoordinates Q split b n hn).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  have he := unique_root_product_centralizer (orderedRoots Q split b n) T
    (fun A hA => hTH.trans (orderedRoots_torus_normalizes Q split b n A hA)) hinj
  rw [rootProduct_range,orderedRoots_product Q split b n hn] at he
  exact he

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
