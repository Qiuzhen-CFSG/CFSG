module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Fixed products in ordered root coordinates

An automorphism preserving each factor of an ordered root product acts on the
coordinate tuple componentwise.  When the ordered product is injective, the
fixed part of its image is therefore exactly the product of the fixed parts
of the individual factors.  This is the generic coordinate lemma used by the
octagon centralizer arguments; all source-specific commutator work remains in
the consuming modules.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {Y : Type*} [Group Y]

private def tupleAction (α : MulAut Y) (l : List (Subgroup Y))
    (hn : ∀ A ∈ l, ∀ x ∈ A, α x ∈ A) : RootTuple l → RootTuple l :=
  match l with
  | [] => id
  | A::l => fun p => (⟨α p.1,hn A (by simp) p.1 p.1.property⟩,
      tupleAction α l (fun B hB => hn B (List.mem_cons_of_mem A hB)) p.2)

private theorem product_tupleAction (α : MulAut Y) (l : List (Subgroup Y))
    (hn : ∀ A ∈ l, ∀ x ∈ A, α x ∈ A) (p : RootTuple l) :
    rootProduct l (tupleAction α l hn p) = α (rootProduct l p) := by
  induction l with
  | nil => exact (map_one α).symm
  | cons A l ih =>
    change α p.1 * rootProduct l (tupleAction α l _ p.2) = α (p.1 * rootProduct l p.2)
    rw [ih,map_mul]

private theorem product_fixed_factors (α : MulAut Y) (l : List (Subgroup Y))
    (hn : ∀ A ∈ l, ∀ x ∈ A, α x ∈ A) (p : RootTuple l)
    (hp : tupleAction α l hn p = p) :
    rootProduct l p ∈ ((l.map (fun A => (A ⊓ α.fixedSubgroup : Subgroup Y))).map
      (fun A => (A : Set Y))).prod := by
  induction l with
  | nil => exact rfl
  | cons A l ih =>
    have hfirst : α (p.1 : Y) = p.1 := congrArg (fun q : RootTuple (A::l) => (q.1 : Y)) hp
    have htail := congrArg (fun q : RootTuple (A::l) => q.2) hp
    exact ⟨p.1,⟨p.1.property,(MulAut.mem_fixedSubgroup α p.1).mpr hfirst⟩,
      rootProduct l p.2,ih _ p.2 htail,rfl⟩

/-- Unique ordered coordinates make the fixed subgroup the product of the fixed root factors. -/
theorem unique_root_product_fixed (α : MulAut Y) (l : List (Subgroup Y))
    (hn : ∀ A ∈ l, ∀ x ∈ A, α x ∈ A)
    (hinj : Function.Injective (rootProduct l)) :
    (Set.range (rootProduct l)) ∩ (α.fixedSubgroup : Set Y) =
      ((l.map (fun A => (A ⊓ α.fixedSubgroup : Subgroup Y))).map
        (fun A => (A : Set Y))).prod := by
  ext y
  constructor
  · rintro ⟨⟨p,rfl⟩,hp⟩
    apply product_fixed_factors α l hn p
    apply hinj
    rw [product_tupleAction]
    exact (MulAut.mem_fixedSubgroup α _).mp hp
  · intro hy
    rw [←rootProduct_range] at hy
    obtain ⟨p,rfl⟩ := hy
    have hr : rootProduct (l.map fun A => A ⊓ α.fixedSubgroup) p ∈
        (l.map (fun A => (A : Set Y))).prod := by
      have hm : ∀ K : List (Subgroup Y),
          ((K.map fun A => A ⊓ α.fixedSubgroup).map (fun A => (A : Set Y))).prod ⊆
            (K.map (fun A => (A : Set Y))).prod := by
        intro K
        induction K with
        | nil => exact Set.Subset.rfl
        | cons A K ih =>
          exact Set.mul_subset_mul (show (↑(A ⊓ α.fixedSubgroup) : Set Y) ⊆ A from fun _ h => h.1) ih
      exact hm l ((rootProduct_range _).le ⟨p,rfl⟩)
    refine ⟨(rootProduct_range l).symm ▸ hr,rootProduct_mem _ _ ?_ p⟩
    intro A hA
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
    exact inf_le_right

private theorem conj_fixedSubgroup_eq_centralizer (c : Y) :
    (MulAut.conj c).fixedSubgroup = centralizer ({c} : Set Y) := by
  ext x
  rw [MulAut.mem_fixedSubgroup, mem_centralizer_singleton_iff]
  constructor
  · intro h
    change c * x * c⁻¹ = x at h
    have hc : c*x = x*c := by
      calc
        c*x = (c*x*c⁻¹)*c := by group
        _ = x*c := by rw [h]
    exact hc.symm
  · intro h
    change c * x * c⁻¹ = x
    calc
      c*x*c⁻¹ = (x*c)*c⁻¹ := by rw [h]
      _ = x := by rw [mul_assoc,mul_inv_cancel,mul_one]

/-- Ordered root coordinates identify the fixed part of a conjugation action.

The factor-normalization premise is discharged for ordered roots by the full
Cartan normalization theorem.  The result is stated with an arbitrary
conjugating element so it can be used for cubic actors as well as full
Cartan fixed-point calculations.
-/
theorem ordered_root_product_conj_fixed
    {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
    (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (b : Bool) (n : ℕ) (hn : n ≤ rotationOrder Q)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    (Set.range (rootProduct (orderedRoots Q split b n))) ∩
        (centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (((orderedRoots Q split b n).map
        (fun A => (A ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)))).map
        (fun A => (A : Set (X ⧸ Q.D)))).prod := by
  let l := orderedRoots Q split b n
  have hnorm : ∀ A ∈ l, ∀ x ∈ A, MulAut.conj (c : X ⧸ Q.D) x ∈ A := by
    intro A hA x hx
    exact ((mem_normalizer_iff.mp (orderedRoots_torus_normalizes Q split b n A hA c.property)) x).mp hx
  have hinj : Function.Injective (rootProduct l) := by
    intro p q he
    apply (orderedCoordinates Q split b n hn).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  have hfixed := unique_root_product_fixed (MulAut.conj (c : X ⧸ Q.D)) l hnorm hinj
  rw [conj_fixedSubgroup_eq_centralizer (c : X ⧸ Q.D)] at hfixed
  exact hfixed

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
