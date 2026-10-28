module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Theory.AlgebraicGroup.Morphism.ClosedImage
public import Theory.AlgebraicGroup.Tori.Character.Tuple
public import Theory.AlgebraicGroup.Tori.Power

universe u

/-! Images of integer-matrix morphisms between diagonal tori. -/

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private noncomputable def dCharacterTupleBasisIso
    (n : ℕ) (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    AlgebraicGroup.Iso (dVariety k n) (dVariety k n) := by
  let z : Fin n → Fin n → ℤ := fun j => b j
  let c : Fin n → Fin n → ℤ := fun j => b.equivFun (Pi.single j 1)
  let hom := dCharacterTupleMorphism (k := k) n n z
  let inv := dCharacterTupleMorphism (k := k) n n c
  have hcb : inv.comp hom =
      Theory.AlgebraicGroup.Morphism.id (dVariety k n) := by
    rw [show inv.comp hom = dCharacterTupleMorphism (k := k) n n
        (fun q i => ∑ j, c q j * z j i) by
      exact dCharacterTupleMorphism_comp n n n c z]
    rw [← dCharacterTupleMorphism_basis (k := k) n]
    congr 1
    funext q i
    have h := congrFun (b.equivFun.symm_apply_apply (Pi.single q 1)) i
    rw [Module.Basis.equivFun_symm_apply] at h
    simpa [z, c, Pi.smul_apply, smul_eq_mul] using h
  have hbc : hom.comp inv =
      Theory.AlgebraicGroup.Morphism.id (dVariety k n) := by
    rw [show hom.comp inv = dCharacterTupleMorphism (k := k) n n
        (fun q i => ∑ j, z q j * c j i) by
      exact dCharacterTupleMorphism_comp n n n z c]
    rw [← dCharacterTupleMorphism_basis (k := k) n]
    congr 1
    funext q i
    calc
      (∑ j, z q j * c j i) =
          b.equivFun (∑ j, z q j • Pi.single j 1) i := by
        rw [map_sum, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_smul]
        rfl
      _ = b.equivFun (b q) i := by
        have hstd : (∑ j, z q j • Pi.single j 1) = b q := by
          simpa [z, Pi.basisFun_repr] using
            (Pi.basisFun ℤ (Fin n)).sum_repr (b q)
        rw [hstd]
      _ = (Pi.single q (1 : ℤ) : Fin n → ℤ) i := by
        rw [b.equivFun_self]
        simp [Pi.single_apply, eq_comm]
  exact
    { hom := hom
      inv := inv
      hom_inv_id := fun x => congrArg (fun f => f.onPoints x) hcb
      inv_hom_id := fun x => congrArg (fun f => f.onPoints x) hbc }

private lemma dCharacterTupleMorphism_surjective_of_smithNormalForm
    [IsAlgClosed k] {r n : ℕ} {N : Submodule ℤ (Fin n → ℤ)}
    (snf : Module.Basis.SmithNormalForm N (Fin n) r) :
    Function.Surjective
      (dCharacterTupleMorphism (k := k) r n
        (fun i => (snf.bN i : Fin n → ℤ))).onPoints := by
  intro y
  have ha : ∀ i, snf.a i ≠ 0 := by
    intro i hai
    have hzero : (snf.bN i : Fin n → ℤ) = 0 := by
      rw [snf.snf i, hai, zero_smul]
    exact snf.bN.ne_zero i (Subtype.ext hzero)
  choose root hroot using fun i =>
    units_zpow_surjective_of_isAlgClosed (k := k) (snf.a i) (ha i)
      (dPointEquiv r y i)
  let u : Fin n → kˣ := Function.extend snf.f root (fun _ => 1)
  let e := dCharacterTupleBasisIso (k := k) n snf.bM
  let yB : Variety.Point (dVariety k n) := (dPointEquiv n).symm u
  let x : Variety.Point (dVariety k n) := e.inv.onPoints yB
  refine ⟨x, ?_⟩
  apply (dPointEquiv r).injective
  funext i
  rw [dCharacterTupleMorphism_apply]
  have hcoord :
      (∏ j, (dPointEquiv n x j) ^ (snf.bM (snf.f i)) j) =
        u (snf.f i) := by
    rw [← dCharacterTupleMorphism_apply n n
      (fun j => (snf.bM j : Fin n → ℤ)) x (snf.f i)]
    change dPointEquiv n (e.hom.onPoints x) (snf.f i) = u (snf.f i)
    rw [e.inv_hom_id]
    rfl
  have hsnf := congrFun (snf.snf i)
  calc
    (∏ j, (dPointEquiv n x j) ^ (snf.bN i : Fin n → ℤ) j) =
        ∏ j, (dPointEquiv n x j) ^
          (snf.a i * (snf.bM (snf.f i)) j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hsnf j]
      rfl
    _ = (∏ j, (dPointEquiv n x j) ^
        (snf.bM (snf.f i)) j) ^ snf.a i := by
      rw [← Finset.prod_zpow]
      apply Finset.prod_congr rfl
      intro j hj
      rw [mul_comm, zpow_mul]
    _ = u (snf.f i) ^ snf.a i := by rw [hcoord]
    _ = root i ^ snf.a i := by
      congr 1
      change Function.extend snf.f root (fun _ => 1) (snf.f i) = root i
      exact Function.Injective.extend_apply snf.f.injective root
        (fun _ => 1) i
    _ = dPointEquiv r y i := hroot i

/-- The closed image of an integer-matrix morphism between standard diagonal
tori is itself a torus. -/
public theorem dCharacterTupleMorphism_image_isTorus
    [IsAlgClosed k] (m n : ℕ) (z : Fin m → Fin n → ℤ) :
    let f := dCharacterTupleMorphism (k := k) m n z
    let I := f.imageClosedSubgroup
    @IsTorus k _ I.carrierVariety I.carrierAlgebraicGroup := by
  let f := dCharacterTupleMorphism (k := k) m n z
  let I := f.imageClosedSubgroup
  let : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  let A : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    Fintype.linearCombination ℤ z
  let N : Submodule ℤ (Fin n → ℤ) := LinearMap.range A
  let ⟨r, snf⟩ := N.smithNormalForm (Pi.basisFun ℤ (Fin n))
  have hzN (j : Fin m) : z j ∈ N := by
    refine ⟨Pi.single j 1, ?_⟩
    simp [A, Fintype.linearCombination_apply_single]
  let zn : Fin m → N := fun j => ⟨z j, hzN j⟩
  let c : Fin m → Fin r → ℤ := fun j => snf.bN.equivFun (zn j)
  let h := dCharacterTupleMorphism (k := k) r n
    (fun i => (snf.bN i : Fin n → ℤ))
  let g := dCharacterTupleMorphism (k := k) m r c
  have hgh : g.comp h = f := by
    rw [show g.comp h = dCharacterTupleMorphism (k := k) m n
        (fun q i => ∑ j, c q j * (snf.bN j : Fin n → ℤ) i) by
      exact dCharacterTupleMorphism_comp m r n c
        (fun i => (snf.bN i : Fin n → ℤ))]
    change dCharacterTupleMorphism (k := k) m n _ =
      dCharacterTupleMorphism (k := k) m n z
    congr 1
    funext q i
    have hrecon := snf.bN.equivFun.symm_apply_apply (zn q)
    rw [Module.Basis.equivFun_symm_apply] at hrecon
    let ev : N →ₗ[ℤ] ℤ :=
      { toFun := fun x => x.val i
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    have hi := congrArg ev hrecon
    rw [map_sum] at hi
    simp only [map_smul] at hi
    change (∑ x, c q x * (snf.bN x : Fin n → ℤ) i) = z q i at hi
    exact hi
  have hsurj : Function.Surjective h.onPoints :=
    dCharacterTupleMorphism_surjective_of_smithNormalForm snf
  have hrange : Set.range g.onPoints = Set.range f.onPoints := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨x, hx⟩ := hsurj t
      refine ⟨x, ?_⟩
      have hpoint := congrArg (fun p => p.onPoints x) hgh
      change g.onPoints (h.onPoints x) = f.onPoints x at hpoint
      rw [hx] at hpoint
      exact hpoint.symm
    · rintro ⟨x, rfl⟩
      refine ⟨h.onPoints x, ?_⟩
      have hpoint := congrArg (fun p => p.onPoints x) hgh
      change g.onPoints (h.onPoints x) = f.onPoints x at hpoint
      exact hpoint
  have hIset : (I : Set (Variety.Point (dVariety k m))) =
      Set.range f.onPoints :=
    f.imageClosedSubgroup_carrier.trans f.image_carrier
  have hgI (x : Variety.Point (dVariety k r)) :
      g.onPoints x ∈ (I : Set (Variety.Point (dVariety k m))) := by
    rw [hIset, ← hrange]
    exact ⟨x, rfl⟩
  let gI : Theory.AlgebraicGroup.Morphism
      (dVariety k r) I.carrierVariety :=
    g.codRestrictClosedSubgroup I hgI
  let : Module.Free ℤ N := Module.Free.of_basis snf.bN
  let Ar : (Fin m → ℤ) →ₗ[ℤ] N := A.rangeRestrict
  obtain ⟨s, hs⟩ := Ar.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr A.surjective_rangeRestrict)
  let d : Fin r → Fin m → ℤ := fun i => s (snf.bN i)
  let q := dCharacterTupleMorphism (k := k) r m d
  have hqg : q.comp g =
      Theory.AlgebraicGroup.Morphism.id (dVariety k r) := by
    rw [show q.comp g = dCharacterTupleMorphism (k := k) r r
        (fun i l => ∑ j, d i j * c j l) by
      exact dCharacterTupleMorphism_comp r m r d c]
    rw [← dCharacterTupleMorphism_basis (k := k) r]
    congr 1
    funext i l
    have hsec : Ar (s (snf.bN i)) = snf.bN i := by
      have happ := LinearMap.congr_fun hs (snf.bN i)
      simpa using happ
    have hcoord := congrArg snf.bN.equivFun hsec
    have hl := congrFun hcoord l
    rw [show snf.bN.equivFun (snf.bN i) l =
        (Pi.single i (1 : ℤ) : Fin r → ℤ) l by
      rw [snf.bN.equivFun_self]
      simp [Pi.single_apply, eq_comm]] at hl
    calc
      (∑ j, d i j * c j l) =
          snf.bN.equivFun (∑ j, d i j • zn j) l := by
        rw [map_sum, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_smul]
        rfl
      _ = snf.bN.equivFun (Ar (s (snf.bN i))) l := by
        have hsub : (∑ j, d i j • zn j) = Ar (s (snf.bN i)) := by
          apply Subtype.ext
          simp [Ar, A, d, zn, Fintype.linearCombination_apply]
        rw [hsub]
      _ = (Pi.single i (1 : ℤ) : Fin r → ℤ) l := hl
  let qI : Theory.AlgebraicGroup.Morphism
      I.carrierVariety (dVariety k r) :=
    q.comp I.inclusion
  refine ⟨r, ⟨{
    hom := gI
    inv := qI
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩⟩
  · intro x
    have hpoint := congrArg (fun p => p.onPoints x) hqg
    change q.onPoints (g.onPoints x) = x at hpoint
    change q.onPoints (I.inclusion.onPoints (gI.onPoints x)) = x
    rw [g.codRestrictClosedSubgroup_inclusion_apply I hgI]
    exact hpoint
  · intro y
    apply I.inclusion_injective
    rw [g.codRestrictClosedSubgroup_inclusion_apply I hgI]
    change g.onPoints (q.onPoints (I.inclusion.onPoints y)) =
      I.inclusion.onPoints y
    have hyI : I.inclusion.onPoints y ∈
        (I : Set (Variety.Point (dVariety k m))) :=
      (I.pointEquiv y).property
    rw [hIset, ← hrange] at hyI
    rcases hyI with ⟨x, hx⟩
    rw [← hx]
    have hpoint := congrArg (fun p => p.onPoints x) hqg
    change q.onPoints (g.onPoints x) = x at hpoint
    rw [hpoint]

end Theory.AlgebraicGroup
