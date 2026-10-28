module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.GrassmannConditions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# Grassmann assignments from local SL₅(2) seed relations

A seed defines a value on its exterior-vector orbit by transporting it through
SL₅(2). The seed's stabilizer relation makes this value independent of the chosen
transporter. Assigning zero off that orbit gives an equivariant function on the
exterior power, hence a function on ordered frames vanishing on dependent ones.

Independent frames with the same span have the same exterior vector: their
change-of-basis determinant is a nonzero binary scalar, hence one. For the line
relation, independence of the three frames with final vectors x, y, and x+y
forces their common frame together with x and y to be independent. Extend its
isomorphism with the standard frame to the ambient space; over F₂ this is an
SL₅ element. Transport the seed relation along it, using that exchanging frame
positions has no sign in characteristic two.

This is the orbit-construction step in the exterior presentation used for
Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma I.1.6(7),
printed p.408/PDF p.419. It is valid for an arbitrary binary representation;
module classification and cohomology vanishing are separate results.
-/

open Module

namespace Representation.SL5TenDimensional.Classification
private theorem binary_unit {c : ZMod 2} (hc : IsUnit c) : c = 1 := by
  exact (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc.ne_zero

private theorem exists_frame_map {ι : Type*} (s t : ι → BinarySpace)
    (hs : LinearIndependent (ZMod 2) s) (ht : LinearIndependent (ZMod 2) t) :
    ∃ g : Group, ∀ i, Matrix.mulVec g.val (s i) = t i := by
  let e := (Basis.span hs).equiv (Basis.span ht) (Equiv.refl ι)
  obtain ⟨f, hf⟩ := Submodule.exists_linearEquiv_restrict_eq e
  have hdet : (LinearMap.toMatrix' f.toLinearMap).det = 1 := by
    rw [LinearMap.det_toMatrix']
    exact binary_unit f.isUnit_det'
  refine ⟨⟨LinearMap.toMatrix' f.toLinearMap, hdet⟩, fun i => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  change f (s i) = t i
  have h := hf (Basis.span hs i)
  simpa only [e, Basis.equiv_apply, Equiv.refl_apply, Basis.coe_span_apply] using h.symm

private theorem alternating_basis {ι M N : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup N] [Module (ZMod 2) N]
    (b : Basis ι (ZMod 2) M) (A : M [⋀^ι]→ₗ[ZMod 2] N) :
    A = b.det.smulRight (A b) := by
  apply b.ext_alternating
  intro f hf
  let e : Equiv.Perm ι := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  change A (b ∘ e) = (b.det.smulRight (A b)) (b ∘ e)
  simp [AlternatingMap.map_perm, Basis.det_self]

private theorem wedge_equal_span (a : Fin 2) (s t : BinaryFrame a)
    (hs : LinearIndependent (ZMod 2) s) (ht : LinearIndependent (ZMod 2) t)
    (hst : Submodule.span (ZMod 2) (Set.range s) =
      Submodule.span (ZMod 2) (Set.range t)) :
    exteriorPower.ιMulti (ZMod 2) (degree a) s =
      exteriorPower.ιMulti (ZMod 2) (degree a) t := by
  let b := Basis.span hs
  let c := (Basis.span ht).map (LinearEquiv.ofEq _ _ hst.symm)
  let A := (exteriorPower.ιMulti (ZMod 2) (degree a)).compLinearMap
    (Submodule.span (ZMod 2) (Set.range s)).subtype
  have hdet : b.det c = 1 := binary_unit (b.isUnit_det c)
  have h := congrArg (fun F => F c) (alternating_basis b A)
  simp only [AlternatingMap.smulRight_apply, hdet, one_smul] at h
  simpa [A, b, c, Function.comp_def] using h.symm


private theorem binary_add_self {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (x : M) : x + x = 0 := by
  calc
    x + x = ((1 : ZMod 2) + 1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

private theorem image_update_compl {ι M : Type*} [DecidableEq ι]
    (w : ι → M) (i : ι) (x : M) :
    Function.update w i x '' ({i}ᶜ : Set ι) = w '' ({i}ᶜ : Set ι) := by
  apply Set.image_congr
  intro j hj
  exact Function.update_of_ne (by simpa using hj) _ _

private theorem range_update {ι M : Type*} [DecidableEq ι]
    (w : ι → M) (i : ι) (x : M) :
    Set.range (Function.update w i x) = insert x (w '' ({i}ᶜ : Set ι)) := by
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    by_cases h : j = i
    · subst j; simp
    · exact Or.inr ⟨j, by simpa using h, Function.update_of_ne h _ _ |>.symm⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨i, Function.update_self _ _ _⟩
    · exact ⟨j, Function.update_of_ne (by simpa using hj) _ _⟩

private theorem line_notMem (a : Fin 2) (w : BinaryFrame a)
    (i : Fin (degree a)) (x y : BinarySpace)
    (hy : LinearIndependent (ZMod 2) (Function.update w i y))
    (hxy : LinearIndependent (ZMod 2) (Function.update w i (x + y))) :
    y ∉ Submodule.span (ZMod 2) (Set.range (Function.update w i x)) := by
  have hy' := hy.notMem_span i
  have hxy' := hxy.notMem_span i
  simp only [Function.update_self, image_update_compl] at hy' hxy'
  rw [range_update, Submodule.mem_span_insert]
  rintro ⟨c, z, hz, heq⟩
  have hc : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  rcases hc with rfl | rfl
  · apply hy'
    simpa only [heq, zero_smul, zero_add] using hz
  · apply hxy'
    have he : x + y = z := by
      rw [heq, one_smul, ← add_assoc, binary_add_self, zero_add]
    exact he.symm ▸ hz

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private noncomputable def orbitValue (ρ : Representation (ZMod 2) Group V)
    (a : Fin 2) (v : V) (z : ExteriorModule (degree a)) : V := by
  classical
  exact if h : ∃ g : Group, exteriorAction (degree a) g (seed a) = z then
    ρ h.choose v else 0

private theorem orbitValue_on_orbit (ρ : Representation (ZMod 2) Group V)
    (a : Fin 2) (v : V) (hv : HasExteriorSeed ρ a v) (g : Group) :
    orbitValue ρ a v (exteriorAction (degree a) g (seed a)) = ρ g v := by
  classical
  let h : ∃ k : Group, exteriorAction (degree a) k (seed a) =
      exteriorAction (degree a) g (seed a) := ⟨g, rfl⟩
  rw [orbitValue, dif_pos h]
  have he : exteriorAction (degree a) (g⁻¹ * h.choose) (seed a) = seed a := by
    rw [map_mul]
    change exteriorAction (degree a) g⁻¹
      (exteriorAction (degree a) h.choose (seed a)) = seed a
    rw [h.choose_spec]
    exact (exteriorAction (degree a)).inv_self_apply g (seed a)
  have hh := congrArg (fun z => ρ g z) (hv.1 (g⁻¹ * h.choose) he)
  simpa only [map_mul, Module.End.mul_apply, ρ.self_inv_apply] using hh

private theorem orbitValue_zero (ρ : Representation (ZMod 2) Group V)
    (a : Fin 2) (v : V) : orbitValue ρ a v 0 = 0 := by
  classical
  unfold orbitValue
  apply dif_neg
  rintro ⟨g, hg⟩
  apply seed_ne_zero a
  have := congrArg (fun z => exteriorAction (degree a) g⁻¹ z) hg
  simpa only [(exteriorAction (degree a)).inv_self_apply, map_zero] using this

private theorem orbitValue_equivariant (ρ : Representation (ZMod 2) Group V)
    (a : Fin 2) (v : V) (hv : HasExteriorSeed ρ a v) (g : Group)
    (z : ExteriorModule (degree a)) :
    orbitValue ρ a v (exteriorAction (degree a) g z) = ρ g (orbitValue ρ a v z) := by
  classical
  by_cases hz : ∃ k : Group, exteriorAction (degree a) k (seed a) = z
  · obtain ⟨k, rfl⟩ := hz
    rw [orbitValue_on_orbit ρ a v hv]
    have he : exteriorAction (degree a) g (exteriorAction (degree a) k (seed a)) =
        exteriorAction (degree a) (g * k) (seed a) := by rw [map_mul]; rfl
    rw [he, orbitValue_on_orbit ρ a v hv, map_mul]
    rfl
  · have hz' : ¬ ∃ k : Group, exteriorAction (degree a) k (seed a) =
        exteriorAction (degree a) g z := by
      rintro ⟨k, hk⟩
      apply hz
      refine ⟨g⁻¹ * k, ?_⟩
      rw [map_mul]
      change exteriorAction (degree a) g⁻¹ (exteriorAction (degree a) k (seed a)) = z
      rw [hk, (exteriorAction (degree a)).inv_self_apply]
    simp only [orbitValue, dif_neg hz, dif_neg hz', map_zero]


private def nextVector (a : Fin 2) : BinarySpace := Pi.single ⟨a.val + 2, by omega⟩ 1

private theorem augmented_independent (a : Fin 2) :
    LinearIndependent (ZMod 2) (Fin.snoc (frame a) (nextVector a)) := by
  have h : Fin.snoc (frame a) (nextVector a) =
      (fun j : Fin (degree a + 1) =>
        (Pi.single (Fin.castLE (by dsimp [degree]; omega) j : Fin 5) (1 : ZMod 2) : BinarySpace)) := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.snoc_last]; rfl
    · rw [Fin.snoc_castSucc]; rfl
  rw [h]
  exact (Pi.linearIndependent_single_one (Fin 5) (ZMod 2)).comp _ (Fin.castLE_injective _)

private theorem standard_step (a : Fin 2) :
    (fun i => Matrix.mulVec (step a).val (frame a i)) =
      Function.update (frame a) (Fin.last (a.val + 1))
        (frame a (Fin.last (a.val + 1)) + nextVector a) := by
  revert a
  decide

private theorem standard_swap (a : Fin 2) :
    (fun i => Matrix.mulVec (swap a).val (frame a i)) =
      Function.update (frame a) (Fin.last (a.val + 1)) (nextVector a) := by
  revert a
  decide

private theorem wedge_swap (a : Fin 2) (w : BinaryFrame a) (i j : Fin (degree a)) :
    exteriorPower.ιMulti (ZMod 2) (degree a) (w ∘ Equiv.swap i j) =
      exteriorPower.ιMulti (ZMod 2) (degree a) w := by
  by_cases h : i = j
  · subst j; simp
  · rw [AlternatingMap.map_swap _ _ h]
    exact neg_eq_iff_add_eq_zero.mpr (binary_add_self _)



private theorem orbitValue_line (ρ : Representation (ZMod 2) Group V)
    (a : Fin 2) (v : V) (hv : HasExteriorSeed ρ a v)
    (w : BinaryFrame a) (i : Fin (degree a)) (x y : BinarySpace)
    (hx : LinearIndependent (ZMod 2) (Function.update w i x))
    (hy : LinearIndependent (ZMod 2) (Function.update w i y))
    (hxy : LinearIndependent (ZMod 2) (Function.update w i (x + y))) :
    orbitValue ρ a v (exteriorPower.ιMulti (ZMod 2) (degree a) (Function.update w i x)) +
    orbitValue ρ a v (exteriorPower.ιMulti (ZMod 2) (degree a) (Function.update w i y)) +
    orbitValue ρ a v (exteriorPower.ιMulti (ZMod 2) (degree a) (Function.update w i (x + y))) = 0 := by
  classical
  let l : Fin (degree a) := Fin.last (a.val + 1)
  let e := Equiv.swap i l
  let wx := Function.update w i x
  have hel : e l = i := Equiv.swap_apply_right _ _
  have hecomp : LinearIndependent (ZMod 2) (wx ∘ e) := hx.comp e e.injective
  have hnot : y ∉ Submodule.span (ZMod 2) (Set.range (wx ∘ e)) := by
    rw [e.surjective.range_comp]
    exact line_notMem a w i x y hy hxy
  obtain ⟨g, hg⟩ := exists_frame_map
    (Fin.snoc (frame a) (nextVector a)) (Fin.snoc (wx ∘ e) y)
    (augmented_independent a) (hecomp.finSnoc hnot)
  have hframe (j : Fin (degree a)) : Matrix.mulVec g.val (frame a j) = wx (e j) := by
    simpa only [Fin.snoc_castSucc, Function.comp_apply] using hg j.castSucc
  have hnext : Matrix.mulVec g.val (nextVector a) = y := by
    simpa only [Fin.snoc_last] using hg (Fin.last (degree a))
  have htrans (z z' : BinarySpace) (hz : Matrix.mulVec g.val z = z') :
      (fun j => Matrix.mulVec g.val (Function.update (frame a) l z j)) =
        Function.update w i z' ∘ e := by
    funext j
    by_cases hj : j = l
    · subst j
      simp only [Function.update_self, Function.comp_apply, hel, hz]
    · have hji : e j ≠ i := fun he => hj (e.injective (he.trans hel.symm))
      simp only [Function.update_of_ne hj, Function.comp_apply, Function.update_of_ne hji]
      simpa only [wx, Function.update_of_ne hji] using hframe j
  have hswap : (fun j => Matrix.mulVec (g * swap a).val (frame a j)) =
      Function.update w i y ∘ e := by
    have heq : (fun j => Matrix.mulVec (g * swap a).val (frame a j)) =
        (fun j => Matrix.mulVec g.val (Matrix.mulVec (swap a).val (frame a j))) := by
      funext j
      exact Matrix.mulVec_mulVec _ _ _ |>.symm
    rw [heq]
    change (fun j => Matrix.mulVec g.val ((fun k => Matrix.mulVec (swap a).val (frame a k)) j)) = _
    rw [standard_swap]
    exact htrans _ _ hnext
  have hstep : (fun j => Matrix.mulVec (g * step a).val (frame a j)) =
      Function.update w i (x + y) ∘ e := by
    have heq : (fun j => Matrix.mulVec (g * step a).val (frame a j)) =
        (fun j => Matrix.mulVec g.val (Matrix.mulVec (step a).val (frame a j))) := by
      funext j
      exact Matrix.mulVec_mulVec _ _ _ |>.symm
    rw [heq]
    change (fun j => Matrix.mulVec g.val ((fun k => Matrix.mulVec (step a).val (frame a k)) j)) = _
    rw [standard_step]
    apply htrans
    rw [Matrix.mulVec_add, hnext, hframe l, hel]
    simp only [wx, Function.update_self]
  have eval (k : Group) (u : BinaryFrame a)
      (hk : (fun j => Matrix.mulVec k.val (frame a j)) = u ∘ e) :
      orbitValue ρ a v (exteriorPower.ιMulti (ZMod 2) (degree a) u) = ρ k v := by
    have hext : exteriorAction (degree a) k (seed a) =
        exteriorPower.ιMulti (ZMod 2) (degree a) u := by
      rw [seed, exteriorAction_ιMulti, hk]
      exact wedge_swap a u i l
    rw [← hext]
    exact orbitValue_on_orbit ρ a v hv k
  rw [eval g wx (funext hframe), eval (g * swap a) _ hswap,
    eval (g * step a) _ hstep]
  have h := congrArg (fun z => ρ g z) hv.2
  simpa only [map_add, map_zero, map_mul, Module.End.mul_apply] using h

/-- Stabilizer invariance and the standard binary Grassmann-line relation
extend a seed to a Grassmann assignment. -/
public theorem grassmannAssignment_of_seed
    (ρ : Representation (ZMod 2) Group V) (a : Fin 2) (v : V)
    (hv : HasExteriorSeed ρ a v) : Nonempty (GrassmannAssignment ρ a v) := by
  refine ⟨{
    value := fun w => orbitValue ρ a v (exteriorPower.ιMulti (ZMod 2) (degree a) w)
    zero_dependent := ?_
    equal_span := ?_
    line := orbitValue_line ρ a v hv
    frame_value := ?_
    equivariant := ?_ }⟩
  · intro w hw
    rw [AlternatingMap.map_linearDependent _ _ hw, orbitValue_zero]
  · intro w w' hw hw' hspan
    rw [wedge_equal_span a w w' hw hw' hspan]
  · have h := orbitValue_on_orbit ρ a v hv 1
    simpa only [map_one, Module.End.one_apply, seed] using h
  · intro g w
    rw [← exteriorAction_ιMulti]
    exact orbitValue_equivariant ρ a v hv g _

end Representation.SL5TenDimensional.Classification
