module

public import Theory.Representation.SubspaceQuotient
public import Theory.Combinatorics.ProjectivePlaneThreeAction
public import Theory.Combinatorics.ProjectivePlaneThreeCoordinates
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Geometric principal-degree candidates for PSL₃(3)

The canonical matrix action on PG(2,3) gives a twelve-dimensional point
augmentation module. The incidence boundary on the fifty-two flags has image
exactly the pairs of vertex vectors with equal sums: paths of length at most
three put every pair of endpoints in its image. Rank-nullity therefore gives
a twenty-seven-dimensional kernel. In characteristic two the constant flag
vector is a nonzero fixed cycle, and quotienting its line gives dimension
twenty-six. Both actual actions are transported to the requested function spaces.

These are constructions and dimension proofs, not simplicity assertions.
Their two irreducibility obligations are kept separate from this geometry.
The source application is Guralnick--Malle, *Classification of 2F-modules I*,
Proposition 4.2, manuscript pp.9--10. The characteristic-two L₃(3)
decomposition matrix lists principal-block degrees 1, 12 and 26; no table
completeness or block-membership assertion is used in these constructions.
-/

@[expose] public section

open scoped BigOperators
open Configuration
namespace Representation.PSL3Three.AbsoluteDegrees.PrincipalModels

abbrev PG := Configuration.PlaneThree.PG
abbrev Group := Matrix.PSL3Three.PSL
noncomputable instance : DecidableEq PG := Classical.decEq _
noncomputable instance : Fintype PG := Fintype.ofFinite PG

lemma card_points : Fintype.card PG = 13 := by
  rw [← Nat.card_eq_fintype_card]
  exact Configuration.Three.card_pg

abbrev Flag := {z : PG × PG // z.1 ∈ z.2}
noncomputable instance : Fintype Flag := Fintype.ofFinite Flag

noncomputable def flagsOverLines : Flag ≃ Σ l : PG, {p : PG // p ∈ l} where
  toFun f := ⟨f.val.2, f.val.1, f.property⟩
  invFun f := ⟨(f.2.val, f.1), f.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_flags : Fintype.card Flag = 52 := by
  classical
  rw [Fintype.card_congr flagsOverLines, Fintype.card_sigma]
  have h (l : PG) : Fintype.card {p : PG // p ∈ l} = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact Configuration.Three.pointCount_pg l
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, card_points]

/-- The canonical projective point action of the literal matrix quotient. -/
noncomputable def pointPerm : Group →* Equiv.Perm PG :=
  (Collineation.pointHom PG PG).comp Configuration.PlaneThree.pslCollineation
/-- The inverse-transpose action on line covectors. -/
noncomputable def linePerm : Group →* Equiv.Perm PG :=
  (Collineation.lineHom PG PG).comp Configuration.PlaneThree.pslCollineation

lemma incident_action (g : Group) (p l : PG) :
    pointPerm g p ∈ linePerm g l ↔ p ∈ l :=
  Collineation.mem_iff _ _ _

/-- The paired action on actual incident point-line pairs. -/
noncomputable def flagPerm : Group →* Equiv.Perm Flag where
  toFun g :=
    { toFun f := ⟨(pointPerm g f.val.1, linePerm g f.val.2),
        (incident_action g _ _).mpr f.property⟩
      invFun f := ⟨(pointPerm g⁻¹ f.val.1, linePerm g⁻¹ f.val.2),
        (incident_action g⁻¹ _ _).mpr f.property⟩
      left_inv f := by apply Subtype.ext; simp [map_inv]
      right_inv f := by apply Subtype.ext; simp [map_inv] }
  map_one' := by ext f <;> simp
  map_mul' g h := by ext f <;> simp

variable (F : Type*) [Field F]

noncomputable def permutation {X : Type*} (π : Group →* Equiv.Perm X) :
    Representation F Group (X → F) where
  toFun g := (LinearEquiv.funCongrLeft F F (π g).symm).toLinearMap
  map_one' := by ext v x; simp only [map_one]; rfl
  map_mul' g h := by ext v x; simp only [map_mul]; rfl

@[simp] lemma permutation_apply {X : Type*} (π : Group →* Equiv.Perm X)
    (g : Group) (v : X → F) (x : X) : permutation F π g v x = v ((π g).symm x) := rfl

noncomputable def augmentation : (PG → F) →ₗ[F] F where
  toFun v := ∑ p, v p
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' _ _ := by simp [Finset.mul_sum]

/-- The augmentation subrepresentation of the thirteen-point action. -/
noncomputable def pointCore : Subrepresentation (permutation F pointPerm) where
  toSubmodule := (augmentation F).ker
  apply_mem_toSubmodule g v hv := by
    change (∑ p, v ((pointPerm g).symm p)) = 0
    rw [Equiv.sum_comp]
    exact hv

lemma finrank_pointCore : Module.finrank F (pointCore F).toSubmodule = 12 := by
  classical
  have hs : Function.Surjective (augmentation F) := by
    intro a
    exact ⟨Pi.single (Configuration.PlaneThree.frame 0) a, by simp [augmentation]⟩
  have h := (augmentation F).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at h
  simp only [finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, card_points] at h
  change Module.finrank F (LinearMap.ker (augmentation F)) = 12
  omega

noncomputable def vertexRepresentation :=
  (permutation F pointPerm).prod (permutation F linePerm)

noncomputable def endpoint (p l : PG) : (PG → F) × (PG → F) :=
  (Pi.single p 1, Pi.single l 1)

noncomputable def boundaryLinear : (Flag → F) →ₗ[F] ((PG → F) × (PG → F)) where
  toFun a := ∑ f : Flag, a f • endpoint F f.val.1 f.val.2
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_smul, Finset.smul_sum]

lemma endpoint_action (g : Group) (p l : PG) :
    vertexRepresentation F g (endpoint F p l) =
      endpoint F (pointPerm g p) (linePerm g l) := by
  classical
  apply Prod.ext <;> funext x <;>
    simp [vertexRepresentation, endpoint, Representation.prod, Pi.single_apply,
      _root_.Equiv.symm_apply_eq]

/-- The unsigned incidence boundary, sending each flag to its two endpoints. -/
noncomputable def boundary :
    (permutation F flagPerm).IntertwiningMap (vertexRepresentation F) where
  toLinearMap := boundaryLinear F
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    change (∑ f : Flag, a ((flagPerm g).symm f) • endpoint F f.val.1 f.val.2) =
      vertexRepresentation F g (∑ f : Flag, a f • endpoint F f.val.1 f.val.2)
    rw [← Equiv.sum_comp (flagPerm g) (fun f : Flag =>
      a ((flagPerm g).symm f) • endpoint F f.val.1 f.val.2)]
    simp only [_root_.Equiv.symm_apply_apply, map_sum, map_smul, endpoint_action]
    rfl

/-- The literal kernel of the equivariant incidence boundary. -/
noncomputable def cycleSpace : Subrepresentation (permutation F flagPerm) :=
  (boundary F).ker

lemma boundary_single (f : Flag) :
    boundary F (Pi.single f 1) = endpoint F f.val.1 f.val.2 := by
  classical
  change (∑ k, (Pi.single f (1 : F) : Flag → F) k • endpoint F k.val.1 k.val.2) = _
  simp [Pi.single_apply]


/-- A path of length at most three places every pair of endpoints in the range. -/
lemma endpoint_mem_range (p l : PG) : endpoint F p l ∈ (boundaryLinear F).range := by
  classical
  have he (p l : PG) (h : p ∈ l) : endpoint F p l ∈ (boundaryLinear F).range :=
    ⟨Pi.single ⟨(p,l), h⟩ 1, boundary_single F ⟨(p,l), h⟩⟩
  have hc : 0 < Nat.card {q : PG // q ∈ l} := by
    change 0 < pointCount PG l
    rw [Configuration.Three.pointCount_pg]
    decide
  obtain ⟨q, hq⟩ := (Nat.card_pos_iff.mp hc).1
  by_cases hp : p = q
  · subst p
    exact he q l hq
  · let m : PG := HasLines.mkLine hp
    have hm : p ∈ m ∧ q ∈ m := HasLines.mkLine_ax hp
    have h := (boundaryLinear F).range.add_mem
      ((boundaryLinear F).range.sub_mem (he p m hm.1) (he q m hm.2)) (he q l hq)
    have hid : endpoint F p m - endpoint F q m + endpoint F q l = endpoint F p l := by
      apply Prod.ext <;> simp [endpoint]
    rwa [hid] at h

noncomputable def balance : ((PG → F) × (PG → F)) →ₗ[F] F :=
  (augmentation F).comp (LinearMap.fst F _ _) -
    (augmentation F).comp (LinearMap.snd F _ _)

@[simp] lemma balance_endpoint (p l : PG) : balance F (endpoint F p l) = 0 := by
  classical
  simp [balance, augmentation, endpoint]

/-- The image consists precisely of pairs with equal total coefficient sums. -/
lemma boundary_range : (boundaryLinear F).range = (balance F).ker := by
  classical
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    change balance F (∑ f : Flag, a f • endpoint F f.val.1 f.val.2) = 0
    simp only [map_sum, map_smul, balance_endpoint, smul_zero, Finset.sum_const_zero]
  · intro w hw
    let p₀ : PG := Configuration.PlaneThree.frame 0
    let l₀ : PG := Configuration.PlaneThree.frame 1
    have hs : (∑ p, w.1 p) = ∑ l, w.2 l := sub_eq_zero.mp hw
    have hp := (boundaryLinear F).range.sum_mem (fun p (_ : p ∈ Finset.univ) =>
      (boundaryLinear F).range.smul_mem (w.1 p) (endpoint_mem_range F p l₀))
    have hl := (boundaryLinear F).range.sum_mem (fun l (_ : l ∈ Finset.univ) =>
      (boundaryLinear F).range.smul_mem (w.2 l) (endpoint_mem_range F p₀ l))
    have hc := (boundaryLinear F).range.smul_mem (∑ p, w.1 p)
      (endpoint_mem_range F p₀ l₀)
    have h := (boundaryLinear F).range.sub_mem ((boundaryLinear F).range.add_mem hp hl) hc
    have hid : (∑ p, w.1 p • endpoint F p l₀) + (∑ l, w.2 l • endpoint F p₀ l) -
        (∑ p, w.1 p) • endpoint F p₀ l₀ = w := by
      apply Prod.ext
      · simp only [Prod.fst_sub, Prod.fst_add, Prod.fst_sum, Prod.smul_fst, endpoint]
        change (∑ p, w.1 p • Pi.single p 1) + (∑ l, w.2 l • Pi.single p₀ 1) -
          (∑ p, w.1 p) • Pi.single p₀ 1 = w.1
        rw [← Finset.sum_smul, hs, add_sub_cancel_right]
        ext p
        simp [Pi.single_apply]
      · simp only [Prod.snd_sub, Prod.snd_add, Prod.snd_sum, Prod.smul_snd, endpoint]
        change (∑ p, w.1 p • Pi.single l₀ 1) + (∑ l, w.2 l • Pi.single l 1) -
          (∑ p, w.1 p) • Pi.single l₀ 1 = w.2
        rw [← Finset.sum_smul, add_sub_cancel_left]
        ext l
        simp [Pi.single_apply]
    rwa [hid] at h

lemma finrank_cycleSpace : Module.finrank F (cycleSpace F).toSubmodule = 27 := by
  classical
  have hs : Function.Surjective (balance F) := by
    intro a
    refine ⟨(Pi.single (Configuration.PlaneThree.frame 0) a, 0), ?_⟩
    simp [balance, augmentation]
  have h := (balance F).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at h
  simp only [finrank_top, Module.finrank_self, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card, card_points] at h
  have hb := (boundaryLinear F).finrank_range_add_finrank_ker
  rw [boundary_range] at hb
  simp only [Module.finrank_fintype_fun_eq_card, card_flags] at hb
  change Module.finrank F (boundaryLinear F).ker = 27
  omega


noncomputable def flagsOverPoints : Flag ≃ Σ p : PG, {l : PG // p ∈ l} where
  toFun f := ⟨f.val.1, f.val.2, f.property⟩
  invFun f := ⟨(f.1, f.2.val), f.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_linesThrough (p : PG) : Nat.card {l : PG // p ∈ l} = 4 := by
  change lineCount PG p = 4
  rw [ProjectivePlane.lineCount_eq_pointCount p p]
  exact Configuration.Three.pointCount_pg p

lemma boundary_constant : boundary F (fun _ => 1) = ((fun _ => 4), (fun _ => 4)) := by
  classical
  have hp (p : PG) : (∑ f : Flag, (Pi.single f.val.1 (1 : F) : PG → F) p) = 4 := by
    rw [← _root_.Equiv.sum_comp flagsOverPoints.symm]
    simp only [Fintype.sum_sigma]
    change (∑ q : PG, ∑ _l : {l : PG // q ∈ l}, (Pi.single q (1 : F)) p) = 4
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_linesThrough]
    simp [Pi.single_apply]
  have hl (l : PG) : (∑ f : Flag, (Pi.single f.val.2 (1 : F) : PG → F) l) = 4 := by
    rw [← _root_.Equiv.sum_comp flagsOverLines.symm]
    simp only [Fintype.sum_sigma]
    change (∑ m : PG, ∑ _p : {p : PG // p ∈ m}, (Pi.single m (1 : F)) l) = 4
    have hc (m : PG) : Nat.card {p : PG // p ∈ m} = 4 := Configuration.Three.pointCount_pg m
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hc]
    simp [Pi.single_apply]
  apply Prod.ext
  · funext p
    simpa [boundary, boundaryLinear, endpoint, Prod.fst_sum] using hp p
  · funext l
    simpa [boundary, boundaryLinear, endpoint, Prod.snd_sum] using hl l

variable [CharP F 2]

/-- Four flags meet each vertex, so the constant flag vector is a binary cycle. -/
noncomputable def constantCycle : (cycleSpace F).toSubmodule :=
  ⟨fun _ => 1, by
    change boundary F (fun _ => 1) = 0
    rw [boundary_constant]
    have h : (4 : F) = 0 := (CharP.cast_eq_zero_iff F 2 4).mpr (by decide)
    apply Prod.ext <;> funext p <;> exact h⟩

lemma constantCycle_ne_zero : constantCycle F ≠ 0 := by
  intro h
  have hc : 0 < Fintype.card Flag := by rw [card_flags]; decide
  obtain ⟨f⟩ := Fintype.card_pos_iff.mp hc
  have hh := congrArg (fun v : (cycleSpace F).toSubmodule => v.val f) h
  exact one_ne_zero hh

lemma constantCycle_fixed (g : Group) :
    (cycleSpace F).toRepresentation g (constantCycle F) = constantCycle F := by
  apply Subtype.ext
  funext f
  rfl

/-- The fixed constant line inside the actual incidence kernel. -/
noncomputable def constantLine : Subrepresentation (cycleSpace F).toRepresentation where
  toSubmodule := Submodule.span F {constantCycle F}
  apply_mem_toSubmodule g v hv := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, constantCycle_fixed]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- Quotient of the cycle space by its constant line, retaining both subspaces. -/
abbrev CycleQuotient := (cycleSpace F).toSubmodule ⧸ (constantLine F).toSubmodule

lemma finrank_cycleQuotient : Module.finrank F (CycleQuotient F) = 26 := by
  have hc : Module.finrank F (constantLine F).toSubmodule = 1 :=
    finrank_span_singleton (constantCycle_ne_zero F)
  have h := (constantLine F).toSubmodule.finrank_quotient_add_finrank
  rw [hc, finrank_cycleSpace] at h
  change Module.finrank F (CycleQuotient F) + 1 = 27 at h
  omega

noncomputable def pointCoordinates : (pointCore F).toSubmodule ≃ₗ[F] (Fin 12 → F) :=
  (Module.finBasisOfFinrankEq F _ (finrank_pointCore F)).equivFun

noncomputable def cycleCoordinates : CycleQuotient F ≃ₗ[F] (Fin 26 → F) :=
  (Module.finBasisOfFinrankEq F _ (finrank_cycleQuotient F)).equivFun

/-- The point augmentation model transported to twelve coordinates. -/
noncomputable def degree12 : Representation F Group (Fin 12 → F) :=
  (pointCoordinates F).conjRingEquiv.toMonoidHom.comp (pointCore F).toRepresentation

/-- The incidence cycle quotient transported to twenty-six coordinates. -/
noncomputable def degree26 : Representation F Group (Fin 26 → F) :=
  (cycleCoordinates F).conjRingEquiv.toMonoidHom.comp (constantLine F).quotientRepresentation



@[simp] lemma pointPerm_apply (g : Group) (p : PG) : pointPerm g p = g • p :=
  Configuration.PlaneThree.pslCollineation_point g p

@[simp] lemma linePerm_project (A : Matrix.PSL3Three.SL) (l : PG) :
    linePerm (Matrix.PSL3Three.project A) l =
      Matrix.SpecialLinearGroup.inverseTranspose A • l :=
  Configuration.PlaneThree.pslCollineation_line A l

/-- Coordinates intertwine the actual point-core action with `degree12`. -/
noncomputable def pointCoreEquiv : (pointCore F).toRepresentation.Equiv (degree12 F) := by
  refine Representation.Equiv.mk (pointCoordinates F) ?_
  intro g
  apply LinearMap.ext
  intro v
  change pointCoordinates F ((pointCore F).toRepresentation g v) =
    pointCoordinates F ((pointCore F).toRepresentation g
      ((pointCoordinates F).symm (pointCoordinates F v)))
  rw [LinearEquiv.symm_apply_apply]

/-- Coordinates intertwine the literal cycle quotient with `degree26`. -/
noncomputable def cycleQuotientEquiv :
    (constantLine F).quotientRepresentation.Equiv (degree26 F) := by
  refine Representation.Equiv.mk (cycleCoordinates F) ?_
  intro g
  apply LinearMap.ext
  intro v
  change cycleCoordinates F ((constantLine F).quotientRepresentation g v) =
    cycleCoordinates F ((constantLine F).quotientRepresentation g
      ((cycleCoordinates F).symm (cycleCoordinates F v)))
  rw [LinearEquiv.symm_apply_apply]

end Representation.PSL3Three.AbsoluteDegrees.PrincipalModels
