module

public import Theory.Mathieu.M12.SmallParabolicPair.CoverOrbitData
public import Theory.Mathieu.M12.Properties.InvolutionFusion

/-!
# The five marked cubic orbits in the concrete M₁₂ core

The two checked quaternion embeddings descend to binary plane coordinates.
The right plane uses a rotated basis so that the simultaneous cubic action
has exactly the source's fusion marking: the first two mixed orbits are
noncentral involutions and the third consists of central involutions.
The coordinate kernel is the actual core center, and the two coordinate axes
are precisely the marked quaternion factors. Squares and permutation support
sizes are checked on the two eight-element domains. Exhaustive involution
fusion then supplies conjugacy in the Witt-design M₁₂ itself.

Source: Aschbacher–Smith, I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

@[expose] public section
open Subgroup Theory.LinearAlgebra.BinaryCubicOrbits
namespace Sporadic.Mathieu.M12SmallPair.CoverOrbits
noncomputable section
abbrev Q := QuaternionGroup 2
set_option maxRecDepth 100000

def leftPlane : Q →* Multiplicative Plane where
  toFun
    | .a n => Multiplicative.ofAdd (n.val, 0)
    | .xa n => Multiplicative.ofAdd (n.val, 1)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def rightPlane : Q →* Multiplicative Plane where
  toFun
    | .a n => Multiplicative.ofAdd (n.val, n.val)
    | .xa n => Multiplicative.ofAdd (n.val + 1, n.val)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def pairCoordinates : Q × Q →* Multiplicative Space where
  toFun x := Multiplicative.ofAdd ((leftPlane x.1).toAdd, (rightPlane x.2).toAdd)
  map_one' := by
    change Multiplicative.ofAdd ((leftPlane 1).toAdd, (rightPlane 1).toAdd) = 1
    rw [leftPlane.map_one, rightPlane.map_one]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd ((leftPlane (x.1 * y.1)).toAdd,
      (rightPlane (x.2 * y.2)).toAdd) = _
    rw [leftPlane.map_mul, rightPlane.map_mul]
    rfl

def pairEmbedding : Q × Q →* core where
  toFun x := ⟨leftEmbedding x.1 * rightEmbedding x.2,
    (mem_core _).mpr ⟨x.1,x.2,rfl⟩⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change leftEmbedding (x.1 * y.1) * rightEmbedding (x.2 * y.2) =
      (leftEmbedding x.1 * rightEmbedding x.2) * (leftEmbedding y.1 * rightEmbedding y.2)
    rw [map_mul, map_mul]
    have h := factors_commute (leftEmbedding y.1) ⟨y.1,rfl⟩ (rightEmbedding x.2) ⟨x.2,rfl⟩
    calc
      _ = leftEmbedding x.1 * (leftEmbedding y.1 * rightEmbedding x.2) * rightEmbedding y.2 := by group
      _ = _ := by rw [h]; group

theorem pairEmbedding_surjective : Function.Surjective pairEmbedding := by
  intro r
  obtain ⟨q,s,h⟩ := (mem_core r.val).mp r.property
  exact ⟨(q,s), Subtype.ext h⟩

theorem pair_kernel : pairEmbedding.ker ≤ pairCoordinates.ker := by
  have h : ∀ q r : Q, leftEmbedding q * rightEmbedding r = 1 →
    pairCoordinates (q,r) = 1 := by decide +kernel
  intro x hx
  exact h x.1 x.2 (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))

def coordinates : core →* Multiplicative Space :=
  pairEmbedding.liftOfSurjective pairEmbedding_surjective ⟨pairCoordinates,pair_kernel⟩

theorem coordinates_pair (q r : Q) :
    coordinates (pairEmbedding (q,r)) = pairCoordinates (q,r) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem coordinates_surjective : Function.Surjective coordinates := by
  have h : Function.Surjective pairCoordinates := by decide +kernel
  intro v
  obtain ⟨⟨q,r⟩,he⟩ := h v
  exact ⟨pairEmbedding (q,r),(coordinates_pair q r).trans he⟩

theorem coordinates_ker : coordinates.ker = center core := by
  ext r
  obtain ⟨⟨q,s⟩,rfl⟩ := pairEmbedding_surjective r
  rw [MonoidHom.mem_ker, coordinates_pair, core_center_mem]
  have h : ∀ q s : Q, pairCoordinates (q,s) = 1 ↔
    leftEmbedding q * rightEmbedding s = 1 ∨ leftEmbedding q * rightEmbedding s = z := by
    decide +kernel
  exact h q s

theorem left_axis (r : core) :
    r ∈ coreQuaternionData.left ↔ (coordinates r).toAdd.2 = 0 := by
  obtain ⟨⟨q,s⟩,rfl⟩ := pairEmbedding_surjective r
  rw [coordinates_pair]
  change (∃ t, leftEmbedding t = leftEmbedding q * rightEmbedding s) ↔ _
  have h : ∀ q s : Q, (∃ t, leftEmbedding t = leftEmbedding q * rightEmbedding s) ↔
    (pairCoordinates (q,s)).toAdd.2 = 0 := by decide +kernel
  exact h q s

theorem right_axis (r : core) :
    r ∈ coreQuaternionData.right ↔ (coordinates r).toAdd.1 = 0 := by
  obtain ⟨⟨q,s⟩,rfl⟩ := pairEmbedding_surjective r
  rw [coordinates_pair]
  change (∃ t, rightEmbedding t = leftEmbedding q * rightEmbedding s) ↔ _
  have h : ∀ q s : Q, (∃ t, rightEmbedding t = leftEmbedding q * rightEmbedding s) ↔
    (pairCoordinates (q,s)).toAdd.1 = 0 := by decide +kernel
  exact h q s

def quaternionCubic : Q → Q
  | .a n => ![.a 0, .xa 2, .a 2, .xa 0] n
  | .xa n => ![.xa 3, .a 1, .xa 1, .a 3] n

theorem cubic_pair (q s : Q) :
    residualCoreAction residualCubic (pairEmbedding (q,s)) =
      pairEmbedding (quaternionCubic q, quaternionCubic s) := by
  apply Subtype.ext
  rw [residualCoreAction_cubic]
  have hl : ∀ q : Q, cubicActor * leftEmbedding q * cubicActor⁻¹ =
    leftEmbedding (quaternionCubic q) := by decide +kernel
  have hr : ∀ q : Q, cubicActor * rightEmbedding q * cubicActor⁻¹ =
    rightEmbedding (quaternionCubic q) := by decide +kernel
  change cubicActor * (leftEmbedding q * rightEmbedding s) * cubicActor⁻¹ =
    leftEmbedding (quaternionCubic q) * rightEmbedding (quaternionCubic s)
  rw [← hl, ← hr]
  group

theorem cubic_equivariance (r : core) :
    (coordinates (residualCoreAction residualCubic r)).toAdd = cubic (coordinates r).toAdd := by
  obtain ⟨⟨q,s⟩,rfl⟩ := pairEmbedding_surjective r
  rw [cubic_pair, coordinates_pair, coordinates_pair]
  have h : ∀ q s : Q, (pairCoordinates (quaternionCubic q, quaternionCubic s)).toAdd =
    cubic (pairCoordinates (q,s)).toAdd := by decide +kernel
  exact h q s

theorem square_mark (r : core) :
    (r : M12)^2 = z ↔ quaternionSquare (coordinates r).toAdd = 1 := by
  obtain ⟨⟨q,s⟩,rfl⟩ := pairEmbedding_surjective r
  rw [coordinates_pair]
  have h : ∀ q s : Q, (leftEmbedding q * rightEmbedding s)^2 = z ↔
    quaternionSquare (pairCoordinates (q,s)).toAdd = 1 := by decide +kernel
  exact h q s

theorem orbit_order (j : Fin 5) (k : Fin 3) (r : core)
    (hr : (coordinates r).toAdd = orbit j k) :
    orderOf (r : M12) = if j = 3 ∨ j = 4 then 4 else 2 := by
  have hn : (r : M12) ≠ 1 := by
    intro he
    have hr1 : r = 1 := Subtype.ext he
    rw [hr1, map_one] at hr
    have h : ∀ j k, orbit j k ≠ 0 := by decide +kernel
    exact h j k hr.symm
  have hs := (core_center_mem (r^2)).mp (coreQuaternionData.square_mem_center r)
  change (r : M12)^2 = 1 ∨ (r : M12)^2 = z at hs
  split_ifs with hj
  · have hz : (r : M12)^2 = z := (square_mark r).mpr (by
      rw [hr, quaternionSquare_orbit, if_pos hj])
    have hz1 : z ≠ 1 := by decide +kernel
    have h4 : (r : M12)^(2^(1+1)) = 1 := by
      change (r : M12)^(2*2) = 1
      rw [pow_mul, hz]
      exact (orderOf_eq_prime_iff.mp z_order).1
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa [hz] using hz1) h4
  · apply orderOf_eq_prime ?_ hn
    exact hs.resolve_right (fun hz => by
      have h := (square_mark r).mp hz
      rw [hr, quaternionSquare_orbit, if_neg hj] at h
      exact (by decide : (0 : ZMod 2) ≠ 1) h)

theorem support_eq_of_isConj {x y : M12} (h : IsConj x y) :
    x.val.support.card = y.val.support.card := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  have he := congrArg (fun x : M12 => x.val.support.card) hg
  change (g.val * x.val * g.val⁻¹).support.card = y.val.support.card at he
  simpa only [Equiv.Perm.card_support_conj] using he

theorem central_fusion_of_support (x : M12) (hx : orderOf x = 2)
    (hs : x.val.support.card = 8) : IsConj z x := by
  rcases M12InvolutionFusion.marked_fusion x hx with h | h
  · exact h
  · have he := support_eq_of_isConj h
    have ht : third.val.support.card = 12 := by decide +kernel
    rw [ht,hs] at he
    omega

theorem noncentral_fusion_of_support (x : M12) (hx : orderOf x = 2)
    (hs : x.val.support.card = 12) : IsConj third x := by
  rcases M12InvolutionFusion.marked_fusion x hx with h | h
  · have he := support_eq_of_isConj h
    have ht : z.val.support.card = 8 := by decide +kernel
    rw [ht,hs] at he
    omega
  · exact h

theorem central_fusion (k : Fin 3) (r : core)
    (hr : (coordinates r).toAdd = orbit 2 k) : IsConj z (r : M12) := by
  apply central_fusion_of_support _ (by simpa using orbit_order 2 k r hr)
  obtain ⟨⟨q,s⟩,rfl⟩ := pairEmbedding_surjective r
  rw [coordinates_pair] at hr
  have h : ∀ q s : Q, ∀ k : Fin 3, (pairCoordinates (q,s)).toAdd = orbit 2 k →
    (leftEmbedding q * rightEmbedding s).val.support.card = 8 := by decide +kernel
  exact h q s k hr

theorem noncentral_fusion (j : Fin 5) (k : Fin 3) (r : core)
    (hj : j = 0 ∨ j = 1) (hr : (coordinates r).toAdd = orbit j k) : IsConj third (r : M12) := by
  have hne : ¬ (j = 3 ∨ j = 4) := by rcases hj with rfl | rfl <;> decide
  apply noncentral_fusion_of_support _ (by simpa only [if_neg hne] using orbit_order j k r hr)
  obtain ⟨⟨q,s⟩,rfl⟩ := pairEmbedding_surjective r
  rw [coordinates_pair] at hr
  have h : ∀ q s : Q, ∀ j : Fin 5, ∀ k : Fin 3, j = 0 ∨ j = 1 →
    (pairCoordinates (q,s)).toAdd = orbit j k →
    (leftEmbedding q * rightEmbedding s).val.support.card = 12 := by decide +kernel
  exact h q s j k hj hr

end
end Sporadic.Mathieu.M12SmallPair.CoverOrbits
