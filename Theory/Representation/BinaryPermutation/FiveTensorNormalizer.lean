module

public import Theory.Representation.BinaryPermutation.ThreeTensor
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Alternating.Aut
public import Theory.Representation.BinaryPermutation.FiveTensorTransvections

/-!
# Normalizer and centralizer of the binary A₅ tensor action

The point-stabilizer fixed line and its five translates show that every
A₅-equivariant endomorphism of the four-dimensional augmentation core is scalar.
The four blocks of an equivariant map on two copies are therefore binary scalars;
invertibility identifies their matrix with the three-point permutation action.
Thus the tensor centralizer is the second S₃ factor. Aut(A₅) = S₅ then
identifies every normalizing map with a unique pair in S₅ × S₃. The
centralizer of the full marked A₅ × S₃ action is trivial.

The point-vector calculation refines the automorphism calculation of
`BinaryAlternatingFiveNormalizer` to arbitrary endomorphisms. Source:
Aschbacher–Smith, the tensor step in 13.8.20, printed p.954.
-/

public section
open TensorProduct Representation
namespace BinaryPermutation.FiveTensorNormalizer

private def weightFour (i : Fin 5) : Full (Fin 5) := fun k => if k = i then 0 else 1

private theorem weightFour_mem : ∀ i, weightFour i ∈ core (Fin 5) := by
  change ∀ i, ∑ k, weightFour i k = 0
  decide +kernel

private def corePoint (i : Fin 5) : core (Fin 5) := ⟨weightFour i, weightFour_mem i⟩

private def cycleA : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 1 3
private def cycleB : Equiv.Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 2 4

private theorem cycles_even :
    cycleA ∈ alternatingGroup (Fin 5) ∧ cycleB ∈ alternatingGroup (Fin 5) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem cycles_fix :
    coreRepresentation (Fin 5) cycleA (corePoint 0) = corePoint 0 ∧
    coreRepresentation (Fin 5) cycleB (corePoint 0) = corePoint 0 := by
  constructor <;> apply Subtype.ext <;> decide +kernel

private theorem cycles_fixed (v : core (Fin 5))
    (ha : coreRepresentation (Fin 5) cycleA v = v)
    (hb : coreRepresentation (Fin 5) cycleB v = v) : v = 0 ∨ v = corePoint 0 := by
  have h : ∀ v : Full (Fin 5), (∑ k, v k) = 0 →
      (∀ k, v (cycleA.symm k) = v k) → (∀ k, v (cycleB.symm k) = v k) →
      v = 0 ∨ v = weightFour 0 := by decide +kernel
  rcases h v v.property (fun k => congrArg (fun u : core (Fin 5) => u.val k) ha)
    (fun k => congrArg (fun u : core (Fin 5) => u.val k) hb) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

private def pointMover (i : Fin 5) : Equiv.Perm (Fin 5) :=
  ![1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2, Equiv.swap 0 4 * Equiv.swap 1 2] i

private theorem pointMover_even : ∀ i, pointMover i ∈ alternatingGroup (Fin 5) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem pointMover_apply (i : Fin 5) :
    coreRepresentation (Fin 5) (pointMover i) (corePoint 0) = corePoint i := by
  apply Subtype.ext
  exact (show ∀ i, representation (Fin 5) (pointMover i) (weightFour 0) =
    weightFour i by decide +kernel) i

private theorem corePoint_generate (v : core (Fin 5)) :
    v = 0 ∨ (∃ i, v = corePoint i) ∨ (∃ i j, v = corePoint i + corePoint j) := by
  have h : ∀ v : Full (Fin 5), (∑ k, v k) = 0 →
      v = 0 ∨ (∃ i, v = weightFour i) ∨ (∃ i j, v = weightFour i + weightFour j) := by
    decide +kernel
  rcases h v v.property with h | ⟨i, h⟩ | ⟨i, j, h⟩
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl ⟨i, Subtype.ext h⟩)
  · exact Or.inr (Or.inr ⟨i, j, Subtype.ext h⟩)

/-- Absolute scalar commutant of the natural binary A₅ core. -/
theorem core_commuting_scalar (f : core (Fin 5) →ₗ[ZMod 2] core (Fin 5))
    (hf : ∀ g : alternatingGroup (Fin 5), ∀ v,
      f (alternatingCoreRepresentation (Fin 5) g v) =
        alternatingCoreRepresentation (Fin 5) g (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  have ha := (hf ⟨cycleA, cycles_even.1⟩ (corePoint 0)).symm
  have hb := (hf ⟨cycleB, cycles_even.2⟩ (corePoint 0)).symm
  change coreRepresentation (Fin 5) cycleA (f (corePoint 0)) =
    f (coreRepresentation (Fin 5) cycleA (corePoint 0)) at ha
  change coreRepresentation (Fin 5) cycleB (f (corePoint 0)) =
    f (coreRepresentation (Fin 5) cycleB (corePoint 0)) at hb
  rw [cycles_fix.1] at ha
  rw [cycles_fix.2] at hb
  have hz : ∃ c : ZMod 2, f (corePoint 0) = c • corePoint 0 := by
    rcases cycles_fixed (f (corePoint 0)) ha hb with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨c, hc⟩ := hz
  have hp (i : Fin 5) : f (corePoint i) = c • corePoint i := by
    rw [← pointMover_apply i]
    rw [show f (coreRepresentation (Fin 5) (pointMover i) (corePoint 0)) =
      coreRepresentation (Fin 5) (pointMover i) (f (corePoint 0)) from
      hf ⟨pointMover i, pointMover_even i⟩ (corePoint 0), hc, map_smul]
  refine ⟨c, fun v => ?_⟩
  rcases corePoint_generate v with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · simp only [map_zero, smul_zero]
  · exact hp i
  · rw [map_add, hp, hp, smul_add]

private theorem pair_coefficients : ∀ a b c d : ZMod 2,
    (∀ x y : ZMod 2, a*x+b*y = 0 → c*x+d*y = 0 → x = 0 ∧ y = 0) →
    ∃ h : Equiv.Perm (Fin 3), ∀ n : Full (Fin 3), (∑ i, n i) = 0 →
      n (h.symm 0) = a * n 0 + b * n 1 ∧
      n (h.symm 1) = c * n 0 + d * n 1 := by
  decide +kernel

/-- The four blocks of an A₅-equivariant map on two copies are binary scalars. -/
theorem pair_commuting_blocks
    (f : (core (Fin 5) × core (Fin 5)) →ₗ[ZMod 2] (core (Fin 5) × core (Fin 5)))
    (hf : ∀ (g : alternatingGroup (Fin 5)) (u v : core (Fin 5)),
      f (alternatingCoreRepresentation (Fin 5) g u,
        alternatingCoreRepresentation (Fin 5) g v) =
      (alternatingCoreRepresentation (Fin 5) g (f (u,v)).1,
        alternatingCoreRepresentation (Fin 5) g (f (u,v)).2)) :
    ∃ a b c d : ZMod 2, ∀ u v, f (u,v) = (a • u + b • v, c • u + d • v) := by
  let p := LinearMap.fst (ZMod 2) (core (Fin 5)) (core (Fin 5))
  let q := LinearMap.snd (ZMod 2) (core (Fin 5)) (core (Fin 5))
  let i := LinearMap.inl (ZMod 2) (core (Fin 5)) (core (Fin 5))
  let j := LinearMap.inr (ZMod 2) (core (Fin 5)) (core (Fin 5))
  obtain ⟨a, ha⟩ := core_commuting_scalar (p.comp (f.comp i)) (by
    intro g v
    simpa [p, i] using congrArg Prod.fst (hf g v 0))
  obtain ⟨b, hb⟩ := core_commuting_scalar (p.comp (f.comp j)) (by
    intro g v
    simpa [p, j] using congrArg Prod.fst (hf g 0 v))
  obtain ⟨c, hc⟩ := core_commuting_scalar (q.comp (f.comp i)) (by
    intro g v
    simpa [q, i] using congrArg Prod.snd (hf g v 0))
  obtain ⟨d, hd⟩ := core_commuting_scalar (q.comp (f.comp j)) (by
    intro g v
    simpa [q, j] using congrArg Prod.snd (hf g 0 v))
  refine ⟨a, b, c, d, fun u v => ?_⟩
  have hadd : f (u,v) = f (u,0) + f (0,v) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using f.map_add (u,0) (0,v)
  rw [hadd]
  exact Prod.ext (congrArg₂ (· + ·) (ha u) (hb v))
    (congrArg₂ (· + ·) (hc u) (hd v))

/-- Every invertible map commuting with A₅ on the first tensor factor is a
three-point permutation on the second factor. -/
theorem tensor_centralizer
    (f : (core (Fin 5) ⊗[ZMod 2] core (Fin 3)) ≃ₗ[ZMod 2]
      (core (Fin 5) ⊗[ZMod 2] core (Fin 3)))
    (hf : ∀ (g : alternatingGroup (Fin 5)) v,
      f (ThreeTensor.action (coreRepresentation (Fin 5)) (g.val,1) v) =
        ThreeTensor.action (coreRepresentation (Fin 5)) (g.val,1) (f v)) :
    ∃ h : Equiv.Perm (Fin 3), ∀ v,
      f v = ThreeTensor.action (coreRepresentation (Fin 5)) (1,h) v := by
  let e := ThreeTensor.pairEquiv (V := core (Fin 5))
  let F := e.symm.trans (f.trans e)
  have hF (g : alternatingGroup (Fin 5)) (u v : core (Fin 5)) :
      F (alternatingCoreRepresentation (Fin 5) g u,
        alternatingCoreRepresentation (Fin 5) g v) =
      (alternatingCoreRepresentation (Fin 5) g (F (u,v)).1,
        alternatingCoreRepresentation (Fin 5) g (F (u,v)).2) := by
    have he := ThreeTensor.pairEquiv_equivariant (coreRepresentation (Fin 5)) g.val
      (e.symm (u,v))
    change e (ThreeTensor.action (coreRepresentation (Fin 5)) (g.val,1) (e.symm (u,v))) =
      ((coreRepresentation (Fin 5)).prod (coreRepresentation (Fin 5))) g.val
        (e (e.symm (u,v))) at he
    rw [e.apply_symm_apply] at he
    change e (ThreeTensor.action (coreRepresentation (Fin 5)) (g.val,1) (e.symm (u,v))) =
      (alternatingCoreRepresentation (Fin 5) g u,
        alternatingCoreRepresentation (Fin 5) g v) at he
    change e (f (e.symm _)) = _
    rw [← he, e.symm_apply_apply, hf]
    exact ThreeTensor.pairEquiv_equivariant (coreRepresentation (Fin 5)) g.val _
  obtain ⟨a,b,c,d,hblocks⟩ := pair_commuting_blocks F.toLinearMap hF
  change ∀ u v, F (u,v) = (a • u + b • v, c • u + d • v) at hblocks
  have hker (x y : ZMod 2) (hxy : a*x+b*y = 0) (hxy' : c*x+d*y = 0) :
      x = 0 ∧ y = 0 := by
    have hh : F (x • corePoint 0, y • corePoint 0) = F 0 := by
      rw [hblocks, map_zero]
      simp only [smul_smul, ← add_smul, hxy, hxy', zero_smul, Prod.zero_eq_mk]
    have hzero := F.injective hh
    constructor
    · have hx := congrArg (fun z : core (Fin 5) × core (Fin 5) => z.1.val 1) hzero
      simpa [corePoint, weightFour] using hx
    · have hy := congrArg (fun z : core (Fin 5) × core (Fin 5) => z.2.val 1) hzero
      simpa [corePoint, weightFour] using hy
  obtain ⟨h, hh⟩ := pair_coefficients a b c d hker
  refine ⟨h, fun v => ?_⟩
  apply e.injective
  have hFe (v) : e (f v) = F (e v) := by simp only [F, LinearEquiv.trans_apply,
    e.symm_apply_apply]
  rw [hFe]
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul u n =>
    rw [ThreeTensor.action_tmul]
    simp only [map_one, Module.End.one_apply]
    change F (ThreeTensor.pairEquiv (u ⊗ₜ[ZMod 2] n)) =
      ThreeTensor.pairEquiv (u ⊗ₜ[ZMod 2] coreRepresentation (Fin 3) h n)
    rw [ThreeTensor.pairEquiv_tmul, ThreeTensor.pairEquiv_tmul]
    change F (n.val 0 • u, n.val 1 • u) =
      ((coreRepresentation (Fin 3) h n).val 0 • u,
        (coreRepresentation (Fin 3) h n).val 1 • u)
    rw [hblocks]
    obtain ⟨h0,h1⟩ := hh n.val n.property
    change (a • n.val 0 • u + b • n.val 1 • u,
      c • n.val 0 • u + d • n.val 1 • u) = (n.val (h.symm 0) • u, n.val (h.symm 1) • u)
    rw [h0, h1]
    simp only [smul_smul, add_smul]
  | add u v hu hv => simpa only [map_add] using congrArg₂ (· + ·) hu hv

/-- Faithfulness of the full permutation tensor action. -/
theorem tensor_faithful :
    Function.Injective (ThreeTensor.action (coreRepresentation (Fin 5))) := by
  let ρ := ThreeTensor.action (coreRepresentation (Fin 5))
  have hk (p : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) (hp : ρ p = 1) : p = 1 := by
    apply FiveTensorTransvections.eq_one_of_displacement_le_one (MulEquiv.refl _) ρ
      (LinearEquiv.refl _ _) (fun _ _ => rfl) p
    have hz : ρ p - LinearMap.id = 0 := by
      change ρ p - 1 = 0
      rw [hp, sub_self]
    have : Subsingleton (LinearMap.range (ρ p - LinearMap.id)) := by
      rw [hz, LinearMap.range_zero]
      infer_instance
    simp only [Module.finrank_zero_of_subsingleton, Nat.zero_le]
  intro p q hpq
  apply mul_inv_eq_one.mp
  apply hk
  change ρ p = ρ q at hpq
  rw [map_mul, hpq, ← map_mul, mul_inv_cancel, map_one]

/-- An automorphism normalizing the marked tensor A₅ action is a pair of
coordinate permutations. The automorphism of A₅ is arbitrary and is realized
using Aut(A₅) = S₅; full equivariance is the conclusion. -/
theorem tensor_normalizer
    (f : (core (Fin 5) ⊗[ZMod 2] core (Fin 3)) ≃ₗ[ZMod 2]
      (core (Fin 5) ⊗[ZMod 2] core (Fin 3)))
    (φ : MulAut (alternatingGroup (Fin 5)))
    (hf : ∀ (g : alternatingGroup (Fin 5)) v,
      f (ThreeTensor.action (coreRepresentation (Fin 5)) (g.val,1) v) =
        ThreeTensor.action (coreRepresentation (Fin 5)) ((φ g).val,1) (f v)) :
    ∃ p : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3), ∀ v,
      f v = ThreeTensor.action (coreRepresentation (Fin 5)) p v := by
  let ρ := ThreeTensor.action (coreRepresentation (Fin 5))
  obtain ⟨σ, hσ⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
      (by decide) (by decide)).surjective φ
  let t : _ ≃ₗ[ZMod 2] _ := LinearEquiv.ofBijective (ρ (σ⁻¹,1)) (ρ.apply_bijective _)
  let F := f.trans t
  have hconj (g : alternatingGroup (Fin 5)) : (φ g).val = σ * g.val * σ⁻¹ := by
    rw [← hσ]
    rfl
  have hF (g : alternatingGroup (Fin 5)) v :
      F (ρ (g.val,1) v) = ρ (g.val,1) (F v) := by
    change ρ (σ⁻¹,1) (f (ρ (g.val,1) v)) = ρ (g.val,1) (ρ (σ⁻¹,1) (f v))
    rw [hf, hconj]
    change ρ (σ⁻¹,1) (ρ (σ * g.val * σ⁻¹,1) (f v)) =
      ρ (g.val,1) (ρ (σ⁻¹,1) (f v))
    simp only [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [mul_assoc, inv_mul_cancel_left]
  obtain ⟨h, hh⟩ := tensor_centralizer F hF
  refine ⟨(σ,h), fun v => ?_⟩
  have he := congrArg (ρ (σ,1)) (hh v)
  change ρ (σ,1) (ρ (σ⁻¹,1) (f v)) = ρ (σ,1) (ρ (1,h) v) at he
  simpa only [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel,
    one_mul, mul_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply] using he

/-- The full marked A₅ × S₃ action has trivial linear centralizer. -/
theorem tensor_joint_centralizer
    (f : (core (Fin 5) ⊗[ZMod 2] core (Fin 3)) ≃ₗ[ZMod 2]
      (core (Fin 5) ⊗[ZMod 2] core (Fin 3)))
    (hf : ∀ (g : alternatingGroup (Fin 5)) v,
      f (ThreeTensor.action (coreRepresentation (Fin 5)) (g.val,1) v) =
        ThreeTensor.action (coreRepresentation (Fin 5)) (g.val,1) (f v))
    (hs : ∀ (s : Equiv.Perm (Fin 3)) v,
      f (ThreeTensor.action (coreRepresentation (Fin 5)) (1,s) v) =
        ThreeTensor.action (coreRepresentation (Fin 5)) (1,s) (f v)) :
    f = LinearEquiv.refl (ZMod 2) _ := by
  obtain ⟨h, hh⟩ := tensor_centralizer f hf
  have hc (s : Equiv.Perm (Fin 3)) : h * s = s * h := by
    have he : ThreeTensor.action (coreRepresentation (Fin 5)) ((1,h) * (1,s)) =
        ThreeTensor.action (coreRepresentation (Fin 5)) ((1,s) * (1,h)) := by
      apply LinearMap.ext
      intro v
      simp only [map_mul, Module.End.mul_apply]
      rw [← hh, ← hh, hs]
    exact congrArg Prod.snd (tensor_faithful he)
  have h1 : h = 1 := by
    have hcenter : ∀ h : Equiv.Perm (Fin 3), (∀ s, h*s = s*h) → h = 1 := by
      decide +kernel
    exact hcenter h hc
  ext v
  simpa only [h1, ← Prod.one_eq_mk, map_one, Module.End.one_apply,
    LinearEquiv.refl_apply] using hh v

/-- Uniqueness of the coordinate permutations produced by the normalizer theorem. -/
theorem tensor_coordinates_unique
    (p q : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))
    (h : ∀ v, ThreeTensor.action (coreRepresentation (Fin 5)) p v =
      ThreeTensor.action (coreRepresentation (Fin 5)) q v) : p = q :=
  tensor_faithful (LinearMap.ext h)

end BinaryPermutation.FiveTensorNormalizer
end
