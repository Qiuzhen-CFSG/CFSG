module
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.Representation.Unbundled
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.GroupTheory.IsPerfect
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Faithfulness of a natural self-extension of a perfect SL₃ cover

A faithful binary representation of a perfect central cover of SL₃(F), with
both an invariant subspace and its quotient naturally marked by the same
covering map, has trivial covering kernel. Choose a linear quotient section
and form its derivation. Multiplying its associated cocycle by any commuting
scalar and taking binary trace gives an additive character, hence zero by
perfectness. A central kernel element has scalar displacement by the natural
commutant calculation. The nondegenerate finite-field trace pairing detects
that scalar: the natural dimension is three, which is odd in characteristic
two. This works even when the field degree is even.

No splitting of the self-extension is asserted. The application is the
whole central-omega covering component in Aschbacher–Smith C.1.34, printed
pp.136–137, including the exceptional even multiplier at field four.
-/

public noncomputable section
open Representation
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
namespace Representation.PerfectSelfExtension

private theorem trace_derivation_eq_zero
    {k X W : Type*} [Field k] [Group X] [Group.IsPerfect X]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k X W) (d : X → Module.End k W)
    (hd : ∀ g h, d (g*h) = σ g * d h + d g * σ h)
    (a : Module.End k W) (ha : ∀ g, Commute a (σ g)) (g : X) :
    LinearMap.trace k W (a * d g * σ g⁻¹) = 0 := by
  let c (g : X) := d g * σ g⁻¹
  have hc (g h : X) : c (g*h) = σ g * c h * σ g⁻¹ + c g := by
    dsimp [c]
    rw [hd,mul_inv_rev,map_mul,add_mul]
    congr 1
    calc
      d g * σ h * (σ h⁻¹ * σ g⁻¹) = d g * (σ h * σ h⁻¹) * σ g⁻¹ := by
        noncomm_ring
      _ = d g * σ g⁻¹ := by rw [←map_mul,mul_inv_cancel,map_one,mul_one]
  have ht (g h : X) :
      LinearMap.trace k W (a * c (g*h)) =
        LinearMap.trace k W (a * c g) + LinearMap.trace k W (a * c h) := by
    rw [hc,mul_add,map_add,add_comm]
    congr 1
    calc
      LinearMap.trace k W (a * (σ g * c h * σ g⁻¹)) =
          LinearMap.trace k W ((σ g * (a * c h)) * σ g⁻¹) := by
        congr 1
        rw [←mul_assoc,←mul_assoc,(ha g).eq]
        noncomm_ring
      _ = LinearMap.trace k W (σ g⁻¹ * (σ g * (a * c h))) :=
        LinearMap.trace_mul_comm k _ _
      _ = LinearMap.trace k W (a * c h) := by
        rw [←mul_assoc,←map_mul,inv_mul_cancel,map_one,one_mul]
  let f : X →* Multiplicative k :=
    { toFun := fun x => Multiplicative.ofAdd (LinearMap.trace k W (a * c x))
      map_one' := by
        have hh := ht 1 1
        simp only [one_mul] at hh
        change LinearMap.trace k W (a * c 1) = 0
        exact add_eq_left.mp hh.symm
      map_mul' := ht }
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hh := Subsingleton.elim (f.rangeRestrict g) (1 : f.range)
  exact congrArg (fun x : f.range => Multiplicative.toAdd x.val) hh

private def scalar {F : Type*} [Field F] [Algebra (ZMod 2) F] (a : F) :
    Module.End (ZMod 2) (Fin 3 → F) :=
  (a • (LinearMap.id : Module.End F (Fin 3 → F))).restrictScalars (ZMod 2)

private theorem trace_scalar {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    (a : F) : LinearMap.trace (ZMod 2) (Fin 3 → F) (scalar a) =
      Algebra.trace (ZMod 2) F a := by
  let b := Module.Free.chooseBasis (ZMod 2) F
  rw [trace_pi_map_perm b (fun i : Fin 3 => i) (fun _ => Algebra.lmul (ZMod 2) F a)
    (scalar a) (by intro v i; rfl)]
  simp only [ite_true,Fin.sum_univ_three,←Algebra.trace_apply]
  rw [CharTwo.add_self_eq_zero,zero_add]

/-- Scalar endomorphisms of the natural three-space are detected by traces
against other scalar endomorphisms, even when the binary field degree is even. -/
private theorem scalar_eq_zero_of_trace {F : Type*} [Field F] [Finite F]
    [Algebra (ZMod 2) F] (c : F)
    (h : ∀ a : F, LinearMap.trace (ZMod 2) (Fin 3 → F) (scalar a * scalar c) = 0) :
    c = 0 := by
  apply (traceForm_nondegenerate (ZMod 2) F).1 c
  intro a
  rw [Algebra.traceForm_apply,mul_comm]
  have he : scalar a * scalar c = scalar (a*c) := by
    ext v i
    simp [scalar,mul_assoc]
  simpa only [he,trace_scalar] using h a

/-- A faithful natural self-extension of a perfect central cover of full SL₃
has trivial covering kernel. The proof uses scalar-weighted binary traces,
so no oddness assumption on the field degree or extension splitting is needed. -/
theorem natural_cover_injective
    {F X V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    [Group X] [Group.IsPerfect X] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (hρ : Function.Injective ρ)
    (π : X →* SL(3,F)) (hπ : Function.Surjective π)
    (hz : π.ker ≤ Subgroup.center X) (N : Subrepresentation ρ)
    (en : N.toRepresentation.Equiv
      (((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp π))
    (eq : N.quotientRepresentation.Equiv
      (((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp π)) :
    Function.Injective π := by
  classical
  let W := Fin 3 → F
  let σ := ((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp π
  let i : W →ₗ[ZMod 2] V := N.toSubmodule.subtype.comp en.symm.toLinearEquiv.toLinearMap
  let q : V →ₗ[ZMod 2] W := eq.toLinearEquiv.toLinearMap.comp N.toSubmodule.mkQ
  have hi : Function.Injective i := Subtype.val_injective.comp en.symm.toLinearEquiv.injective
  have hq : Function.Surjective q := eq.toLinearEquiv.surjective.comp N.toSubmodule.mkQ_surjective
  have hi_equiv (g : X) (w : W) : ρ g (i w) = i (σ g w) := by
    exact (congrArg Subtype.val (LinearMap.congr_fun (en.symm.isIntertwining' g) w)).symm
  have hq_equiv (g : X) (v : V) : q (ρ g v) = σ g (q v) := by
    exact LinearMap.congr_fun (eq.isIntertwining' g) (N.toSubmodule.mkQ v)
  have hqi (w : W) : q (i w) = 0 := by
    change eq (N.toSubmodule.mkQ (en.symm w).val) = 0
    rw [show N.toSubmodule.mkQ (en.symm w).val = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr (en.symm w).property, map_zero]
  have hqker (v : V) : q v = 0 ↔ v ∈ N.toSubmodule := by
    change eq.toLinearEquiv (N.toSubmodule.mkQ v) = 0 ↔ _
    rw [eq.toLinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  obtain ⟨j, hj⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqj (w : W) : q (j w) = w := LinearMap.congr_fun hj w
  let δ (g : X) : W →ₗ[ZMod 2] V := (ρ g).comp j - j.comp (σ g)
  have hδ (g : X) (w : W) : δ g w ∈ N.toSubmodule := by
    apply (hqker _).mp
    change q (ρ g (j w) - j (σ g w)) = 0
    rw [map_sub, hq_equiv, hqj, hqj, sub_self]
  let d (g : X) : Module.End (ZMod 2) W :=
    en.toLinearEquiv.toLinearMap.comp ((δ g).codRestrict N.toSubmodule (hδ g))
  have hid (g : X) (w : W) : i (d g w) = ρ g (j w) - j (σ g w) := by
    change (en.symm (en ⟨δ g w, hδ g w⟩)).val = _
    rw [en.symm_apply_apply]
    rfl
  have hd (g h : X) : d (g * h) = (σ g).comp (d h) + (d g).comp (σ h) := by
    apply LinearMap.ext
    intro w
    apply hi
    change i (d (g * h) w) = i (σ g (d h w) + d g (σ h w))
    rw [hid, map_add, ← hi_equiv, hid, hid, map_sub,
      map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    abel
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro z hzker
  change z = 1
  have hzσ : σ z = 1 := by
    change ((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)) (π z) = 1
    rw [show π z = 1 from hzker,map_one]
  have hcomm (g : X) : (d z) * σ g = σ g * (d z) := by
    have hh := congrArg d (Subgroup.mem_center_iff.mp (hz hzker) g)
    rw [hd,hd] at hh
    change σ g * d z + d g * σ z = σ z * d g + d z * σ g at hh
    rw [hzσ,mul_one,one_mul,add_comm] at hh
    exact (add_left_cancel hh).symm
  obtain ⟨c,hc⟩ := SL3OddNaturalNormalizer.centralizer_scalar (d z).toAddMonoidHom (by
    intro g w
    obtain ⟨x,rfl⟩ := hπ g
    exact LinearMap.congr_fun (hcomm x) w)
  have hdscalar : d z = scalar c := LinearMap.ext hc
  have hc0 : c = 0 := by
    apply scalar_eq_zero_of_trace c
    intro a
    have ha (g : X) : Commute (scalar a) (σ g) := by
      change scalar a * σ g = σ g * scalar a
      apply LinearMap.ext
      intro w
      exact (((specialLinearNatural (k := F) 3) (π g)).map_smul a w).symm
    have ht := trace_derivation_eq_zero σ d hd (scalar a) ha z
    have hzσinv : σ z⁻¹ = 1 := by
      calc
        σ z⁻¹ = σ z * σ z⁻¹ := by rw [hzσ,one_mul]
        _ = 1 := by rw [←map_mul,mul_inv_cancel,map_one]
    simpa only [hzσinv,mul_one,hdscalar] using ht
  have hdz : d z = 0 := by
    rw [hdscalar,hc0]
    ext v i
    simp [scalar]
  have hzi (w : W) : ρ z (i w) = i w := by
    rw [hi_equiv,hzσ,Module.End.one_apply]
  have hzj (w : W) : ρ z (j w) = j w := by
    have hh := hid z w
    rw [hdz,LinearMap.zero_apply,map_zero,hzσ,Module.End.one_apply] at hh
    exact sub_eq_zero.mp hh.symm
  apply hρ
  rw [map_one]
  apply LinearMap.ext
  intro v
  have hv : v - j (q v) ∈ N.toSubmodule := by
    apply (hqker _).mp
    rw [map_sub,hqj,sub_self]
  have hdecomp : v = i (en ⟨v-j (q v),hv⟩) + j (q v) := by
    change v = (en.symm (en ⟨v-j (q v),hv⟩)).val + j (q v)
    rw [en.symm_apply_apply]
    exact (sub_add_cancel v (j (q v))).symm
  change ρ z v = v
  conv_lhs => rw [hdecomp,map_add,hzi,hzj]
  exact hdecomp.symm

end Representation.PerfectSelfExtension
