module
public import Mathlib.GroupTheory.IsPerfect
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.CommutatorRank
/-!
# Displacement across a central section of a perfect group

Suppose an invariant subspace has trivial quotient and maps onto a module
with fixed kernel. Vanishing of first cohomology of that module and its dual
shows that each group element displaces no more of the full space than of the
section. The first vanishing supplies a fixed supplement; the dual vanishing
makes the section map injective on commutators.

This is the extension step used for the alternating-five restriction in
Aschbacher–Smith B.5.13 (printed p.110), using I.1.6(1) (printed p.408).
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace Representation.OneCohomology
variable {D U Q : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Q] [Module (ZMod 2) Q]
  {σ : Representation (ZMod 2) D U} {τ : Representation (ZMod 2) D Q}
private theorem central_kernel_H1 [Group.IsPerfect D]
    (p : σ.IntertwiningMap τ) (hs : Function.Surjective p)
    (hc : p.toLinearMap.ker ≤ σ.invariants) [Subsingleton (H1 τ)] :
    Subsingleton (H1 σ) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro f _
  let cf : cocycles τ := ⟨fun g => p (f.val g), fun g h => by
    change p (f.val (g*h)) = τ g (p (f.val h)) + p (f.val g)
    rw [f.property, map_add, p.isIntertwining]⟩
  obtain ⟨q, hq⟩ := (classMap_eq_zero_iff τ cf).mp (Subsingleton.elim _ _)
  obtain ⟨u, rfl⟩ := hs q
  let d := f - principal σ u
  have hd (g : D) : d.val g ∈ σ.invariants := by
    apply hc
    have he := congrArg (fun c : cocycles τ => c.val g) hq
    change τ g (p u) - p u = p (f.val g) at he
    change p (f.val g - (σ g u - u)) = 0
    rw [map_sub, map_sub, p.isIntertwining, he, sub_self]
  let h : D →* Multiplicative U :=
    { toFun := fun g => Multiplicative.ofAdd (d.val g)
      map_one' := by
        change d.val 1 = 0
        have he := d.property 1 1
        simpa using he
      map_mul' := fun g t => by
        change d.val (g*t) = d.val g + d.val t
        rw [d.property, hd t g, add_comm] }
  let : Group.IsPerfect h.range := Group.IsPerfect.range h
  have hz (g : D) : d.val g = 0 := by
    have he : (⟨h g, g, rfl⟩ : h.range) = 1 := Subsingleton.elim _ _
    exact congrArg (fun x : h.range => Multiplicative.toAdd x.val) he
  refine ⟨u, ?_⟩
  apply Subtype.ext
  funext g
  exact (sub_eq_zero.mp (hz g)).symm

private theorem range_H1 (i : σ.IntertwiningMap τ) (hi : Function.Injective i)
    [Subsingleton (H1 σ)] : Subsingleton (H1 i.range.toRepresentation) := by
  let l : U ≃ₗ[ZMod 2] i.range.toSubmodule := LinearEquiv.ofInjective i.toLinearMap hi
  have hl (g : D) (v : U) : l (σ g v) = i.range.toRepresentation g (l v) :=
    Subtype.ext (i.isIntertwining σ τ g v)
  exact (H1Congr σ i.range.toRepresentation (MulEquiv.refl D) l hl).symm.injective.subsingleton

private theorem range_fixed_supplement (i : σ.IntertwiningMap τ)
    (hi : Function.Injective i) (ht : HasTrivialQuotient i.range)
    [Subsingleton (H1 σ)] (v : Q) :
    ∃ u : U, ∃ z : Q, z ∈ τ.invariants ∧ i u + z = v := by
  let := range_H1 i hi
  have hv := (extensionClass_eq_zero_iff i.range ht v).mp (Subsingleton.elim _ _)
  obtain ⟨_, ⟨u,rfl⟩, z, hz, he⟩ := Submodule.mem_sup.mp hv
  exact ⟨u,z,hz,he⟩

private theorem central_kernel_disjoint
    (p : σ.IntertwiningMap τ) (hs : Function.Surjective p)
    (hc : p.toLinearMap.ker ≤ σ.invariants) [Subsingleton (H1 τ.dual)] :
    Disjoint (Coinvariants.ker σ) p.toLinearMap.ker := by
  let i : τ.dual.IntertwiningMap σ.dual := dualIntertwining p
  have ht : HasTrivialQuotient i.range := by
    intro g f
    change σ.dual g f - f ∈ p.toLinearMap.dualMap.range
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro w hw
    change f (σ g⁻¹ w) - f w = 0
    rw [(hc hw) g⁻¹, sub_self]
  rw [Submodule.disjoint_def]
  intro x hx hk
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) x).mp
  intro f
  obtain ⟨b,z,hz,rfl⟩ := range_fixed_supplement (σ := τ.dual) (τ := σ.dual) i
    (LinearMap.dualMap_injective_of_surjective (f := p.toLinearMap) hs) ht f
  have hz' : z ∈ (Coinvariants.ker σ).dualAnnihilator := by
    rw [← σ.invariants_dual_eq_commutator_annihilator]
    exact hz
  change b (p x) + z x = 0
  have hzx : z x = 0 := by
    rw [Submodule.mem_dualAnnihilator] at hz'
    exact hz' x hx
  rw [show p x = 0 from hk, map_zero, hzx, add_zero]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) Q]
  {ρ : Representation (ZMod 2) D V}

/-- A central section with vanishing first cohomology controls full displacement. -/
theorem fixedCodim_central_section_le [Group.IsPerfect D]
    (U : Subrepresentation ρ) (ht : HasTrivialQuotient U)
    (p : U.toRepresentation.IntertwiningMap τ) (hs : Function.Surjective p)
    (hc : p.toLinearMap.ker ≤ U.toRepresentation.invariants)
    [Subsingleton (H1 τ)] [Subsingleton (H1 τ.dual)] (t : D) :
    fixedCodim ρ (zpowers t) ≤ fixedCodim τ (zpowers t) := by
  let := central_kernel_H1 p hs hc
  have hsup : U.toSubmodule ⊔ fixedSpace ρ (zpowers t) = ⊤ := by
    apply top_unique
    intro v _
    have hv := (extensionClass_eq_zero_iff U ht v).mp (Subsingleton.elim _ _)
    have hle : Representation.OneCohomology.fixed ρ ≤ fixedSpace ρ (zpowers t) :=
      fun w hw a => hw a.val
    exact (sup_le_sup_left hle U.toSubmodule) hv
  rw [← (fixedCodim_subrepresentation_eq_iff ρ U (zpowers t)).mpr hsup,
    fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank]
  let f : LinearMap.range (U.toRepresentation t - LinearMap.id) →ₗ[ZMod 2]
      LinearMap.range (τ t - LinearMap.id) :=
    { toFun := fun v => ⟨p v, by
        obtain ⟨w,hw⟩ := v.property
        refine ⟨p w, ?_⟩
        change τ t (p w) - p w = p v
        rw [← p.isIntertwining, ← map_sub]
        exact congrArg p hw⟩
      map_add' := by intros; apply Subtype.ext; exact map_add p _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul p _ _ }
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro v hv
  have hz : p v = 0 := congrArg Subtype.val hv
  have hm : (v : U.toSubmodule) ∈ Coinvariants.ker U.toRepresentation := by
    obtain ⟨w,hw⟩ := v.property
    rw [← hw]
    exact Coinvariants.sub_mem_ker t w
  exact Subtype.ext (Submodule.disjoint_def.mp (central_kernel_disjoint p hs hc)
    v hm hz)
end Representation.OneCohomology
