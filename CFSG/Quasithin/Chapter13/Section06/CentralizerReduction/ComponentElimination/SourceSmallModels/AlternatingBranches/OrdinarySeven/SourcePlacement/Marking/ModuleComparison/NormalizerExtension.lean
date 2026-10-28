module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.Summand
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.Representation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Action
public import Theory.Representation.BinaryPermutation.SevenCommutant
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.LinearAlgebra.RegularLinearAction

/-!
# Extend the chosen natural summand to its normalizing actor

The given A₇ summand is the component commutator space and its complementary
kernel is the component fixed space. Relative normality makes both invariant.
In their prescribed coordinates, the full action conjugates the alternating
action just as the given permutation homomorphism does. The genuine scalar
commutant of the natural A₇ module forces these two actions to agree. The
binary complementary kernel has dimension at most one, so its action is trivial.
Thus the extension preserves the supplied inclusion and projection exactly.

The final applications use the literal W₀ representation and K⁺ subgroup,
with normality and the ordinary permutation action supplied by Marking.Action.
The component splitting and its kernel bound are explicit inputs to be
constructed by the source assembly owner. This is the normalizer-extension
step, not an assertion that B.3.3's splitting has already been constructed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.3.3(1),
printed p.84/PDF p.95, and 13.6.22, printed p.932/PDF p.949.
-/

@[expose] public section
open Subgroup Equiv Representation
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
namespace NormalizerExtension
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) H V} {φ : H →* Perm (Fin 7)} {B : Subgroup H}
  (d : NaturalSummand (ρ.comp B.subtype) (φ.comp B.subtype))
  (hB : B.map φ = alternatingGroup (Fin 7))
local notation "N" => BinaryPermutation.natural (Fin 7)
local notation "σ" => BinaryPermutation.naturalRepresentation (Fin 7)
include hB

/-- The given complementary kernel is exactly the component fixed space. -/
theorem kernel_eq_fixedSpace : d.projection.ker = fixedSpace ρ B := by
  ext x
  constructor
  · intro hx b
    have h := d.remainder_fixed b x
    change ρ b.val (x - d.inclusion (d.projection x)) = x - d.inclusion (d.projection x) at h
    change d.projection x = 0 at hx
    change ρ b.val x = x
    simpa only [hx, map_zero, sub_zero] using h
  · intro hx
    apply BinaryPermutation.SevenCommutant.fixed_eq_zero
    intro g
    obtain ⟨b, hb, hbg⟩ := (show g.val ∈ B.map φ from hB.symm ▸ g.property)
    have he := d.projection_equivariant ⟨b, hb⟩ x
    change d.projection (ρ b x) = σ (φ b) (d.projection x) at he
    rw [show ρ b x = x from hx ⟨b, hb⟩, hbg] at he
    exact he.symm

/-- The given natural image is exactly the component commutator space. -/
theorem range_eq_commutator : d.inclusion.range = subspaceCommutator ρ ⊤ B := by
  apply le_antisymm
  · have hn : (⊤ : Submodule (ZMod 2) N) ≤
        (subspaceCommutator ρ ⊤ B).comap d.inclusion := by
      rw [← BinaryPermutation.SevenCommutant.commutator_eq_top]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, w, _, rfl⟩
      obtain ⟨b, hb, rfl⟩ := (show g ∈ B.map φ from hB.symm ▸ hg)
      change d.inclusion (σ (φ b) w - w) ∈ subspaceCommutator ρ ⊤ B
      have he := d.inclusion_equivariant ⟨b, hb⟩ w
      change ρ b (d.inclusion w) = d.inclusion (σ (φ b) w) at he
      rw [map_sub, ← he]
      exact Submodule.subset_span ⟨b, hb, d.inclusion w, Submodule.mem_top, rfl⟩
    rintro _ ⟨w, rfl⟩
    exact hn Submodule.mem_top
  · apply Submodule.span_le.mpr
    rintro _ ⟨b, hb, x, _, rfl⟩
    have hr := d.remainder_fixed ⟨b, hb⟩ x
    change ρ b (x - d.inclusion (d.projection x)) = x - d.inclusion (d.projection x) at hr
    rw [map_sub] at hr
    have he := d.inclusion_equivariant ⟨b, hb⟩ (d.projection x)
    change ρ b (d.inclusion (d.projection x)) = d.inclusion (σ (φ b) (d.projection x)) at he
    rw [he] at hr
    refine ⟨σ (φ b) (d.projection x) - d.projection x, ?_⟩
    rw [map_sub]
    exact (sub_eq_sub_iff_sub_eq_sub.mp hr).symm

variable [B.Normal]

/-- Relative normality preserves the component fixed space. -/
theorem kernel_stable : (⊤ : Subgroup H) ≤ subspaceStabilizer ρ d.projection.ker := by
  rw [kernel_eq_fixedSpace d hB]
  exact fixedSpace_stable_of_normal ρ B

/-- Relative normality preserves the component commutator space. -/
theorem range_stable : (⊤ : Subgroup H) ≤ subspaceStabilizer ρ d.inclusion.range := by
  rw [range_eq_commutator d hB]
  apply subspaceCommutator_invariant_normalizer
  · exact le_subspaceStabilizer ρ ⊤ (fun _ _ _ _ => Submodule.mem_top)
  · rw [Subgroup.normalizer_eq_top]

private theorem inclusion_projection_action (h : H) (x : N) :
    d.inclusion (d.projection (ρ h (d.inclusion x))) = ρ h (d.inclusion x) := by
  have hm := (range_stable d hB (mem_top h) (d.inclusion x)).2 ⟨x, rfl⟩
  obtain ⟨w, hw⟩ := hm
  rw [← hw, d.retraction]

/-- The actual action on the characteristic natural summand, in its given coordinates. -/
def naturalAction : Representation (ZMod 2) H N where
  toFun h := d.projection.comp ((ρ h).comp d.inclusion)
  map_one' := by
    apply LinearMap.ext
    intro x
    change d.projection (ρ 1 (d.inclusion x)) = x
    rw [map_one, Module.End.one_apply, d.retraction]
  map_mul' h k := by
    apply LinearMap.ext
    intro x
    change d.projection (ρ (h * k) (d.inclusion x)) =
      d.projection (ρ h (d.inclusion (d.projection (ρ k (d.inclusion x)))))
    rw [inclusion_projection_action d hB, map_mul, Module.End.mul_apply]

private theorem naturalAction_component (b : B) : naturalAction d hB b.val = σ (φ b.val) := by
  apply LinearMap.ext
  intro x
  change d.projection (ρ b.val (d.inclusion x)) = σ (φ b.val) x
  have he := d.inclusion_equivariant b x
  change ρ b.val (d.inclusion x) = d.inclusion (σ (φ b.val) x) at he
  rw [he, d.retraction]

/-- Conjugation compatibility and the scalar commutant force precisely the original φ. -/
theorem naturalAction_eq (h : H) : naturalAction d hB h = σ (φ h) := by
  let R := naturalAction d hB
  let f : N →ₗ[ZMod 2] N := σ (φ h⁻¹) * R h
  have hcancel (x : N) : σ (φ h) (f x) = R h x := by
    change σ (φ h) (σ (φ h⁻¹) (R h x)) = R h x
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel,
      map_one, map_one, Module.End.one_apply]
  have hinj : Function.Injective f := by
    intro x y he
    have hh := congrArg (fun z => R h⁻¹ (σ (φ h) z)) he
    rw [hcancel, hcancel] at hh
    simpa only [← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply] using hh
  have hf : ∀ g : alternatingGroup (Fin 7), ∀ x,
      f (σ g.val x) = σ g.val (f x) := by
    intro g x
    obtain ⟨b, hb, hbg⟩ := (show g.val ∈ B.map φ from hB.symm ▸ g.property)
    have hc : h * b * h⁻¹ ∈ B := (inferInstance : B.Normal).conj_mem b hb h
    have he : R (h * b * h⁻¹) = σ (φ (h * b * h⁻¹)) :=
      naturalAction_component d hB ⟨_, hc⟩
    have heb : R b = σ (φ b) := naturalAction_component d hB ⟨b, hb⟩
    change σ (φ h⁻¹) (R h (σ g.val x)) = σ g.val (σ (φ h⁻¹) (R h x))
    have hm : R h (R b x) = R (h * b * h⁻¹) (R h x) := by
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    calc
      _ = σ (φ h⁻¹) (R h (R b x)) := by rw [heb, hbg]
      _ = σ (φ h⁻¹) (σ (φ (h * b * h⁻¹)) (R h x)) := by rw [hm, he]
      _ = σ (φ b) (σ (φ h⁻¹) (R h x)) := by
        have hp : φ h⁻¹ * φ (h * b * h⁻¹) = φ b * φ h⁻¹ := by
          simp only [map_mul, map_inv]
          group
        rw [← Module.End.mul_apply, ← map_mul, hp, map_mul, Module.End.mul_apply]
      _ = _ := by rw [hbg]
  have he := BinaryPermutation.SevenCommutant.commuting_eq_id f hinj hf
  apply LinearMap.ext
  intro x
  have hh : σ (φ h) (f x) = σ (φ h) x :=
    congrArg (fun q : N →ₗ[ZMod 2] N => σ (φ h) (q x)) he
  rw [hcancel] at hh
  exact hh

private theorem inclusion_equivariant (h : H) (x : N) :
    ρ h (d.inclusion x) = d.inclusion (σ (φ h) x) := by
  rw [← naturalAction_eq d hB h]
  exact (inclusion_projection_action d hB h x).symm

variable [FiniteDimensional (ZMod 2) V]

private theorem kernel_fixed (hd : Module.finrank (ZMod 2) d.projection.ker ≤ 1)
    (h : H) (x : V) (hx : x ∈ d.projection.ker) : ρ h x = x := by
  let e : d.projection.ker ≃ₗ[ZMod 2] d.projection.ker :=
    { toLinearMap := (ρ h).restrict (fun {v} hv => (kernel_stable d hB (mem_top h) v).2 hv)
      invFun y := ⟨ρ h⁻¹ y, (kernel_stable d hB (mem_top h⁻¹) y).2 y.property⟩
      left_inv y := by
        apply Subtype.ext
        change ρ h⁻¹ (ρ h y.val) = y.val
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv y := by
        apply Subtype.ext
        change ρ h (ρ h⁻¹ y.val) = y.val
        simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }
  have he := LinearGroup.eq_one_of_binary_finrank_le_one hd e
  exact congrArg (fun q : d.projection.ker ≃ₗ[ZMod 2] d.projection.ker => (q ⟨x, hx⟩).val) he

/-- Extend the supplied component splitting, preserving both of its linear maps. -/
noncomputable def extend (hd : Module.finrank (ZMod 2) d.projection.ker ≤ 1) :
    NaturalSummand ρ φ where
  inclusion := d.inclusion
  projection := d.projection
  retraction := d.retraction
  inclusion_equivariant := by exact inclusion_equivariant d hB
  projection_equivariant h x := by
    have hm : x - d.inclusion (d.projection x) ∈ d.projection.ker := by
      change d.projection (x - d.inclusion (d.projection x)) = 0
      rw [map_sub, d.retraction, sub_self]
    have he := kernel_fixed d hB hd h _ hm
    have hp := congrArg d.projection he
    rw [map_sub, inclusion_equivariant d hB, map_sub, d.retraction,
      map_sub, d.retraction, sub_self] at hp
    exact sub_eq_zero.mp hp
  remainder_fixed h x := by
    apply kernel_fixed d hB hd h
    change d.projection (x - d.inclusion (d.projection x)) = 0
    rw [map_sub, d.retraction, sub_self]

@[simp] theorem extend_inclusion (hd : Module.finrank (ZMod 2) d.projection.ker ≤ 1) :
    (extend d hB hd).inclusion = d.inclusion := rfl
@[simp] theorem extend_projection (hd : Module.finrank (ZMod 2) d.projection.ker ≤ 1) :
    (extend d hB hd).projection = d.projection := rfl
end NormalizerExtension
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison

open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
variable {G : Type*} [Group G] [Finite G]

/-- Apply the extension to the literal plus quotient and W₀ representation.
The supplied splitting and its kernel bound remain the component-splitting
owner's inputs; relative normality is discharged here. -/
noncomputable def extend_plus
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hφB : (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7))
    (d : NaturalSummand ((representation K L T z v hL hz hWT).comp
      (plusImage K L T z v hL hz K).subtype)
      (φ.comp (plusImage K L T z v hL hz K).subtype))
    (hd : Module.finrank (ZMod 2) d.projection.ker ≤ 1) :
    NaturalSummand (representation K L T z v hL hz hWT) φ := by
  let := component_image_normal K L T z v hL hz hn hLv
  let : Module.Finite (ZMod 2) (Additive (Carrier K L T z v)) := Module.Finite.of_finite
  exact NormalizerExtension.extend d hφB hd

/-- Choose the source-compatible action, then extend any supplied component
splitting in those same coordinates. The output is the actual input to
`NaturalSummand.fixedCodim_eq` and `fixed_centralizer_le_thompson`.
Neither fixed codimensions nor a centralizer conclusion is assumed. -/
theorem ordinary_extension_exists
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (hY : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hblock : ChapterC.IsAlternatingBlock K 7) :
    ∃ φ : Gplus K L T z v hL hz →* Perm (Fin 7), Function.Injective φ ∧
      (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7) ∧
      (∀ k : K,
        φ (plusMk K L T z v hL hz
          ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
            (blockProjection K (ordinaryQuotientEquiv K hblock) k : Perm (Fin 7))) ∧
      ∀ d : NaturalSummand ((representation K L T z v hL hz hWT).comp
          (plusImage K L T z v hL hz K).subtype)
          (φ.comp (plusImage K L T z v hL hz K).subtype),
        Module.finrank (ZMod 2) d.projection.ker ≤ 1 →
        ∃ D : NaturalSummand (representation K L T z v hL hz hWT) φ,
          D.inclusion = d.inclusion ∧ D.projection = d.projection := by
  obtain ⟨φ, hφ, hφB, hcoord⟩ := ordinary_action_exists K L T z v hL hz hn hLv hY hR hblock
  refine ⟨φ, hφ, hφB, hcoord, fun d hd => ?_⟩
  exact ⟨extend_plus K L T z v hL hz hn hLv hWT φ hφB d hd, rfl, rfl⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
