module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Action
public import Theory.Representation.BinaryOffender.Embedding
public import Theory.Representation.PSL3Two.DoubledOffenders.Model

/-!
# Transport from the actual W_K to its doubled submodule U_K

The supplied full action intertwines with the literal inclusion U_K ≤ W_K,
viewed inside the actual plus actor. Every best offender on W_K is consequently
an offender on the doubled module. An element fixing C_W_K(A) also fixes
C_U_K(A), so the full-Sylow model calculation bounds its image. Conversely,
each element of A fixes its own centralizer, giving the literal equality
required by B.2.20 with the full inverse image of A under plusMk.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.20,
printed p.82; the central branch of 13.6.20, printed p.931.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
open ComponentSelection ModuleAlternatives
variable {G : Type*} [Group G] [Finite G] {K L T : Subgroup G} {z v : G}
variable {e : EarlierData K L T z v}
variable {d : DoubledCoordinates K L T z v e.selected.1.1 e.normalizeL e.fixSeed}
namespace ExtendedCoordinates
variable (c : ExtendedCoordinates e d)
/-- The marked U_K included in the elementary group W_K inside the actual actor. -/
noncomputable def moduleInclusion (_c : ExtendedCoordinates e d) : (BinaryLinearThree.Vector × BinaryLinearThree.Vector) →ₗ[ZMod 2]
    Additive e.internalW :=
  (AddMonoidHom.toMultiplicative.symm
    (({ toFun := fun u : UK K L T z v =>
          (⟨⟨u, e.WK_le_actor (UK_le_WK K L T z v e.normalizeL e.fixSeed u.property)⟩,
            UK_le_WK K L T z v e.normalizeL e.fixSeed u.property⟩ : e.internalW)
        map_one' := rfl
        map_mul' := fun _ _ => rfl } : UK K L T z v →* e.internalW).comp
          d.moduleEquiv.symm.toMonoidHom)).toZModLinearMap 2

/-- The actual module inclusion loses no vectors. -/
theorem moduleInclusion_injective : Function.Injective (c.moduleInclusion) := by
  intro x y h
  have hh := congrArg (fun w : Additive e.internalW => ((w.toMul : plusActor K L T v) : G)) h
  have hu : d.moduleEquiv.symm (Multiplicative.ofAdd x) =
      d.moduleEquiv.symm (Multiplicative.ofAdd y) := Subtype.ext hh
  exact d.moduleEquiv.symm.injective hu

/-- The inclusion intertwines the full action and the faithful plus quotient action. -/
theorem moduleInclusion_equivariant (g : Gplus K L T z v e.normalizeL e.fixSeed)
    (w : BinaryLinearThree.Vector × BinaryLinearThree.Vector) :
    e.plusRepresentation g (c.moduleInclusion w) =
      c.moduleInclusion (BinaryLinearThree.DoubledOffenders.τ (c.action g) w) := by
  obtain ⟨a, rfl⟩ := plusMk_surjective K L T z v e.normalizeL e.fixSeed g
  let u := d.moduleEquiv.symm (Multiplicative.ofAdd w)
  have he := c.equivariant a u
  have hw : (d.moduleEquiv u).toAdd = w := congrArg Multiplicative.toAdd (d.moduleEquiv.apply_symm_apply _)
  rw [hw] at he
  have he' := congrArg d.moduleEquiv.symm he
  rw [d.moduleEquiv.symm_apply_apply] at he'
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  have hr := NormalElementaryQuotient.representation_apply e.internalW
    (plusMk K L T z v e.normalizeL e.fixSeed)
    (plusMk_surjective K L T z v e.normalizeL e.fixSeed) e.plusMk_ker_internal
    a (c.moduleInclusion w)
  change _ = ((d.moduleEquiv.symm (Multiplicative.ofAdd
    (BinaryLinearThree.DoubledOffenders.τ (c.action (plusMk K L T z v e.normalizeL e.fixSeed a)) w))) : G)
  exact (congrArg Subtype.val hr).trans (congrArg Subtype.val he')

/-- A best offender on W_K remains an offender on the faithful doubled U_K. -/
theorem offender_map {A : Subgroup (Gplus K L T z v e.normalizeL e.fixSeed)}
    (hA : IsBestOffender e.plusRepresentation A) :
    IsOffender BinaryLinearThree.DoubledOffenders.τ (A.map c.action) :=
  (hA.isOffender e.plusRepresentation).map_of_embedding e.plusRepresentation
    BinaryLinearThree.DoubledOffenders.τ c.action c.moduleInclusion
    c.moduleInclusion_injective c.moduleInclusion_equivariant c.faithful

private theorem mem_fixedSpace_preimage
    (A : Subgroup (Gplus K L T z v e.normalizeL e.fixSeed))
    (w : Additive e.internalW) :
    w ∈ fixedSpace e.plusRepresentation A ↔
      (w.toMul : plusActor K L T v) ∈ centralizer
        (A.comap (plusMk K L T z v e.normalizeL e.fixSeed) : Set (plusActor K L T v)) := by
  have h := NormalElementaryQuotient.mem_fixedSpace_image e.internalW
    (plusMk K L T z v e.normalizeL e.fixSeed)
    (plusMk_surjective K L T z v e.normalizeL e.fixSeed) e.plusMk_ker_internal
    (A.comap (plusMk K L T z v e.normalizeL e.fixSeed)) w
  rw [map_comap_eq_self_of_surjective (plusMk_surjective K L T z v e.normalizeL e.fixSeed)] at h
  exact h

/-- Transfer the full Sylow pointwise-fixer calculation to C_W(A), retaining
its full inverse image in the original actor. -/
theorem fixedCentralizer_image_eq
    (A : Subgroup (Gplus K L T z v e.normalizeL e.fixSeed))
    (hAS : A ≤ plusImage K L T z v e.normalizeL e.fixSeed (Tv T v))
    (hfix : ∀ x ∈ plusImage K L T z v e.normalizeL e.fixSeed (Tv T v),
      (∀ w ∈ fixedSpace BinaryLinearThree.DoubledOffenders.τ (A.map c.action),
        BinaryLinearThree.DoubledOffenders.τ (c.action x) w = w) → x ∈ A) :
    (e.internalR ⊓ centralizer (e.internalW ⊓ centralizer
      (A.comap (plusMk K L T z v e.normalizeL e.fixSeed) : Set (plusActor K L T v)) :
        Set (plusActor K L T v))).map (plusMk K L T z v e.normalizeL e.fixSeed) = A := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply hfix _ (mem_map_of_mem _ hx.1)
    intro w hw
    apply c.moduleInclusion_injective
    rw [← c.moduleInclusion_equivariant]
    have hw' : c.moduleInclusion w ∈ fixedSpace e.plusRepresentation A :=
      (embedding_mem_fixedSpace_iff e.plusRepresentation BinaryLinearThree.DoubledOffenders.τ
        c.action c.moduleInclusion c.moduleInclusion_injective c.moduleInclusion_equivariant A w).mpr hw
    have hc := hx.2 (c.moduleInclusion w).toMul
      ⟨(c.moduleInclusion w).toMul.property, (mem_fixedSpace_preimage A _).mp hw'⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [EarlierData.plusRepresentation, NormalElementaryQuotient.representation_apply]
    rw [← hc, mul_inv_cancel_right]
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := hAS ha
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro w hw
    exact (hw.2 x ha).symm

end ExtendedCoordinates
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
