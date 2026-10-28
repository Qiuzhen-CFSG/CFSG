module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.NormalizerAction
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.NormalizerFactorization
public import Theory.GroupTheory.ActorCentralizerLift

/-!
# The binary G₂ actor on the original local residual core

The source residual core R lies in T and hence in N_G(L). Restricting the
marked normalizer actor therefore gives a G₂(2) actor on the actual R.
Its kernel is the original Q=O₂(LT), since this is C_R(V). A
self-centralizing conjugate-module image then gives the centralizer cover
used in the counting factorization, with the same literal R, Q and Vᵈ.

Source: Aschbacher--Smith 3.3.28, printed p.601.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource Atlas.G2.Natural

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

local notation "F" => ZMod 2
local notation "E" => TraceZero F

omit [Finite G] in
/-- Faithfulness of the trace-zero model identifies an actor kernel with
the literal centralizer of the chosen module. -/
theorem full_g2_actor_ker_eq_centralizer
    (R : Subgroup G) (b : V ≃* Multiplicative E)
    (φ : R →* Atlas.G2.Model F)
    (hφ : ∀ (r : R) (x : E),
      (b.symm (Multiplicative.ofAdd
        (Atlas.G2.Natural.traceZeroAction F (φ r) x)) : G) =
        (r : G) * (b.symm (Multiplicative.ofAdd x) : G) * (r : G)⁻¹) :
    φ.ker = (centralizer (V : Set G)).subgroupOf R := by
  ext r
  change φ r = 1 ↔ (r : G) ∈ centralizer (V : Set G)
  constructor
  · intro hr v hv
    have hh := hφ r (b ⟨v, hv⟩).toAdd
    rw [hr, map_one, Module.End.one_apply, ofAdd_toAdd, b.symm_apply_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hr
    apply traceZeroAction_injective_binary
    apply LinearMap.ext
    intro x
    have hh := hφ r x
    have hc := hr (b.symm (Multiplicative.ofAdd x))
      (b.symm (Multiplicative.ofAdd x)).property
    have hfix : (r : G) * (b.symm (Multiplicative.ofAdd x) : G) * (r : G)⁻¹ =
        (b.symm (Multiplicative.ofAdd x) : G) :=
      mul_inv_eq_iff_eq_mul.mpr hc.symm
    rw [hfix] at hh
    have he := b.symm.injective (Subtype.ext hh)
    simpa only [map_one, Module.End.one_apply] using Multiplicative.ofAdd.injective he

/-- The actual residual core admits the marked full binary G₂ actor with
kernel exactly the original two-core Q. -/
theorem exists_local_residual_full_g2_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    ∃ (b : V ≃* Multiplicative E)
      (φ : omegaResidualCore T L →* Atlas.G2.Model F),
      (∀ (r : omegaResidualCore T L) (x : E),
        (b.symm (Multiplicative.ofAdd
          (Atlas.G2.Natural.traceZeroAction F (φ r) x)) : G) =
          (r : G) * (b.symm (Multiplicative.ofAdd x) : G) * (r : G)⁻¹) ∧
      φ.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
        (omegaResidualCore T L) := by
  obtain ⟨b, ψ, hψ, _⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  have hRN : omegaResidualCore T L ≤ normalizer (L : Set G) :=
    local_core_containments.2.trans D.sylow_normalizes_component
  let φ := ψ.comp (inclusion hRN)
  have hφ (r : omegaResidualCore T L) (x : E) := hψ (inclusion hRN r) x
  refine ⟨b, φ, hφ, ?_⟩
  rw [full_g2_actor_ker_eq_centralizer _ b φ hφ,
    ← local_centralizer_chosen_eq_core h D structural, inf_subgroupOf_left]

/-- The exact image self-centralizer premise discharges the source
centralizer-cover input for the literal conjugate Vᵈ. -/
theorem local_centralizer_conjugate_le_of_actor_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (φ : omegaResidualCore T L →* Atlas.G2.Model F)
    (hker : φ.ker ≤ ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (omegaResidualCore T L))
    (hself : φ.range ⊓ centralizer
        (((V.map (MulAut.conj d).toMonoidHom).subgroupOf
          (omegaResidualCore T L)).map φ : Set (Atlas.G2.Model F)) ≤
      ((V.map (MulAut.conj d).toMonoidHom).subgroupOf
        (omegaResidualCore T L)).map φ) :
    omegaResidualCore T L ⊓
        centralizer (V.map (MulAut.conj d).toMonoidHom : Set G) ≤
      V.map (MulAut.conj d).toMonoidHom ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  inf_centralizer_le_sup_of_actor_image _ _ _
    (conjugate_chosen_le_local_core h D structural e hne hd)
    local_core_containments.1 φ hker hself

/-- The image self-centralizer, image index and fixed-space index feed
the original Q=V C_Q(Vᵈ) conclusion without changing the quotient actor. -/
theorem core_eq_chosen_sup_centralizer_of_actor_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (φ : omegaResidualCore T L →* Atlas.G2.Model F)
    (hker : φ.ker ≤ ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (omegaResidualCore T L))
    (hself : φ.range ⊓ centralizer
        (((V.map (MulAut.conj d).toMonoidHom).subgroupOf
          (omegaResidualCore T L)).map φ : Set (Atlas.G2.Model F)) ≤
      ((V.map (MulAut.conj d).toMonoidHom).subgroupOf
        (omegaResidualCore T L)).map φ)
    (himage : Nat.card (V.map (MulAut.conj d).toMonoidHom) =
      8 * Nat.card (V.map (MulAut.conj d).toMonoidHom ⊓
        (L ⊔ (T : Subgroup G)).pCoreIn 2 : Subgroup G))
    (hfixed : Nat.card V = 8 * Nat.card (V ⊓
      centralizer (V.map (MulAut.conj d).toMonoidHom : Set G) : Subgroup G)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = V ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓
        centralizer (V.map (MulAut.conj d).toMonoidHom : Set G)) :=
  core_eq_chosen_sup_centralizer_of_point_geometry h D structural e hne hd
    (local_centralizer_conjugate_le_of_actor_image h D structural e hne hd φ hker hself)
    himage hfixed

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
