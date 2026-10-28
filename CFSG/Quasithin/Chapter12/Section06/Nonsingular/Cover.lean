module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.PointStabilizer
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer.Order
public import Theory.Representation.BinaryPermutationEightCover.Universal
public import Theory.Representation.BinaryConjugationSection.Coinvariants

/-!
# The original augmentation cover and full nonsingular stabilizer

The Irr⁺ choice generates the literal V by L-commutators. Descending the
actual conjugation representation through its kernel makes the original
projection V → V/C_V(L) a perfect central cover of the A₈ natural module.
The proved universal-cover theorem supplies an equivariant surjection
from the augmentation core, preserving that projection.

A nonsingular natural vector has a pair representative. Its stabilizer
fixes both lifts to the augmentation core, so it fixes every lift in V.
Consequently C_L(v) is the full preimage of the model stabilizer, and its
index in L is exactly 28. This supplies the L-orbit calculation preceding
the Sylow arrangement; no Sylow position in M or G is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), §12.6 and
the opening of Theorem 12.6.2, printed pp.822–824, using B.3.3 and I.1.5–6.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BinaryNaturalDual.VectorStabilizers
open Representation Representation.OneCohomology
open BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem seed_kernel (hn : L ≤ normalizer (V : Set G)) :
    (conjugation L V hn).ker ≤ (seedRepresentation L V hn).ker := by
  intro l hl
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  exact DFunLike.congr_fun hl v.toMul

noncomputable def OrthogonalMarking.fullAction (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) :
    Representation (ZMod 2) (alternatingGroup (Fin 8)) (Additive V) :=
  (QuotientGroup.lift (conjugation L V chosen.normalizes).ker
    (seedRepresentation L V chosen.normalizes) (by exact seed_kernel chosen.normalizes)).comp
      D.groupEquiv.symm.toMonoidHom

omit [Finite G] in
theorem OrthogonalMarking.fullAction_actorMap (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (l : L) (v : Additive V) :
    D.fullAction chosen (D.actorMap l) v = seedRepresentation L V chosen.normalizes l v := by
  dsimp only [fullAction, actorMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [D.groupEquiv.symm_apply_apply]
  rfl

theorem OrthogonalMarking.core_cover (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) :
    ∃ f : core (Fin 8) →ₗ[ZMod 2] Additive V, Function.Surjective f ∧
      (∀ l : L, ∀ w, f (alternatingCoreRepresentation (Fin 8) (D.actorMap l) w) =
        seedRepresentation L V chosen.normalizes l (f w)) ∧
      ∀ w, D.coordinates (Submodule.Quotient.mk (f w)) = coreToNatural (Fin 8) w := by
  let σ := D.fullAction chosen
  let f₀ := D.coordinates.toLinearMap.comp (fixedSeed L V chosen.normalizes).toSubmodule.mkQ
  let P : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin 8)) :=
    f₀.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g w
      obtain ⟨l,rfl⟩ := D.actorMap_surjective g
      rw [D.fullAction_actorMap]
      exact D.equivariant l (Submodule.Quotient.mk w))
  have hsur : Function.Surjective P :=
    D.coordinates.surjective.comp (Submodule.mkQ_surjective _)
  have hk : P.toLinearMap.ker ≤ fixed σ := by
    intro w hw a
    obtain ⟨l,rfl⟩ := D.actorMap_surjective a
    rw [D.fullAction_actorMap]
    have hz : (Submodule.Quotient.mk w : Vhat L V chosen.normalizes) = 0 :=
      D.coordinates.injective (show D.coordinates _ = D.coordinates 0 from
        hw.trans D.coordinates.map_zero.symm)
    exact (Submodule.Quotient.mk_eq_zero _).mp hz l
  let c : BinaryConjugationSection L V ⊥ (σ.comp D.actorMap) := {
    section_le := chosen.le_component
    kernel_le := bot_le
    normalized := chosen.normalizes
    coordinates := {
      toFun w := Multiplicative.ofAdd (Additive.ofMul w)
      map_one' := rfl
      map_mul' _ _ := rfl }
    onto := fun w => ⟨w.toAdd.toMul,rfl⟩
    kernel_eq := by
      ext w
      change w = 1 ↔ (w : G) = 1
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    equivariant := by
      intro l w
      change Additive.ofMul ⟨(l : G) * w * (l : G)⁻¹, _⟩ =
        D.fullAction chosen (D.actorMap l) (Additive.ofMul w)
      rw [D.fullAction_actorMap]
      rfl }
  have hc : Coinvariants.ker σ = ⊤ :=
    c.coinvariants_eq_top_of_group_generation L le_rfl σ D.actorMap (fun _ _ => rfl)
      (by rw [sup_bot_eq, commutator_comm, ← chosen.eq_commutator])
  obtain ⟨f,hf,he,hp⟩ := EightCover.core_quotient_of_alternating_cover σ P ⟨hsur,hk,hc⟩
  refine ⟨f,hf, ?_,hp⟩
  intro l w
  exact (he (D.actorMap l) w).trans (D.fullAction_actorMap chosen l (f w))



theorem OrthogonalMarking.nonsingular_fixed_iff (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v) (l : L) :
    seedRepresentation L V chosen.normalizes l (Additive.ofMul v) = Additive.ofMul v ↔
      alternatingNaturalRepresentation (Fin 8) (D.actorMap l)
        (D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v)) := by
  constructor
  · intro h
    have he := D.equivariant l (Submodule.Quotient.mk (Additive.ofMul v))
    change D.coordinates (Submodule.Quotient.mk
      (seedRepresentation L V chosen.normalizes l (Additive.ofMul v))) = _ at he
    rw [h] at he
    exact he.symm
  · intro h
    obtain ⟨f,hf,he,hp⟩ := D.core_cover chosen
    obtain ⟨w,hw⟩ := hf (Additive.ofMul v)
    have hwq : coreToNatural (Fin 8) w =
        D.coordinates (Submodule.Quotient.mk (Additive.ofMul v)) := by
      rw [← hp,hw]
    have hfixed := core_fixed_of_nonsingular (D.actorMap l) w (hwq ▸ hv)
      (by change alternatingNaturalRepresentation (Fin 8) (D.actorMap l) _ = _; rwa [hwq])
    calc
      _ = seedRepresentation L V chosen.normalizes l (f w) := by rw [hw]
      _ = f (alternatingCoreRepresentation (Fin 8) (D.actorMap l) w) := (he l w).symm
      _ = Additive.ofMul v := (congrArg f hfixed).trans hw

theorem OrthogonalMarking.centralizer_preimage (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    (CLv L (v : G)).subgroupOf L =
      (stabilizer (D.coordinates (Submodule.Quotient.mk (Additive.ofMul v)))).comap D.actorMap := by
  ext l
  change ((l : G) ∈ L ∧ (l : G) ∈ Gv (v : G)) ↔ _
  rw [and_iff_right l.property]
  change (l : G) ∈ Gv (v : G) ↔
    alternatingNaturalRepresentation (Fin 8) (D.actorMap l)
      (D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) = _
  rw [← D.nonsingular_fixed_iff chosen v hv l]
  change (l : G) ∈ centralizer ({(v : G)} : Set G) ↔ _
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (v : G) * (l : G)⁻¹ = v
    rw [h,mul_inv_cancel_right]
  · intro h
    have he := congrArg (fun a : Additive V => (a.toMul : G)) h
    change (l : G) * (v : G) * (l : G)⁻¹ = v at he
    exact mul_inv_eq_iff_eq_mul.mp he

/-- The literal nonsingular L-orbit has length 28, including a nonzero fixed space. -/
theorem OrthogonalMarking.nonsingular_centralizer_index
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    (CLv L (v : G)).relIndex L = 28 := by
  change ((CLv L (v : G)).subgroupOf L).index = 28
  rw [D.centralizer_preimage chosen v hv,
    (stabilizer (D.coordinates (Submodule.Quotient.mk (Additive.ofMul v)))).index_comap_of_surjective
      D.actorMap_surjective]
  exact nonsingular_stabilizer_index _ hv

end CFSG.Quasithin.Chapter12.Section06
