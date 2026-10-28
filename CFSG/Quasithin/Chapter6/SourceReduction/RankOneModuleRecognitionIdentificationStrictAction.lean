module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictGeometry

/-!
# The faithful dotted action in the strict branch

Conjugation by H = C_G(z) on its normal subgroup U descends to the literal
central quotient U/Z(U). The dotted group is H modulo the kernel of this
specific action. The kernel criterion retains ambient commutators and the
embedded center of U; no equality with O₂(H) is imposed.

The resulting binary representation is faithful and preserves the actual
commutator form. On the original layer V, the kernel is exactly U ∩ V:
a commutator lying both in V and Z(U) lies in ⟨z⟩, where the earlier action
kernel criterion applies. Consequently the image of V in the dotted group
has order two.

The exposed action definitions retain the literal conjugation and quotient
maps needed by subsequent crossing and moved-space calculations.
Source: Aschbacher--Smith, 6.2.15--16, printed pp.688--689. The moved-space
type, crossing subgroups, G.11 inputs and final elimination remain to be
constructed by the strict-branch owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G]

/-- Actual conjugation by H on its normal subgroup U. -/
@[expose] def strictClosureAction (T L R : Subgroup G) (z : G) :
    centralizer ({z} : Set G) →* MulAut (sourceClosure T L R z) := by
  let _ := conjMulDistribMulActionOfLeNormalizer (centralizer ({z} : Set G))
    (sourceClosure T L R z) (sourceClosure_normalized T L R z)
  exact MulDistribMulAction.toMulAut _ _

theorem strictClosureAction_apply (T L R : Subgroup G) (z : G)
    (h : centralizer ({z} : Set G)) (u : sourceClosure T L R z) :
    (strictClosureAction T L R z h u : G) = (h : G) * (u : G) * (h : G)⁻¹ := rfl

abbrev StrictVectorQuotient (T L R : Subgroup G) (z : G) :=
  sourceClosure T L R z ⧸ center (sourceClosure T L R z)

/-- The source H-action on the literal central quotient U/Z(U). -/
@[expose] def strictQuotientAction (T L R : Subgroup G) (z : G) :
    centralizer ({z} : Set G) →* MulAut (StrictVectorQuotient T L R z) :=
  (quotientAut (center (sourceClosure T L R z))).comp (strictClosureAction T L R z)

theorem strictQuotientAction_mk (T L R : Subgroup G) (z : G)
    (h : centralizer ({z} : Set G)) (u : sourceClosure T L R z) :
    strictQuotientAction T L R z h (QuotientGroup.mk' _ u) =
      QuotientGroup.mk' _ (strictClosureAction T L R z h u) :=
  quotientAut_apply_mk _ _ _

/-- The denominator is exactly C_H(U/Z(U)), expressed by literal ambient
commutators, and need not equal O₂(H). -/
theorem strictQuotientAction_mem_ker (T L R : Subgroup G) (z : G)
    (h : centralizer ({z} : Set G)) :
    h ∈ (strictQuotientAction T L R z).ker ↔
      ∀ u ∈ sourceClosure T L R z, ⁅(h : G), u⁆ ∈
        (center (sourceClosure T L R z)).map (sourceClosure T L R z).subtype := by
  let U := sourceClosure T L R z
  change strictQuotientAction T L R z h = 1 ↔ _
  constructor
  · intro hh u hu
    have he := congrArg (fun a : MulAut (StrictVectorQuotient T L R z) =>
      a (QuotientGroup.mk' _ ⟨u, hu⟩)) hh
    rw [strictQuotientAction_mk] at he
    have hc := QuotientGroup.eq_iff_div_mem.mp he
    refine ⟨strictClosureAction T L R z h ⟨u, hu⟩ / ⟨u, hu⟩, hc, ?_⟩
    change (strictClosureAction T L R z h ⟨u, hu⟩ : G) / u = _
    rw [strictClosureAction_apply, div_eq_mul_inv, commutatorElement_def]
  · intro hh
    apply MulEquiv.ext
    intro w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center U) w
    rw [strictQuotientAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨c, hc, he⟩ := hh u u.property
    have huc : strictClosureAction T L R z h u / u = c := by
      apply Subtype.ext
      change (strictClosureAction T L R z h u : G) / (u : G) = (c : G)
      rw [strictClosureAction_apply, div_eq_mul_inv, ← commutatorElement_def]
      exact he.symm
    rw [huc]
    exact hc

/-- The dotted actor is the original centralizer modulo its actual action kernel. -/
abbrev StrictActor (T L R : Subgroup G) (z : G) :=
  centralizer ({z} : Set G) ⧸ (strictQuotientAction T L R z).ker

@[expose] def strictActorEquivRange (T L R : Subgroup G) (z : G) :
    StrictActor T L R z ≃* (strictQuotientAction T L R z).range :=
  QuotientGroup.quotientKerEquivRange (strictQuotientAction T L R z)

section Representation
variable (T L R : Subgroup G) (z : G)
  [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)]

/-- Faithful binary representation of the exact dotted quotient. -/
@[expose] def strictRepresentation :
    Representation (ZMod 2) (StrictActor T L R z) (Additive (StrictVectorQuotient T L R z)) where
  toFun a := (strictActorEquivRange T L R z a).val.toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext v
    change Additive.ofMul ((strictActorEquivRange T L R z 1).val v.toMul) = v
    rw [map_one]
    rfl
  map_mul' a b := by
    ext v
    change Additive.ofMul ((strictActorEquivRange T L R z (a * b)).val v.toMul) = _
    rw [map_mul]
    rfl

theorem strictRepresentation_mk (h : centralizer ({z} : Set G))
    (v : Additive (StrictVectorQuotient T L R z)) :
    strictRepresentation T L R z (QuotientGroup.mk' _ h) v =
      Additive.ofMul (strictQuotientAction T L R z h v.toMul) := rfl

theorem strictRepresentation_injective : Function.Injective (strictRepresentation T L R z) := by
  intro a b hab
  apply (strictActorEquivRange T L R z).injective
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  exact Additive.ofMul.injective
    (congrArg (fun f : Module.End (ZMod 2) (Additive (StrictVectorQuotient T L R z)) =>
      f (Additive.ofMul v)) hab)

end Representation

variable [Finite G] {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G}
  {n : ℕ} {z : G}

/-- The original strict source hypotheses construct a faithful symplectic
representation of H/C_H(U/Z(U)), on the actual central quotient and in
dimension at least four. -/
theorem LocalAnalysis.strict_faithful_symplectic_action
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z),
      letI := he
      ∃ B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)),
        B.IsAlt ∧ B.Nondegenerate ∧
        4 ≤ Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ∧
        Function.Injective (strictRepresentation (T : Subgroup G) L R z) ∧
        ∀ a x y, B (strictRepresentation (T : Subgroup G) L R z a x)
          (strictRepresentation (T : Subgroup G) L R z a y) = B x y := by
  obtain ⟨he, e, B, ha, hn, hd, _, hi⟩ := A.strict_symplectic_geometry h611 hnatural hz horder hstrict
  let := he
  refine ⟨he, B, ha, hn, hd, strictRepresentation_injective _ _ _ _, ?_⟩
  intro a x y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (strictQuotientAction (T : Subgroup G) L R z).ker a
  rw [strictRepresentation_mk, strictRepresentation_mk]
  exact hi (strictClosureAction (T : Subgroup G) L R z h) x.toMul y.toMul



/-- Passing from U/⟨z⟩ to U/Z(U) does not enlarge the action kernel
on the original layer: its intersection remains precisely U ∩ V. -/
theorem LocalAnalysis.strict_layer_action_kernel
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    (strictQuotientAction (T : Subgroup G) L R z).ker.map
      (centralizer ({z} : Set G)).subtype ⊓ layer L R =
      sourceClosure (T : Subgroup G) L R z ⊓ layer L R := by
  let U := sourceClosure (T : Subgroup G) L R z
  let H := centralizer ({z} : Set G)
  have hcenter : (center U).map U.subtype ⊓ layer L R = zpowers z :=
    A.strict_layer_center_intersection h611 hnatural hz horder hstrict
  have hline : zpowers z ≤ (center U).map U.subtype := hcenter ▸ inf_le_left
  ext x
  constructor
  · rintro ⟨⟨h, hk, rfl⟩, hv⟩
    have hcomm := (strictQuotientAction_mem_ker (T : Subgroup G) L R z h).mp hk
    have hcore : (h : G) ∈ H.pCoreIn 2 := (A.action_kernel h h.property).mp (by
      intro u hu
      rw [← hcenter]
      exact ⟨hcomm u hu, (A.layer_closure_commutator (commutator_mem_commutator hv hu)).1⟩)
    have he := (A.strict_intersection_eq_core h611 hnatural hstrict).1
    exact he.symm ▸ (show (h : G) ∈ layer L R ⊓ H.pCoreIn 2 from ⟨hv, hcore⟩)
  · intro hx
    have hxH := (A.closure_le_core.trans (H.pCoreIn_le 2)) hx.1
    refine ⟨⟨⟨x, hxH⟩, ?_, rfl⟩, hx.2⟩
    apply (strictQuotientAction_mem_ker (T : Subgroup G) L R z ⟨x, hxH⟩).mpr
    intro u hu
    exact hline (A.closure_core_commutator
      (commutator_mem_commutator hx.1 (A.closure_le_core hu)))

/-- The original layer has an order-two image in the exact dotted actor. -/
theorem LocalAnalysis.strict_layer_actor_image_card
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    Nat.card (((layer L R).subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker)) = 2 := by
  let H := centralizer ({z} : Set G)
  let V := (layer L R).subgroupOf H
  let K := (strictQuotientAction (T : Subgroup G) L R z).ker
  have hVH : layer L R ≤ H := layer_le_involution_centralizer h611 hz
  have hcV : Nat.card V = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv).trans hnatural.2.1.card
  have hcK : Nat.card (K ⊓ V : Subgroup H) = 8 := by
    rw [← card_subtype H (K ⊓ V), map_inf _ _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hVH, A.strict_layer_action_kernel h611 hnatural hz horder hstrict]
    exact (A.strict_intersection_eq_core h611 hnatural hstrict).2
  have hp := relIndex_mul_relIndex (⊥ : Subgroup H) (K ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, hcK, hcV, inf_relIndex_right] at hp
  have hr := relIndex_ker V (QuotientGroup.mk' K)
  rw [QuotientGroup.ker_mk'] at hr
  change Nat.card (V.map (QuotientGroup.mk' K)) = 2
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
