module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.FullMovement
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.CubicPlane
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Literal tensor images, perpendicular spaces and the first moved plane

Source: Aschbacher–Smith, Lemma 14.4.10 and its first proof paragraph,
printed p.1010; the earlier commutator form and bound are 12.8.8(2) and
12.8.11(1), printed pp.851 and 854, combined manuscript of 1 March 2004.

All images use the published U/Z(U) coordinates, and all actors use the
published H/O₂(H) coordinates. Conjugation identifies the literal image of
[P,X] with its linear commutator. The actual three-core image is the marked
cubic group, so every quotient line yields an image of order four and,
under extraspeciality, an actual moved subgroup of order eight.

Normalization of a binary quotient line implies pointwise fixation. The
canonical commutator form identifies the image of C_U(P) with the actual
perpendicular space, and the source bound [W,Wᵍ] ≤ E passes through the same
quotient maps. Containment of the first moved plane in E still requires
the constituent intersection calculation; the final Y-application below
is explicitly conditional on that containment.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {G : Type*} [Group G]
namespace CaseFiveCoordinates
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {H U : Subgroup G} (c : CaseFiveCoordinates hAD (V := V) H U)

local instance : Module (ZMod 2)
    (Additive (Multiplicative (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V))) :=
  inferInstanceAs (Module (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V))

/-- The literal central-quotient image in the published tensor coordinates. -/
noncomputable def image (A : Subgroup G) :
    Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V) :=
  quotientImage U c.quotientMap A

/-- Membership retains an actual representative in U. -/
theorem mem_image (A : Subgroup G)
    (v : BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V) :
    v ∈ c.image A ↔ ∃ u : U, (u : G) ∈ A ∧ (c.quotientMap u).toAdd = v := by
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨u, hu, congrArg Multiplicative.toAdd he⟩
  · rintro ⟨u, hu, he⟩
    exact ⟨u, hu, congrArg Multiplicative.ofAdd he⟩

/-- Subgroup containments pass to the same quotient coordinates. -/
theorem image_mono {A B : Subgroup G} (h : A ≤ B) : c.image A ≤ c.image B := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := (c.mem_image A v).mp hv
  exact (c.mem_image B _).mpr ⟨u, h hu, rfl⟩

/-- The literal actor map for a contained subgroup of H. -/
noncomputable def actorMap {X : Subgroup G} (hX : X ≤ H) : X →* Three × D :=
  c.actor.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hX))

/-- Its range is the published star image in the actor coordinates. -/
theorem actorMap_range {X : Subgroup G} (hX : X ≤ H) :
    (c.actorMap hX).range = (star H X).map c.actor.toMonoidHom := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨⟨x, hX x.property⟩, x.property, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

/-- Relative normalization gives invariance of the literal quotient image. -/
theorem image_invariant {P X : Subgroup G} (hX : X ≤ H)
    (hn : X ≤ normalizer (P : Set G)) :
    (star H X).map c.actor.toMonoidHom ≤
      subspaceStabilizer (sourceTensorAction c.constituent) (c.image P) := by
  apply le_subspaceStabilizer
  intro a ha v hv
  rw [← c.actorMap_range hX] at ha
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨u, hu, rfl⟩ := (c.mem_image P v).mp hv
  let u' : U := ⟨(x : G) * u * (x : G)⁻¹,
    le_normalizer_iff.mp c.H_normalizes_U (inclusion hX x) (hX x.property) u u.property⟩
  have he : (c.quotientMap u').toAdd =
      sourceTensorAction c.constituent (c.actorMap hX x) (c.quotientMap u).toAdd :=
    congrArg Multiplicative.toAdd (c.equivariant (inclusion hX x) u)
  rw [← he]
  exact (c.mem_image P _).mpr ⟨u',
    le_normalizer_iff.mp hn x x.property u hu, rfl⟩

/-- A normalized binary quotient line is fixed pointwise. -/
theorem point_fixed_of_normalizes {P X : Subgroup G} (hX : X ≤ H)
    (hn : X ≤ normalizer (P : Set G))
    (hP : Module.finrank (ZMod 2) (c.image P) = 1) :
    c.image P ≤ fixedSpace (sourceTensorAction c.constituent)
      ((star H X).map c.actor.toMonoidHom) := by
  intro v hv a
  change sourceTensorAction c.constituent (a : Three × D) v = v
  by_cases hv0 : v = 0
  · subst v
    exact map_zero _
  have hm := (c.image_invariant hX hn a.property v).mpr hv
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0
  rw [hspan] at hm
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hm
  have hf : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by decide
  rcases hf k with rfl | rfl
  · have hh := congrArg (sourceTensorAction c.constituent (a : Three × D)⁻¹) hk
    simp only [zero_smul, map_zero, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply] at hh
    exact (hv0 hh.symm).elim
  · simpa only [one_smul] using hk.symm

/-- Literal conjugation identifies group and linear commutator images. -/
theorem image_commutator {P X : Subgroup G} (hPU : P ≤ U) (hX : X ≤ H) :
    c.image (movedSpace P X) = subspaceCommutator (sourceTensorAction c.constituent)
      (c.image P) ((star H X).map c.actor.toMonoidHom) := by
  rw [← c.actorMap_range hX]
  have hact : ∀ (x : X) (u : U),
      sourceTensorAction c.constituent (c.actorMap hX x) (c.quotientMap u).toAdd =
      (c.quotientMap ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp (hX.trans c.H_normalizes_U) x x.property u u.property⟩).toAdd := by
    intro x u
    exact (congrArg Multiplicative.toAdd (c.equivariant (inclusion hX x) u)).symm
  exact quotientImage_commutator
    (Q := Multiplicative (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V))
    (sourceTensorAction c.constituent) U P X
    (hX.trans c.H_normalizes_U) hPU (c.actorMap hX) c.quotientMap
    c.quotientMap_surjective hact

/-- The tensor coordinates preserve the cardinality of the literal tilde image. -/
theorem image_card [Finite G] (A : Subgroup G) :
    Nat.card (c.image A) = Nat.card (tilde U A) := by
  let e : (c.image A) ≃ ((A.subgroupOf U).map c.quotientMap) := {
    toFun v := ⟨Multiplicative.ofAdd v, v.property⟩
    invFun v := ⟨v.val.toAdd, v.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e]
  change Nat.card ((A.subgroupOf U).map
    (c.space.toMonoidHom.comp (QuotientGroup.mk' (center U)))) = _
  rw [← Subgroup.map_map, Subgroup.card_map_of_injective c.space.injective]
  rfl

/-- Containment in tensor coordinates is exactly containment of tilde images. -/
theorem image_le_iff {A B : Subgroup G} :
    c.image A ≤ c.image B ↔ tilde U A ≤ tilde U B := by
  change ((A.subgroupOf U).map c.quotientMap ≤ (B.subgroupOf U).map c.quotientMap) ↔ _
  change ((A.subgroupOf U).map
    (c.space.toMonoidHom.comp (QuotientGroup.mk' (center U))) ≤
    (B.subgroupOf U).map
    (c.space.toMonoidHom.comp (QuotientGroup.mk' (center U)))) ↔ _
  rw [← Subgroup.map_map, ← Subgroup.map_map,
    Subgroup.map_le_map_iff_of_injective c.space.injective]
  rfl

/-- The canonical commutator form gives W̃ = Ṽ₂-perp for W = C_U(V₂). -/
theorem image_centralizer (P : Subgroup G) (hPU : P ≤ U)
    (B : LinearMap.BilinForm (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V))
    (hB : ∀ u v : U, B (c.quotientMap u).toAdd (c.quotientMap v).toAdd = 0 ↔
      Commute u v) :
    c.image (U ⊓ centralizer (P : Set G)) = (c.image P).orthogonalBilin B := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := (c.mem_image _ _).mp hv
    intro w hw
    obtain ⟨p, hp, rfl⟩ := (c.mem_image P w).mp hw
    apply (hB p u).mpr
    apply Subtype.ext
    exact mem_centralizer_iff.mp hu.2 p hp
  · intro hv
    obtain ⟨u, hu⟩ := c.quotientMap_surjective (Multiplicative.ofAdd v)
    have huv : (c.quotientMap u).toAdd = v := congrArg Multiplicative.toAdd hu
    apply (c.mem_image _ _).mpr
    refine ⟨u, ⟨u.property, ?_⟩, huv⟩
    apply mem_centralizer_iff.mpr
    intro p hp
    let pU : U := ⟨p, hPU hp⟩
    have hh := hv (c.quotientMap pU).toAdd
      ((c.mem_image P _).mpr ⟨pU, hp, rfl⟩)
    rw [← huv] at hh
    exact congrArg Subtype.val ((hB pU u).mp hh).eq

/-- The earlier actual commutator bound descends through the specified maps. -/
theorem source_commutator_bound {W Wg E : Subgroup G}
    (hWU : W ≤ U) (hWgH : Wg ≤ H) (hWE : ⁅W, Wg⁆ ≤ E) :
    subspaceCommutator (sourceTensorAction c.constituent) (c.image W)
      ((star H Wg).map c.actor.toMonoidHom) ≤ c.image E := by
  rw [← c.image_commutator hWU hWgH]
  exact c.image_mono hWE

/-- The actual X₁ image is the marked cubic subgroup. -/
theorem first_actor_image [Finite G] :
    (star H (first H)).map c.actor.toMonoidHom = zpowers (cubicActor D) := by
  have hle : zpowers (cubicActor D) ≤ (star H (first H)).map c.actor.toMonoidHom := by
    apply zpowers_le.mpr
    exact ⟨c.actor.symm (cubicActor D), c.marked_cubic_mem_star_first,
      c.actor.apply_symm_apply _⟩
  apply (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective c.actor.injective, star_first,
    Theory.SpecificGroups.TensorThreeFive.tensor_threeCore_card c.actor_models,
    Nat.card_zpowers, cubicActor_order]

/-- The literal first moved image is the cubic plane on the source quotient line. -/
theorem first_image_eq_cubicPlane [Finite G] {P : Subgroup G} (hPU : P ≤ U)
    (v : BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V)
    (hP : c.image P = Submodule.span (ZMod 2) {v}) :
    c.image (movedSpace P (first H)) = cubicPlane c.constituent v := by
  rw [c.image_commutator hPU (first_le H), c.first_actor_image, hP, cubic_moved_line]

/-- The actual central-quotient image of [P,X₁] has order four. -/
theorem first_tilde_card_four [Finite G] {P : Subgroup G} (hPU : P ≤ U)
    (hP : Module.finrank (ZMod 2) (c.image P) = 1) :
    Nat.card (tilde U (movedSpace P (first H))) = 4 := by
  have hne : c.image P ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hP
    omega
  obtain ⟨v, hv, hv0⟩ := (c.image P).ne_bot_iff.mp hne
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0
  rw [← c.image_card, c.first_image_eq_cubicPlane hPU v hspan,
    cubicPlane_card c.constituent v hv0]

/-- Extraspeciality supplies the central factor, giving actual order eight. -/
theorem first_movedSpace_card_eight [Finite G] [IsExtraspecial 2 U]
    {T P : Subgroup G} (hT : T ≤ H) (hUT : U ≤ T) (hPU : P ≤ U)
    (hZP : center U ≤ P.subgroupOf U)
    (hP : Module.finrank (ZMod 2) (c.image P) = 1) :
    Nat.card (movedSpace P (first H)) = 8 := by
  exact Mathieu.movedSpace_card_eight_of_extraspecial_image H T U P (first H)
    (first_mem_X hT c.actor_models) hUT c.H_normalizes_U hPU hZP
    (QuotientGroup.mk' (center U)) (QuotientGroup.ker_mk' _)
    (c.first_tilde_card_four hPU hP)

/-- After the remaining plane containment, apply the literal Y-lifting theorem. -/
theorem first_mem_Y_of_image_le [Finite G] [IsExtraspecial 2 U]
    {T P E : Subgroup G} (hT : T ≤ H) (hUT : U ≤ T) (hPU : P ≤ U)
    (hZP : center U ≤ P.subgroupOf U) (hZE : center U ≤ E.subgroupOf U)
    (hP : Module.finrank (ZMod 2) (c.image P) = 1)
    (hE : c.image (movedSpace P (first H)) ≤ c.image E) :
    first H ∈ YFamily H T P E := by
  exact first_mem_Y_of_tilde_calculation hT hUT c.H_normalizes_U hPU hZP hZE
    c.actor_models (c.first_tilde_card_four hPU hP) ((c.image_le_iff).mp hE)

end CaseFiveCoordinates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
