module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedMovementTransport
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedNine
public import Theory.SpecificGroups.OrthogonalFourBinary.MarkedNineMovement
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# The Nine marking with its actual residual movement

The marked orthogonal vector and the literal stabilizer are transported along
one fixed coordinate equivalence. The Sylow fixed space lies in the marked
line plus the displacement of the stabilizer's actual two-residual. This is
the missing marked-row input to the odd-core and component argument of
15.1.19; generation, cardinality and the Sylow intersection refer to the same
chosen vector throughout.

Source: Aschbacher--Smith 15.1.16(b), 15.1.18 and 15.1.19(1),
printed pp.1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original Nine row supplies its marked stabilizer and residual fixed-space bound. -/
theorem chosen_nine_marked_image_with_movement
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)) :
    ∃ (v : Additive V) (K : Subgroup (internalActionImage M V hn)),
      v ≠ 0 ∧
      v ∈ fixedSpace (imageRepresentation M V hn)
        (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V hn).rangeRestrict) ∧
      (∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v) ∧
      K ⊔ (((T : Subgroup G).subgroupOf M).map
        (actionHom M V hn).rangeRestrict) = ⊤ ∧
      Nat.card K = 6 ∧
      (∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype =
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) ⊓ K) ∧
      fixedSpace (imageRepresentation M V hn)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) ≤
        Submodule.span (ZMod 2) {v} ⊔ subspaceCommutator (imageRepresentation M V hn)
          ⊤ ((pResidual 2 K).map K.subtype) := by
  let f := (actionHom M V hn).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  let ρ := imageRepresentation M V hn
  obtain ⟨l, _, _, hD, _, _, hS, x, φ, hφ, hcoord⟩ := h9
  let hcyc : IsCyclic S := hS.1
  obtain ⟨A, hAS, hA, hJA⟩ := ChapterB.exists_cyclic_two_marker
    (T : Subgroup G) M hTM f S le_rfl hS.2 1
  obtain ⟨z, hz, hfix, hgen, hKcard, hSyl, hbound⟩ :=
    @OrthogonalFourBinary.MarkedNine.exists_marked_vector_with_movement _ _ _ φ hφ hD S hcyc hS.2
  let v : Additive V := x.symm z
  let K := OrthogonalFourBinary.MarkedNine.pointStabilizer φ z
  have hv : v ≠ 0 := by
    intro h
    have hh := congrArg x h
    simp only [v, x.apply_symm_apply, map_zero] at hh
    exact hz hh
  have hK : ∀ d, d ∈ K ↔ ρ d v = v := by
    intro d
    change (φ d).val z = z ↔ ρ d v = v
    constructor
    · intro hd
      apply x.injective
      calc
        x (ρ d v) = (φ d).val (x v) := hcoord d v
        _ = (φ d).val z := by rw [show x v = z from x.apply_symm_apply z]
        _ = z := hd
        _ = x v := (x.apply_symm_apply z).symm
    · intro hd
      have hh := congrArg x hd
      rw [hcoord d v] at hh
      simpa only [v, x.apply_symm_apply] using hh
  have hvfixed : v ∈ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f) := by
    intro d
    apply (hK d).mp
    apply hfix d (hAS (hJA d.property))
    have hp := pow_card_eq_one' (x := (⟨(d : internalActionImage M V hn), hJA d.property⟩ : A))
    rw [hA] at hp
    exact congrArg Subtype.val hp
  refine ⟨v,K,hv,hvfixed,hK,hgen,hKcard,hSyl,?_⟩
  let σ := OrthogonalFourBinary.naturalRepresentation.comp φ
  let R := (pResidual 2 K).map K.subtype
  have hx (d : internalActionImage M V hn) (w : OrthogonalFourBinary.Space) :
      ρ d (x.symm w) = x.symm (σ d w) := by
    apply x.injective
    rw [x.apply_symm_apply,hcoord,x.apply_symm_apply]
    rfl
  have hm := subspaceCommutator_map_embedding ρ σ (MonoidHom.id _) x.symm.toLinearMap
    hx R ⊤
  simp only [Submodule.map_top,LinearEquiv.range,Subgroup.map_id] at hm
  intro w hw
  have hwx : x w ∈ fixedSpace σ S := by
    intro a
    change (φ a).val (x w) = x w
    rw [← hcoord]
    exact congrArg x (hw a)
  have hb := hbound hwx
  have hmapped := Submodule.mem_map_of_mem (f := x.symm.toLinearMap) hb
  rw [Submodule.map_sup,Submodule.map_span,Set.image_singleton,← hm] at hmapped
  simpa only [LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hmapped
end CFSG.Quasithin.Chapter15.Section01
