module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSeedCentralizer
public import CFSG.Quasithin.ChapterF.Section09.ClosurePair

/-!
# The original normal-branch orthogonal action and S₃ pairs

The source quaternion theorem constructs the actual square action on U_H.
Its original kernel Q_H gives an injective H/Q_H action in O₄⁺(2). Every
original V actor is an involution with singular displacement. The finite
orthogonal pair theorem therefore recognizes each non-two starred pair
as S₃ without any additional plane-control or F.9 applicability premise.

Source: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOrthogonal
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)

noncomputable def quaternion : QuaternionCentralProductData D.UH :=
  (SourceQuaternion.source13_5_15_five d h e hseed hn hU).2.2.2.2.choose

include d h e hseed hn hU in
theorem center_map : (center D.UH).map D.UH.subtype=D.V₁ := by
  rw [(SourceQuaternion.source13_5_15_five d h e hseed hn hU).2.2.1,
    map_subgroupOf_eq_of_le (show D.V₁≤D.UH from h.point_lt.le.trans (le_conjugateSpanBy _ _))]

include d in
theorem seed_index : D.Vplus.relIndex D.V=2 := by
  have hh := (D.Vplus.subgroupOf D.V).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe d.seed_le).toEquiv,d.seed_card,ReturningPlane.module_card d] at hh
  change (D.Vplus.subgroupOf D.V).index=2
  omega

include h hU in
theorem module_not_le_core : ¬D.V≤D.QH :=
  fun hv=>hU (h.UH_elementary_of_V_le_QH hv).toIsMulCommutative

noncomputable def starEmbedding : Section08.Source.Hstar D.H→*BinaryFourPlus.Wreath :=
  h.closureStarEmbedding (quaternion d h e hseed hn hU) (center_map d h e hseed hn hU)

theorem starEmbedding_injective : Function.Injective (starEmbedding d h e hseed hn hU) :=
  h.closureStarEmbedding_injective _ _

theorem starEmbedding_mk (x : D.H) :
    starEmbedding d h e hseed hn hU (QuotientGroup.mk' (pCore 2 D.H) x)=
      closureOrthogonalAction D.H le_rfl (quaternion d h e hseed hn hU) x := rfl

theorem module_actor_singular (v : D.V) :
    BinaryFourPlus.SingularDisplacements
      (starEmbedding d h e hseed hn hU
        (QuotientGroup.mk' (pCore 2 D.H) (inclusion h.V_le_H v))) := by
  rw [starEmbedding_mk]
  apply (quaternion d h e hseed hn hU).wreath_singular_displacement
  intro u
  apply Subtype.ext
  change (((v:G)*(u:G)*(v:G)⁻¹)*(u:G)⁻¹)^2=1
  let : IsElementaryAbelian 2 D.V := h.elementary
  have hc := h.core_module_commutator_le_seed (seed_index d) (module_not_le_core h hU)
  apply elemPow_eq_one_of_isElementaryAbelian (G:=G) (A:=D.V)
  apply h.plus_le
  rw [show ((v:G)*(u:G)*(v:G)⁻¹)*(u:G)⁻¹=⁅(v:G),(u:G)⁆ from rfl,
    ←commutatorElement_inv]
  exact D.Vplus.inv_mem (hc (commutator_mem_commutator (h.UH_le_QH u.property) v.property))

include d h e hseed hn hU in
theorem original_star_pair_symmetricThree (g : G) (hg : g∈D.H)
    (hpair : ¬IsPGroup 2 (Section08.Source.starImage D.H
      (D.V⊔D.V.map (MulAut.conj g).toMonoidHom))) :
    Nonempty ((Section08.Source.starImage D.H
      (D.V⊔D.V.map (MulAut.conj g).toMonoidHom))≃*Equiv.Perm (Fin 3)) :=
  h.closure_pair_star_symmetricThree (seed_index d) (module_not_le_core h hU) g hg
    (quaternion d h e hseed hn hU) (center_map d h e hseed hn hU) hpair

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOrthogonal
end
