module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.Selection
/-!
# Natural coordinates on the original moved subgroup

The B.5 natural action equivalence is transported through the literal
commutator-space embedding of [U,L]. The actor marking factors the original
map L → L/O₂(L), retaining the intertwining equation on actual group elements.

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterB.QuasisimpleSource
open Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource.SourceCompletion
open ChapterB.QuasisimpleSource.ExtensionConsequences
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
/-- Natural coordinates for the original component quotient and moved subgroup. -/
theorem HasExchangedLinearSource.original_natural_coordinates
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (_hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (_hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hne : M ≠ Mc) (_hfull : V = localModule T M)
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    IsElementaryAbelian 2 (d.U t) ∧ ∃ hE : IsElementaryAbelian 2 (d.UL t),
      letI := hE
      ∃ hn : d.L ≤ normalizer (d.UL t : Set G),
        ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
          ∃ e : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
            ∃ x : Additive (d.UL t) ≃ₗ[ZMod 2] (Fin n → ZMod 2),
              ∀ (l : d.L) (v : Additive (d.UL t)),
                x (Additive.ofMul (ChapterD.UniqueFactor.actionHom d.L (d.UL t) hn l v.toMul)) =
                  (e (QuotientGroup.mk' (pCore 2 d.L) l)).val.mulVec (x v) := by
  obtain ⟨n,hn,⟨mark⟩⟩ := s.2.2
  let J := d.L ⊔ d.Q1
  let W := (d.U t).subgroupOf J
  let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h
    (s.c27Input hG h) s.cubicFacts t ht
  let := hr.normal
  let := hr.elementary
  let : IsMulCommutative W := inferInstance
  let q := QuotientGroup.mk' (centralizer (W : Set J))
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let B := offenderSubgroup ρ
  let K := ((d.L.subgroupOf J).map q).subgroupOf B
  obtain ⟨hKB,c,hc⟩ := d.exchanged_U_binary_action_cases s.1 hG hM hu h
    (s.c27Input hG h) s.cubicFacts t ht htS hn mark
  obtain ⟨a⟩ := s.original_natural_of_actionCase hG _hempty hM _hmany _hJ hu
    _hne _hfull h t ht htS c n hn hc
  obtain ⟨e0,he0⟩ := d.exchanged_U_component_marking s.1 hG hM hu h
    (s.c27Input hG h) s.cubicFacts t ht htS
  let eK : (d.L ⧸ pCore 2 d.L) ≃* K :=
    e0.trans (subgroupOfEquivOfLe hKB).symm
  let e := eK.trans a.groupEquiv
  have hU : IsElementaryAbelian 2 (d.U t) :=
    d.exchanged_U_elementary s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht
  let := hU
  have hE : IsElementaryAbelian 2 (d.UL t) := IsElementaryAbelian.of_le (d.UL_le_U t)
  let := hE
  let : IsMulCommutative (d.UL t) := inferInstance
  have hnUL : d.L ≤ normalizer (d.UL t : Set G) := normalizer_commutator_ge_right _ _
  have hUJ : d.U t ≤ J :=
    (d.exchanged_U_le_Q1 s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht).trans le_sup_right
  let f : d.UL t →* W := {
    toFun := fun v => ⟨⟨v,hUJ (d.UL_le_U t v.property)⟩,d.UL_le_U t v.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hmem := (s.original_moved_space_and_supplement hG hM hu h t ht htS c).1
  let f' : Additive (d.UL t) →ₗ[ZMod 2] c.sectionData.space.toSubmodule :=
    (f.toAdditive.toZModLinearMap 2).codRestrict _ (fun v => (hmem _).mpr v.toMul.property)
  let b : Additive (d.UL t) ≃ₗ[ZMod 2] c.sectionData.space.toSubmodule :=
    LinearEquiv.ofBijective f' ⟨fun v w he => Additive.toMul.injective (Subtype.ext
      (congrArg (fun v => (v.val.toMul.val : G)) he)),fun v =>
        ⟨Additive.ofMul ⟨(v.val.toMul.val : G),(hmem _).mp v.property⟩,rfl⟩⟩
  let x := b.trans a.linearEquiv
  refine ⟨hU,hE,hnUL,n,hn,e,x,?_⟩
  intro l v
  let k := eK (QuotientGroup.mk' (pCore 2 d.L) l)
  have hk : k.val.val = q ⟨l,mem_sup_left l.property⟩ := he0 l
  have hb : b (Additive.ofMul (ChapterD.UniqueFactor.actionHom d.L (d.UL t) hnUL l v.toMul)) =
      c.sectionData.space.toRepresentation k (b v) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * (v.toMul : G) * (l : G)⁻¹ = ((ρ k.val.val (f' v).val).toMul.val : G)
    rw [hk,NormalElementaryQuotient.representation_apply]
    rfl
  change a.linearEquiv (b (Additive.ofMul (ChapterD.UniqueFactor.actionHom d.L (d.UL t) hnUL l v.toMul))) = _
  exact (congrArg a.linearEquiv hb).trans (a.intertwines k (b v))
end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
