module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterRank
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOrbit
public import CFSG.Quasithin.ChapterG.Section03.CommonAxisSource
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
import Theory.GroupTheory.QuotientActionCentralizer

/-!
# The actual common axis in the central-involution branch

When the original closure induces exactly two automorphisms of U, its
literal centralizer of U has index two. Its image in W/<z> is therefore
an actual hyperplane fixed by the entire original U-image. This constructs
the common axis and all dual G.3.1 conclusions, retaining the original
point orbit, conjugation formula and complete action kernel.

Source: Aschbacher--Smith12.7.18, printed p.845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine order-two closure automizer supplies the literal common
axis and the dual source conclusions without an assumed axis or recognition. -/
theorem original_tripleSix_central_closure_axes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hsmall : Nat.card (inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G))))) = 2) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 R
    let Z := zpowers (z:G)
    ∃ (hHW : H ≤ normalizer (W : Set G)) (hZN : (Z.subgroupOf W).Normal),
      letI := hZN
      ∃ he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := he
        ∃ φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] Additive (W ⧸ Z.subgroupOf W)),
          (∀ (g : H) (w : W), φ g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩)) ∧
          (∀ g : H, g ∈ φ.ker ↔ ∀ w ∈ W, ⁅w,(g:G)⁆ ∈ Z) ∧ pCore 2 φ.range = ⊥ ∧
          (Nat.card ((U.subgroupOf H).map φ) = 4 ∨ Nat.card ((U.subgroupOf H).map φ) = 16) ∧
          ∃ x : Additive (W ⧸ Z.subgroupOf W), x ≠ 0 ∧
            Submodule.span (ZMod 2) {x} = AddSubgroup.toZModSubmodule 2
              (Subgroup.toAddSubgroup ((V1.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
            Submodule.span (ZMod 2) (Set.range (fun g : φ.range => g.val x)) = ⊤ ∧
            ∃ f : Module.Dual (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)), f ≠ 0 ∧
              f.ker = AddSubgroup.toZModSubmodule 2
                (Subgroup.toAddSubgroup (((W ⊓ centralizer (U : Set G)).subgroupOf W).map
                  (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
              (∀ g ∈ (U.subgroupOf H).map φ, ∀ v ∈ f.ker, g v = v) ∧
              ChapterG.Section03.FullAction (BinaryTransvectionGroups.dualGroup φ.range)
                (MulAction.orbit (BinaryTransvectionGroups.dualGroup φ.range) f) ∧
              ChapterG.Section03.Decomposition (BinaryTransvectionGroups.dualGroup φ.range)
                (MulAction.orbit (BinaryTransvectionGroups.dualGroup φ.range) f) ∧
              ChapterG.Section03.LocalStructure (BinaryTransvectionGroups.dualGroup φ.range)
                (MulAction.orbit (BinaryTransvectionGroups.dualGroup φ.range) f) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_orbit h structural D a z hz hzT hnot
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,hker,hcore,x,hx,hspan,horbit⟩ := hrest
  let := he
  obtain ⟨N,hN,hmem,_,_,_,_,hcard,_,_⟩ :=
    original_tripleSix_central_closure_rank h structural D a z hz hzT hnot
  let : N.Normal := hN
  have hk : φ.ker = N := by ext g; exact (hker g).trans (hmem g).symm
  have heq : Nat.card ((U.subgroupOf H).map φ) =
      Nat.card ((U.subgroupOf H).map (QuotientGroup.mk' N)) := by
    apply le_antisymm
    · apply card_map_le_card_map_of_ker_le
      rw [QuotientGroup.ker_mk',hk]
    · apply card_map_le_card_map_of_ker_le
      rw [QuotientGroup.ker_mk',hk]
  have hcard' : Nat.card ((U.subgroupOf H).map φ) = 4 ∨ Nat.card ((U.subgroupOf H).map φ) = 16 :=
    heq.symm ▸ hcard
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hWH : W ≤ H := hc.2.2.1.trans (pCoreIn_le 2 H)
  have hp := tripleSixPoint_properties D a z hz
  have hZW : Z ≤ W := (zpowers_le.mpr hp.1).trans (le_conjugateSpanBy V1 R)
  let V := Additive (W ⧸ Z.subgroupOf W)
  let ρ : Representation (ZMod 2) H V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp φ
  let q := QuotientGroup.mk' (Z.subgroupOf W)
  let c : BinaryConjugationSection H W Z ρ :=
    { section_le := hWH
      kernel_le := hZW
      normalized := hHW
      coordinates := q
      onto := QuotientGroup.mk'_surjective _
      kernel_eq := QuotientGroup.ker_mk' _
      equivariant := fun g w => (hformula g w).symm }
  let B := W ⊓ centralizer (U : Set G)
  let := D.elementary
  have hZB : Z ≤ B := by
    refine le_inf hZW (zpowers_le.mpr ?_)
    intro u hu
    exact congrArg Subtype.val (mul_comm (⟨u,hu⟩ : U) z)
  have hWT : W ≤ (T : Subgroup G) :=
    (original_tripleSix_central_closure_automizer_cases h structural D a z hz hzT hnot).1
  have hWN : W ≤ normalizer (U : Set G) := hWT.trans (((structural K h).2.2 U D).1)
  have hsize : Nat.card (inducedAutomizer U W) =
      (centralizer (U : Set G)).relIndex W := by
    rw [inducedAutomizer,←relIndex_ker,MonoidHom.ker_rangeRestrict,
      normalizerMonoidHom_ker,relIndex_subgroupOf hWN]
  have hidx : B.relIndex W = 2 := by
    rw [show B = W ⊓ centralizer (U : Set G) from rfl,inf_comm,inf_relIndex_right]
    exact hsize.symm.trans hsmall
  let E := c.imageSpace B
  have hd : Module.finrank (ZMod 2) E + 1 = Module.finrank (ZMod 2) V :=
    c.imageSpace_codimension_of_index B inf_le_left hZB 1 (by simpa using hidx)
  have hEt : E ≠ ⊤ := by
    intro ht
    rw [ht,finrank_top] at hd
    omega
  obtain ⟨f,hf,hEf⟩ := E.exists_le_ker_of_lt_top hEt.lt_top
  have hE : E = f.ker := Submodule.eq_of_le_of_finrank_eq hEf (by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega)
  have hcomm : ⁅U,B⁆ ≤ Z := by
    have hh : ⁅B,U⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
    rw [commutator_comm,hh]
    exact bot_le
  have hfix : ∀ g ∈ (U.subgroupOf H).map φ, ∀ v ∈ f.ker, g v = v := by
    rintro _ ⟨g,hg,rfl⟩ v hv
    have hvE : v ∈ E := hE.symm ▸ hv
    exact c.fixed_on_imageSpace_of_commutator_le U B hcomm g hg v hvE
  have hAH : (U.subgroupOf H).map φ ≤ φ.range := map_le_range _ _
  have hlarge : 2 < Nat.card ((U.subgroupOf H).map φ) := by rcases hcard' with hh | hh <;> omega
  have hs := ChapterG.Section03.source_conclusions_of_common_axis hcore f hf
    ((U.subgroupOf H).map φ) hAH hlarge hfix
  exact ⟨hHW,hZN,he,φ,hformula,hker,hcore,hcard',x,hx,hspan,horbit,f,hf,hE.symm,hfix,hs⟩

end CFSG.Quasithin.Chapter12.Section07
