module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureTransvections
public import CFSG.Quasithin.ChapterG.Section03.SQTKSpanningBlocks

/-!
# Component lifts and block bounds in the original central-closure action

The unchanged H lies in the centralizer of the original involution z and
is therefore SQTK. The actual quotient representation and its marked G.3
blocks consequently have literal C-component lifts in H, dimensions three
through five, and at most two blocks. The full action kernel and original
point are retained; no component or classification input is assumed.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Literal C-component lifts and the source block bounds for the same
original inner-automizer branch and the same whole quotient module. -/
theorem original_tripleSix_central_closure_blocks
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
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
            (∀ g ∈ (U.subgroupOf H).map φ, g x = x) ∧
            (∀ g ∈ (U.subgroupOf H).map φ, ∀ y, g y-y ∈ BinaryTransvectionGroups.centerLine x) ∧
            ChapterG.Section03.FullAction φ.range (MulAction.orbit φ.range x) ∧
            ChapterG.Section03.Decomposition φ.range (MulAction.orbit φ.range x) ∧
            ChapterG.Section03.LocalStructure φ.range (MulAction.orbit φ.range x) ∧
            (∀ i : ChapterG.Section03.OrbitBlock φ.range (MulAction.orbit φ.range x),
              (3 ≤ Module.finrank (ZMod 2) (ChapterG.Section03.blockSpace φ.range (MulAction.orbit φ.range x) i) ∧
                Module.finrank (ZMod 2) (ChapterG.Section03.blockSpace φ.range (MulAction.orbit φ.range x) i) ≤ 5) ∧
              ∃ B : Subgroup H, B.IsCComponent ∧ B.map φ.rangeRestrict =
                (ChapterG.Section03.blockGroup φ.range (MulAction.orbit φ.range x) i).subgroupOf φ.range) ∧
            Nat.card (ChapterG.Section03.OrbitBlock φ.range (MulAction.orbit φ.range x)) ≤ 2 := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_transvections
    h structural D a z hz hzT hnot hinner
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,hker,hcore,hcard,x,hx,hpoint,horbit,hfix,hmove,hfull,hdecomp,hlocal⟩ := hrest
  let := he
  have hHC : H ≤ C :=
    (original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot).1
  let := D.elementary
  have hz1 : (z:G) ≠ 1 := fun hh => hz (Subtype.ext hh)
  have hzorder : orderOf (z:G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property) hz1
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHC)).mp
      ((h.simpleQTKE.involution_centralizer_sqtk hzorder).subgroup (H.subgroupOf C))
  have hspan : Submodule.span (ZMod 2) (MulAction.orbit φ.range x) = ⊤ := by
    have heq : MulAction.orbit φ.range x = Set.range (fun g : φ.range => g.val x) := by
      ext y
      exact MulAction.mem_orbit_iff
    rwa [heq]
  have hlifts := ChapterG.Section03.sqtk_spanning_block_lifts hH φ.range φ.rangeRestrict
    φ.rangeRestrict_surjective x hfull hdecomp hlocal hspan
  have hcount := ChapterG.Section03.sqtk_spanning_block_count hH φ.range φ.rangeRestrict
    φ.rangeRestrict_surjective x hfull hdecomp hlocal hspan
  exact ⟨hHW,hZN,he,φ,hformula,hker,hcore,hcard,x,hx,hpoint,horbit,hfix,hmove,
    hfull,hdecomp,hlocal,hlifts,hcount⟩

end CFSG.Quasithin.Chapter12.Section07
