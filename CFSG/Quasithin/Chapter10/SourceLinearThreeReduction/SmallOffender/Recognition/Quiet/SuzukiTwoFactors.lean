module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.SuzukiFFRows
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SuzukiCentralizer

/-!
# The remaining two-factor case in the quiet Suzuki centralizer

The original Suzuki component has zero fixed space on the literal full module.
Its image commutes with the offender subgroup of the orbit centralizer. The
doubled-SL₃ centralizer exclusion therefore removes the quasisimple alternative
from the large-section reduction, leaving the actual B.5.6(3) two-factor case.
The final theorem connects that remaining case to the original small offender.

Source: Aschbacher–Smith 10.1.1 and 10.2.12 (printed pp.741–742, 754–755).
The two-factor exclusion remains with qt-d-10-nona5-small-offender. The independent
half-Sylow input retains producer qt-d-10-nona5-half-sylow-unique and its existing
final discharge by qt-d-10-nona5-point-control.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 BenderSuzuki.MatrixGroups PointControl.Selection
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem quiet_suzuki_centralizer_two_factors
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let C := centralizer (X : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))
    let N := offenderSubgroup (ρ.comp C.subtype)
    let σ := (ρ.comp C.subtype).comp N.subtype
    Nonempty (SourceTwoFactorCase σ) := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let Q := M ⧸ centralizer (U : Set M)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let C := centralizer (X : Set Q)
  let N := offenderSubgroup (ρ.comp C.subtype)
  let f := C.subtype.comp N.subtype
  let A := L.subgroupOf M
  let S := A.map q
  have hLM : L ≤ M := (le_componentOrbit L T).trans R.le_normalizer
  obtain ⟨a⟩ := ModuleChoice.full_action_original_component_equiv D c.nonnormal
  let eS : S ≃* SuzukiMatrixGroup m := a.trans e
  have hfull := quiet_suzuki_moved_eq_full D c hJ hNL hm e
  have hz := quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ
  rw [hfull] at hz
  have hfixS : fixedSpace ρ S = ⊥ := by
    apply bot_unique
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    apply hz.le
    refine ⟨v.toMul.property,?_⟩
    intro l hl
    let lM : M := ⟨l,hLM hl⟩
    have hh := hv ⟨q lM,mem_map_of_mem q hl⟩
    have hact := ChapterB.InternalThompsonAction.action_apply U lM v
    have he : l * (v.toMul : G) * l⁻¹ = (v.toMul : G) := by
      exact (congrArg (fun x : M => (x : G)) hact).symm.trans
        (congrArg (fun x : Additive U => ((x.toMul : M) : G)) hh)
    exact mul_inv_eq_iff_eq_mul.mp he
  have hSX : S ≤ X := map_mono (comap_mono (le_componentOrbit L T))
  have hc : f.range ≤ centralizer (S : Set Q) := by
    rintro _ ⟨n,rfl⟩ s hs
    exact n.val.property s (hSX hs)
  rcases quiet_suzuki_centralizer_ff_rows D c hJ hNL hm e with h | ⟨d,F,_,⟨mark⟩⟩
  · exact h
  exact (not_doubleThree_of_commuting_suzuki ρ S (by omega) eS hfixS f hc _ d F mark).elim

/-- Apply the remaining concrete FF alternatives to the original survivor
contract. Half-Sylow uniqueness remains an independent earlier source input. -/
theorem nonnormalSmallOffender_or_quiet_suzuki_two_factors
    (hhalf : PointControl.HalfSylowUniqueAt T) :
    SourceNonnormalSmallOffenderAt T ∨
    (∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) ∧
      normalizer (L : Set G) ≤ D.maximalLocal ∧
      ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) ∧
        (let U := D.fullModule.subgroupOf D.maximalLocal
         let := (source_full_module_reduced D).normal
         let := (source_full_module_reduced D).elementary
         let q := ChapterB.InternalThompsonAction.actionMk U
         let ρ := ChapterB.InternalThompsonAction.action U
         let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
         let C := centralizer (X : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))
         let N := offenderSubgroup (ρ.comp C.subtype)
         Nonempty (SourceTwoFactorCase ((ρ.comp C.subtype).comp N.subtype)))) := by
  rcases nonnormalSmallOffender_or_quiet_suzuki hhalf with hs | h
  · exact Or.inl hs
  obtain ⟨L,D,g,c,hJ,hNL,m,hm,he,_,_,_⟩ := h
  exact Or.inr ⟨L,D,g,c,hJ,hNL,m,hm,he,
    quiet_suzuki_centralizer_two_factors D c hJ hNL hm he.some⟩

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
