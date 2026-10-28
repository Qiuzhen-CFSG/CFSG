module
public import Theory.Representation.BinaryNaturalDual.FourSeed
public import CFSG.Quasithin.ChapterG.Section11.CorrectedReduction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.EarlierClassification

/-!
# Excluding the exceptional full-four action on the original HS flag

The literal L₁ action moves the marked point of V/V₁: otherwise it would
preserve V₂, contradicting V = ⟨V₂^{L₁}⟩. The original Sylow image preserves
this seed plane and fixes that point. In the full natural-plus-dual GL₄(2)
action every stabilizer of such a plane fixes the point, so the actual
coordinate model is impossible.

This is the ambient exclusion needed by the corrected G.11 reduction. It
uses neither centerlessness nor the later natural SL₂(4) conclusion. The
remaining marked action alternatives and their recognition are still required.
Source: Aschbacher--Smith 12.8.5, 14.3.11 and 14.3.23--24,
printed pp.850,993,999--1000; see the G.10.15 correction in
`docs/quasithin-proof-basis.md`.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem source_seed_stable (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (a : F.H) (ha : (a:G) ∈ normalizer (V : Set G)) (w : Additive F.Uhat)
    (hw : w ∈ hatSpace F V) :
    F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w ∈ hatSpace F V := by
  obtain ⟨b,hb,he⟩ := (show w.toMul ∈ hatImage F V from hw)
  refine ⟨F.uAction a b, (mem_normalizer_iff.mp ha (b:G)).mp hb, ?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction a b) = F.terminalHatAction a w.toMul
  change QuotientGroup.mk' (center F.U) (F.uAction a b) = F.uhatAction a w.toMul
  rw [← F.uhatAction_apply_mk,he]

/-- The natural residual L₁ moves the marked nonzero seed point. -/
theorem source_seed_point_moved (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (v : Additive F.Uhat) (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    ∃ k ∈ F.terminalDot (F.Li L 1), F.terminalRepresentation k v ≠ v := by
  let := chosen.elementary
  obtain ⟨hspan,_,hcenter⟩ := source_seed_geometry d earlier hq chosen F
  have hc := hcenter hne
  by_contra! hfix
  have hn : F.Li L 1 ≤ normalizer (F.Vi 2 : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk b hb
    let a : F.H := ⟨k,(F.Li_le L 1 hk).2⟩
    let bU : F.U := ⟨b,(F.le_seed 2).trans (le_conjugateSpanBy _ _) hb⟩
    let q := QuotientGroup.mk' (center F.U)
    have hbline : Additive.ofMul (q bU) ∈ Submodule.span (ZMod 2) {v} :=
      hline ▸ (show Additive.ofMul (q bU) ∈ hatSpace F (F.Vi 2) from ⟨bU,hb,rfl⟩)
    obtain ⟨c,hcb⟩ := Submodule.mem_span_singleton.mp hbline
    have hkdot : QuotientGroup.mk' F.terminalHatAction.ker a ∈ F.terminalDot (F.Li L 1) :=
      ⟨a,hk,rfl⟩
    have hq : F.terminalHatAction a (q bU) = q bU := by
      have he : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)
          (Additive.ofMul (q bU)) = Additive.ofMul (q bU) := by
        rw [← hcb,map_smul,hfix _ hkdot]
      exact congrArg Additive.toMul he
    have hz : F.uAction a bU * bU⁻¹ ∈ center F.U := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (_ * _) = 1
      rw [map_mul,map_inv,← F.uhatAction_apply_mk]
      change F.terminalHatAction a (q bU) * (q bU)⁻¹ = 1
      rw [hq,mul_inv_cancel]
    have hbV := F.le_seed 2 hb
    have hkV := chosen.normalizes (F.Li_le L 1 hk).1
    have hzV : k*b*k⁻¹*b⁻¹ ∈ V :=
      V.mul_mem ((mem_normalizer_iff.mp hkV b).mp hbV) (V.inv_mem hbV)
    have hzZ : k*b*k⁻¹*b⁻¹ ∈ F.ZU := mem_map_of_mem F.U.subtype hz
    have hz1 : k*b*k⁻¹*b⁻¹ ∈ F.Vi 1 := hc ▸ ⟨hzV,hzZ⟩
    have he := (F.Vi 2).mul_mem (F.monotone (by decide : 1 ≤ 2) hz1) hb
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using he
  have hle : V ≤ F.Vi 2 := hspan.ge.trans (conjugateSpanBy_le le_rfl hn)
  have hh := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  have hcV : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  rw [hcV,F.card 2 (by decide)] at hh
  norm_num at hh

/-- The original natural seed excludes the whole exceptional S₈ action. -/
theorem source_no_full_linear_model (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (H : Subgroup F.TerminalHdot) (I J : Submodule (ZMod 2) (Additive F.Uhat)) :
    ¬ Nonempty (ChapterG.Section11.FullLinearFour.WholeActionModel F.terminalRepresentation H I J) := by
  rintro ⟨m⟩
  let := chosen.elementary
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,_,B,v,hyp,hline,hfix⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  have hP : (P : Subgroup F.TerminalHdot) = F.terminalDot (T : Subgroup G) := rfl
  have hs : ∀ a ∈ P, ∀ w ∈ hatSpace F V, F.terminalRepresentation a w ∈ hatSpace F V := by
    intro a ha w hw
    obtain ⟨b,hb,rfl⟩ := (show a ∈ F.terminalDot (T : Subgroup G) from hP ▸ ha)
    apply source_seed_stable F b _ w hw
    have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := by
      simpa only [F.last] using F.invariant 3
    exact hTV hb
  have hseed : hatSpace F (F.Vi 2) ≤ hatSpace F V := fun _ hw =>
    (show hatImage F (F.Vi 2) ≤ hatImage F V from map_mono (comap_mono (F.le_seed 2))) hw
  have hv : v ∈ hatSpace F V := hseed (hline ▸ Submodule.mem_span_singleton_self v)
  obtain ⟨k,hk,hm⟩ := source_seed_point_moved d earlier hq chosen F hne v hline
  apply hm
  apply BinaryNaturalDual.FourSeed.point_fixed_of_coordinates F.terminalRepresentation
    (BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction (Or.inl rfl))
    m.groupEquiv m.spaceEquiv m.equivariant P (hatSpace F V)
    (seed_hat_dimension F (source_closure d earlier hq chosen structural alternatives F hne).2.2)
    hs v hv (fun a ha => hfix a (hP ▸ ha)) k
  intro w hw
  obtain ⟨b,hb,rfl⟩ := hk
  exact source_seed_stable F b (chosen.normalizes (F.Li_le L 1 hb).1) w hw

/-- Eliminate the exceptional marked row of the corrected G.11 catalogue,
using its literal whole-action coordinates. -/
theorem source_no_full_linear_alternative (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (W : Submodule (ZMod 2) (Additive F.Uhat)) (X : Subgroup F.TerminalHdot)
    (X₀ : Subgroup X) :
    ¬ ChapterG.Section11.FullLinearFour.MarkedAlternative F.terminalRepresentation B v W X X₀ := by
  rintro ⟨H,I,J,m,_⟩
  exact source_no_full_linear_model d earlier hq chosen structural alternatives F hne H I J ⟨m⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
