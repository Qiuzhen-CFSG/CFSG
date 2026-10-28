module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Terminal
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction

/-!
# The original marked point stabilizer

When Z(U) is the first flag point, the preimage of the marked line in U/Z(U)
is exactly V₂. Its point stabilizer is therefore the literal image of H∩G₂.
The earlier relative-normality theorem puts the conjugate actor normally in
this whole point stabilizer, as required by G.11 and the marked model rows.

Source: Aschbacher--Smith, 12.8.12(2), G.11.1 and 14.4.2,
printed pp.855,364,1006.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The exact point stabilizer, retaining the original central quotient and
the original plane normalizer. -/
theorem source_point_stabilizer (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (hZ : F.ZU = F.Vi 1)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    ChapterG.Section10.pointCentralizer F.terminalRepresentation v =
      F.terminalDot (F.H ⊓ F.Gi 2) := by
  have hVU : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  have hcenter : center F.U ≤ (F.Vi 2).subgroupOf F.U := by
    intro z hz
    exact F.monotone (by omega : 1 ≤ 2) (hZ ▸ (show (z:G) ∈ F.ZU from ⟨z,hz,rfl⟩))
  have hpre : (hatImage F (F.Vi 2)).comap (QuotientGroup.mk' (center F.U)) =
      (F.Vi 2).subgroupOf F.U := by
    rw [hatImage, comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hcenter]
  have hconj (a : F.H)
      (ha : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) v = v)
      (w : G) (hw : w ∈ F.Vi 2) : (a:G) * w * (a:G)⁻¹ ∈ F.Vi 2 := by
    let wU : F.U := ⟨w,hVU hw⟩
    have hwP : hatElement F wU ∈ hatSpace F (F.Vi 2) := ⟨wU,hw,rfl⟩
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline.symm ▸ hwP)
    have him : hatElement F (F.uAction a wU) ∈ hatSpace F (F.Vi 2) := by
      have he : hatElement F (F.uAction a wU) =
          F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) (hatElement F wU) :=
        congrArg Additive.ofMul (F.uhatAction_apply_mk a wU).symm
      rw [he, ← hc, map_smul, ha]
      exact (hatSpace F (F.Vi 2)).smul_mem c (hline ▸ Submodule.mem_span_singleton_self v)
    have hm : F.uAction a wU ∈ (hatImage F (F.Vi 2)).comap (QuotientGroup.mk' (center F.U)) := him
    rw [hpre] at hm
    exact hm
  ext x
  constructor
  · intro hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker x
    refine ⟨a, ⟨a.property, ?_⟩, rfl⟩
    apply mem_normalizer_iff.mpr
    intro w
    refine ⟨hconj a hx w, fun hw => ?_⟩
    have hi : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a⁻¹) v = v := by
      have hi := (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).inv_mem hx
      change F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)⁻¹ v = v at hi
      simpa only [map_inv] using hi
    have hh := hconj a⁻¹ hi ((a:G)*w*(a:G)⁻¹) hw
    simpa only [coe_inv, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel, mul_one] using hh
  · rintro ⟨a,ha,rfl⟩
    have hvP : v ∈ hatSpace F (F.Vi 2) := hline ▸ Submodule.mem_span_singleton_self v
    obtain ⟨w,hw,he⟩ := (show v.toMul ∈ hatImage F (F.Vi 2) from hvP)
    have haw : (F.uAction a w : G) ∈ F.Vi 2 := (mem_normalizer_iff.mp ha.2 (w:G)).mp hw
    have him : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) v ∈
        hatSpace F (F.Vi 2) := by
      refine ⟨F.uAction a w,haw,?_⟩
      change QuotientGroup.mk' (center F.U) (F.uAction a w) = F.uhatAction a v.toMul
      rw [← F.uhatAction_apply_mk,he]
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline.symm ▸ him)
    have hc0 : c ≠ 0 := by
      intro hzero
      rw [hzero,zero_smul] at hc
      have hh := congrArg (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)⁻¹) hc
      rw [map_zero,← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply] at hh
      exact hv hh.symm
    have hc1 : c = 1 := (show ∀ c : ZMod 2, c = 0 ∨ c = 1 from by decide) c |>.resolve_left hc0
    change F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) v = v
    simpa only [hc1,one_smul] using hc.symm

/-- The conjugate actor is relatively normal in the whole marked point
stabilizer, with 12.8.12(2)'s premises supplied by the original source. -/
theorem source_actor_normal_in_point_stabilizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    F.terminalDot (F.X g) ≤ ChapterG.Section10.pointCentralizer F.terminalRepresentation v ∧
      ((F.terminalDot (F.X g)).subgroupOf
        (ChapterG.Section10.pointCentralizer F.terminalRepresentation v)).Normal := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hindex, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  obtain ⟨z,hz,hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hn := actors_normal_in_dot_H2 F (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex) g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
    F.terminalHatAction F.terminalHatAction_apply_mk
  rw [source_point_stabilizer F hZ v hv hline]
  exact ⟨hn.1,hn.2.1⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
