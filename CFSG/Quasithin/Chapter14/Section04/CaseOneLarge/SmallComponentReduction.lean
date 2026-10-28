module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SingleComponentFixedLine
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeSeven

/-!
# The remaining binary G₂ component on the original large flag

The previous exclusions leave only A₇ and G₂(2)′. Their small-degree
catalogues, the large extraspecial order and parity force degree six.
The original point-centralizer three-rank bound then excludes A₇ via the
seven-point transvection calculation, retaining the literal relative quotient.

The final theorem leaves only the actual G₂(2)′ component in degree six.
It is a component-branch reduction, not marked-catalogue exhaustiveness:
that small-degree exclusion and the multiplicity branches remain open.

The seven-point transport adapts ChapterG.Section11.LargeWholeSeven using
the original extraspecial point-centralizer bound in place of its
nonextraspecial smaller-actor condition.
Source: Aschbacher--Smith 12.8.13(8), G.9.3, G.11.7 and 14.4.2,
printed pp.856,354,367--368,1006--1007; refs/quasithin.pdf.
-/


public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SevenComponent
open ChapterG BinaryPermutation SevenParabolic Representation.BinaryOffender
private theorem binary_rank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Group.rank A = finrank (ZMod 2) (Additive A) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply le_antisymm (IsElementaryAbelian.rank_le_finrank (p := 2) A)
  have hc : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← hc]
  exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)))


/-- The actual whole A₇ action contradicts the bound on the original point stabilizer. -/
private theorem not_seven_of_point_rank_le_one
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X Z L : Subgroup G}
    [IsElementaryAbelian 2 X] {C : GroupClass}
    (h : Section10.Hypothesis ρ B v W X (Z.subgroupOf X))
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hd : 6 ≤ finrank (ZMod 2) V) (hZX : Z ≤ X)
    (hpoint : primeRank 3 (Section10.pointCentralizer ρ v) ≤ 1)
    (eK : L ≃* alternatingGroup (Fin 7)) : False := by
  let := h9.normal_H
  have hu := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr eK)] at hu
  have hb := Section07.AlternatingSevenCover.alternating_seven_automorphism_two_rank
  let σ := (ρ.comp L.subtype).comp eK.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eK.symm.toMonoidHom eK.symm.surjective _).mpr h9.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp eK.symm.injective)
  have hs := ChapterK.Alternating.sevenSmallDegreeSpectrum σ hf inferInstance (by omega)
  have hdim : finrank (ZMod 2) V = 6 := by rcases hs with hs | hs | hs <;> omega
  obtain ⟨f⟩ := ChapterK.Alternating.SevenSixSpace.of_point_fixed_or_dual σ hdim
    (ChapterK.Alternating.SevenSixSpace.fixed_or_dual
      ChapterK.Alternating.SevenSixSpace.pointSimpleDegrees _ hdim)
  let c := coreEquivNatural (Fin 7) (by decide)
  let eV := f.toLinearEquiv.trans c.symm
  have he (l : L) (u : V) : eV (ρ l u) =
      alternatingCoreRepresentation (Fin 7) (eK l) (eV u) := by
    apply c.injective
    change c (c.symm (f (ρ l u))) =
      c (alternatingCoreRepresentation (Fin 7) (eK l) (c.symm (f u)))
    rw [c.apply_symm_apply]
    have hh := coreEquivNatural_equivariant (Fin 7) (by decide) (eK l).val (c.symm (f u))
    change c (alternatingCoreRepresentation (Fin 7) (eK l) (c.symm (f u))) =
      alternatingNaturalRepresentation (Fin 7) (eK l) (c (c.symm (f u))) at hh
    rw [hh,c.apply_symm_apply]
    have hh := IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (eK l) u
    change f (ρ (eK.symm (eK l)) u) = alternatingNaturalRepresentation (Fin 7) (eK l) (f u) at hh
    rwa [eK.symm_apply_apply] at hh
  obtain ⟨f,hf,hfK,hact⟩ := faithful_extension L ρ h.faithful eK eV he
  have hAlt : alternatingGroup (Fin 7) ≤ f.range := by
    intro a ha
    obtain ⟨k,hk⟩ := eK.surjective ⟨a,ha⟩
    exact ⟨k,by rw [hfK,hk]⟩
  have hform (u w : V) : B u w = pairing (eV u) (eV w) :=
    marked_form_eq L ρ eK eV he B h.nondegenerate (fun k => h.preserves k) u w
  have hv : eV v ≠ 0 := fun hh => h.point_ne_zero (eV.injective (hh.trans eV.map_zero.symm))
  have hmapFix : (fixedSpace ρ X).map eV.toLinearMap = fixedSpace (action.comp f) X := by
    ext w
    obtain ⟨u,rfl⟩ := eV.surjective w
    rw [Submodule.mem_map_equiv,eV.symm_apply_apply]
    constructor
    · intro hu x
      change action (f x) (eV u) = eV u
      rw [← hact]
      exact congrArg eV (hu x)
    · intro hu x
      apply eV.injective
      change eV (ρ (x:G) u) = eV u
      rw [hact]
      exact hu x
  have hfixed : W.map eV.toLinearMap ⊓ fixedSpace (action.comp f) X =
      Submodule.span (ZMod 2) {eV v} := by
    have hh := congrArg (fun P : Submodule (ZMod 2) V => P.map eV.toLinearMap) h.fixedSpace_in_W
    rwa [Submodule.map_inf _ eV.injective,hmapFix,Submodule.map_span,Set.image_singleton] at hh
  apply exclude f hf hAlt X X Z le_rfl hZX (W.map eV.toLinearMap) (eV v) hv
  · intro x hx
    rw [← hact]
    exact congrArg eV (h.fixes_point hx)
  · rintro _ ⟨u,hu,rfl⟩ _ ⟨w,hw,rfl⟩
    exact (hform u w).symm.trans (h.isotropic u hu w hw)
  · rintro x hx _ ⟨u,hu,rfl⟩
    change action (f x) (eV u) - eV u ∈ Submodule.span (ZMod 2) {eV v}
    obtain ⟨l,_,hl⟩ := h.transvections ⟨x,hx⟩
    rw [← hact,hl ⟨u,hu⟩,map_add,map_smul,add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact hfixed
  · intro x hx w hw
    obtain ⟨u,rfl⟩ := eV.surjective w
    rw [← hact,← map_sub]
    exact Submodule.mem_map_of_mem (h.displacement ⟨x,hx⟩ u ((hform v u).trans hw))
  · rw [eV.finrank_map_eq]
    have hh := h.dimension
    rwa [binary_rank,hdim] at hh
  · intro hp
    have he : (pointStabilizer (eV v)).comap f = Section10.pointCentralizer ρ v := by
      ext x
      change action (f x) (eV v) = eV v ↔ ρ x v = v
      rw [← hact,eV.injective.eq_iff]
    rw [he] at hp
    omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SevenComponent

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original point-centralizer bound excludes the A₇ component
using the seven-point transvection calculation. -/
theorem source_no_alternating_seven_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hd : finrank (ZMod 2) (Additive F.Uhat) = 6)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (e₀ : C ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨_,_,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  let P := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hHc : F.H ≤ centralizer (F.ZU : Set G) := by
    rw [hZ]
    exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hD : D = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact mem_map_of_mem _ (hHc b.property)
  have hu := CaseOneHS.source_center_centralizing_point_image_three_rank_le_one
    d earlier hq chosen structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (P.subgroupOf D) ≤ 1 at hu
  have hpD : P ≤ D := by rw [hD]; exact le_top
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe hpD)] at hu
  exact SevenComponent.not_seven_of_point_rank_le_one hyp h9 (by omega)
    (map_mono (fun _ hx => F.conjugate_ZU_le_X g hx)) hu e₀

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension
open LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- The normal irreducible component branch reduces to the literal binary
G₂-derived component in dimension six. Other component and multiplicity
branches, and exclusion of this final small-degree branch, remain open. -/
theorem source_large_single_component_binary_g2 (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) :
    finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
      Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨hd,he | he⟩ := source_large_single_component_six d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH C hC hm hirr
  · exact (source_no_alternating_seven_component d earlier hq chosen structural alternatives
      F hne hZ hd g hgP hgH C hC hm hirr he.some).elim
  · exact ⟨hd,he⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
