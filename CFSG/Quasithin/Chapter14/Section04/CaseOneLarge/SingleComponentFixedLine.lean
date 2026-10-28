module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.MathieuComponentExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineModule
public import CFSG.Quasithin.ChapterG.Section11.WholeBinaryG2

/-!
# The fixed-line clause for an original normal irreducible component

Without a low-rank witness the original cyclic-module argument gives degree
at least eight. The actual A₇ and G₂(2)′ degree catalogues and component
rank bounds exclude those carriers. The original component reduction then
leaves the triple M₂₂ cover in degree twelve. Its whole-group coordinates
and source contradiction discharge that last branch, proving the low-rank
clause for every normal component acting irreducibly on the original module.

Normality and irreducibility are branch conditions, not conclusions asserted
for every component. Multiplicity and the remaining low-rank branch still
belong to catalogue assembly.

Source: Aschbacher--Smith G.9.3, G.11.1(3), G.11.7 and 14.4.2,
printed pp.354,364,367--368,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension
open LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

private theorem not_small_component_of_degree_ge_eight
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {X C : Subgroup D}
    [IsElementaryAbelian 2 X]
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X C C
      (finrank (ZMod 2) (Additive X)))
    (hd : 8 ≤ finrank (ZMod 2) W)
    (he : Nonempty (C ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  have hu := h9.single_component_degree_bound
  rcases he with he | he
  all_goals obtain ⟨e⟩ := he
  · rw [primeRank_equiv 2 (MulAut.congr e)] at hu
    have hb := ChapterG.Section07.AlternatingSevenCover.alternating_seven_automorphism_two_rank
    let σ := (ρ.comp C.subtype).comp e.symm.toMonoidHom
    let : IsIrreducible σ :=
      (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
    have hf : Function.Injective σ :=
      h9.faithful.comp (C.subtype_injective.comp e.symm.injective)
    have hs := ChapterK.Alternating.sevenSmallDegreeSpectrum σ hf inferInstance (by omega)
    rcases hs with hs | hs | hs <;> omega
  · rw [primeRank_equiv 2 (MulAut.congr e)] at hu
    have hb := Atlas.G2.binary_derived_automorphism_two_rank_le_three
    let σ := (ρ.comp C.subtype).comp e.symm.toMonoidHom
    let : IsIrreducible σ :=
      (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
    obtain ⟨Ω,hΩ,τ,o,K,hK,hstab,htrans,hfil⟩ :=
      G2DerivedPermutationFiltration.exists_permutation_filtration
    let := hΩ
    have hs := BinaryPermutation.finrank_mem_of_factorDegreeFiltration
      τ o K hK hstab htrans hfil σ
    change finrank (ZMod 2) W=1 ∨ finrank (ZMod 2) W=6 ∨ 8<finrank (ZMod 2) W at hs
    omega

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- For the literal normal irreducible component, the fixed-line clause
without a low-rank witness forces the actual triple M₂₂ cover and degree twelve. -/
theorem source_large_single_component_of_no_lowRank (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) :
    Chapter1.Section02.LocalModels.IsM22Cover C ∧ finrank (ZMod 2) (Additive F.Uhat) = 12 := by
  have hd := (source_fixed_line_module d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH B v hyp hline hn).2.1
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
  rcases source_large_single_component_models d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH C hC hm hirr with ⟨_,he | he | hf⟩ | hc
  · exact (not_small_component_of_degree_ge_eight h9 hd (.inl he)).elim
  · exact (not_small_component_of_degree_ge_eight h9 hd (.inr he)).elim
  · exact (source_no_mathieu_twenty_two_component d earlier hq chosen structural alternatives
      F hne g hgP hgH C hC hm hirr hf.2.some).elim
  · exact hc

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension
open LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- A normal irreducible component on the original large flag forces the
low-rank clause; the separate fixed-line clause is excluded by the actual
Mathieu whole-group recognition and source contradiction. -/
theorem source_large_single_component_lowRank (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) :
    ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  by_contra hn
  obtain ⟨model,hd⟩ := source_large_single_component_of_no_lowRank d earlier hq chosen
    structural alternatives F hne hZ hlarge g hgP hgH B v hyp hline hn C hC hm hirr
  exact source_no_triple_mathieu_component d earlier hq chosen structural alternatives
    classification F hne hZ hlarge C hirr model hd

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension
open LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- After the original source exclusions, a normal irreducible component can
only be A₇ or G₂(2)′, on a six-dimensional quotient. This is the remaining
small-degree branch, not a marked-catalogue exhaustiveness theorem. -/
theorem source_large_single_component_six (d : Counterexample T L)
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
      (Nonempty (C ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2)))) := by
  have hsmall : Nonempty (C ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
    rcases source_large_single_component_models d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH C hC hm hirr with ⟨_,he | he | hf⟩ | hc
    · exact .inl he
    · exact .inr he
    · exact (source_no_mathieu_twenty_two_component d earlier hq chosen structural alternatives
        F hne g hgP hgH C hC hm hirr hf.2.some).elim
    · exact (source_no_triple_mathieu_component d earlier hq chosen structural alternatives
        classification F hne hZ hlarge C hirr hc.1 hc.2).elim
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
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
  have hlt : finrank (ZMod 2) (Additive F.Uhat) < 8 :=
    Nat.lt_of_not_ge (fun hd => not_small_component_of_degree_ge_eight h9 hd hsmall)
  have hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
    have hcenter := (source_extraspecial_order d earlier hq chosen structural alternatives
      F hne hZ).1.center_order_p
    have hc : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
      rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hcenter]
      change Nat.card (Additive F.Uhat) * 2 = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,pow_succ]
    by_contra hn
    have hb := Nat.pow_le_pow_right (n := 2) (by decide)
      (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 6)
    rw [← hc] at hb
    norm_num at hb
    omega
  have heven := AlternatingForm.even_finrank B hyp.alternating hyp.nondegenerate
  exact ⟨by obtain ⟨n,hn⟩ := heven; omega,hsmall⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

