module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ClassicalExclusion
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeModels
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.ElementaryFixed

/-!
# Remaining normal irreducible components of the original large action

Apply the full G.9 carrier catalogue to the literal normal component. The
proved Bender, symplectic and G₂ exclusions cover both G.11 fixed-point
clauses. Self-duality excludes the binary linear-three and linear-five rows;
the actual small-degree catalogues and relative Sylow normality remove the
remaining odd and sporadic families. An elementary sixteen in Aut(M₁₂)
fixes at least two dimensions, excluding its fixed-line branch as well.

The surviving simple carriers are A₇, A₈, G₂(2)′ and fixed-line M₂₂. Among
central covers only the literal triple M₂₂ remains, and its minimum degree
and automorphism rank force degree twelve. The final theorem derives this
list from the original flag, with normality and component irreducibility as
branch conditions. It does not assert that those conditions always hold,
identify the remaining whole-group actions, or exhaust the marked catalogue.

Source: Aschbacher--Smith G.9.3, G.11.6--7 and 14.4.2,
printed pp.353--356,365--368,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SingleComponent
open ChapterG ChapterG.Section11 ChapterG.Section09
open ChapterG.Section09.DefiningCharacteristic Chapter1.Section02.LocalModels

open LargeWhole (SmallCarrier)

variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {B : LinearMap.BilinForm (ZMod 2) W}
  {v : W} {E : Submodule (ZMod 2) W} {X C : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

private theorem triple_degree
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple ρ X C C
      (finrank (ZMod 2) (Additive X))) (model : IsM22Cover C) :
    finrank (ZMod 2) W = 12 := by
  let : IsQuasisimple C := h9.component.2
  have hr := TwistedExclusions.actor_rank_le_of_central_quotient h9 model.2.2.some
    Sporadic.Mathieu.m22_automorphism_twoRank_le_five
  have hc : Nat.card (center C) = 3 :=
    (Nat.card_congr model.2.1.some.toEquiv).trans (by simp)
  obtain ⟨e⟩ := Sporadic.Mathieu.M22TripleCover.nonempty_mulEquiv hc model.2.2
  let σ := (ρ.comp C.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  have hl := Sporadic.Mathieu.M22TripleCover.faithful_irreducible_finrank_ge_twelve σ
    (h9.faithful.comp (C.subtype_injective.comp e.symm.injective))
  have hu := h9.degree_le
  omega

open Sporadic.Mathieu Representation.MathieuSmall
open ChapterH.Section10To12.M12Calculations in
private theorem not_mathieu_fixed_line
    (h : Section10.Hypothesis ρ B v E X X₀)
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple ρ X C C
      (finrank (ZMod 2) (Additive X)))
    (hfixed : fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (e : C ≃* M12) : False := by
  let := h9.normal_H
  let := h9.irreducible
  have hd := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hd
  have hb := M12AutomorphismRank.twoRank_le_four
  let σ := (ρ.comp C.subtype).comp e.symm.toMonoidHom
  obtain ⟨f⟩ := Representation.MathieuSmall.M12Recognition.equiv_heart_of_faithful_finrank_le_ten
    σ (h.faithful.comp (C.subtype_injective.comp e.symm.injective)) (by omega)
  have hf (l : C) (u : W) : f (ρ l u) = m12HeartRepresentation (e l) (f u) := by
    have hh := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (e l) u
    change f (ρ (e.symm (e l)) u) = m12HeartRepresentation (e l) (f u) at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  let φ : D →* MulAut M12 := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := C))
  have hφ (g : D) (u : W) : f (ρ g u) = Ambient.automorphismRepresentation (φ g) (f u) :=
    BinaryNormalExtension.equivariant ρ C m12HeartRepresentation
      Ambient.automorphismRepresentation Ambient.automorphismRepresentation_inner
      (fun c hc => Ambient.heart_centralizer c hc) e f.toLinearEquiv hf g u
  have hφi : Function.Injective φ := by
    apply (injective_iff_map_eq_one _).mpr
    intro g hg
    apply h.faithful
    ext u
    apply f.injective
    rw [map_one,Module.End.one_apply]
    change f (ρ g u) = f u
    simpa only [hg,map_one,Module.End.one_apply] using hφ g u
  have hr := h9.toSetup.rank_le_automorphisms (L := C) (by
    rw [normalizer_eq_top_iff.mpr h9.normal_H]; exact le_top)
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  have hdim : finrank (ZMod 2) W = 10 := f.toLinearEquiv.finrank_eq.trans finrank_m12Heart
  have hdegree := h9.degree_le
  have hc : Nat.card (X.map φ) = 16 := by
    rw [card_map_of_injective hφi,h9.card_actor,
      show finrank (ZMod 2) (Additive X) = 4 by omega]
    norm_num
  let : IsElementaryAbelian 2 (X.map φ) := IsElementaryAbelian.map φ
  have htwo := Ambient.ElementaryFixed.two_le_fixed_of_sixteen (X.map φ) hc
  have heq := fixedCodim_map_equivariant ρ Ambient.automorphismRepresentation φ
    f.toLinearEquiv hφ X
  have h1 := fixedCodim_add_finrank ρ X
  have h2 := fixedCodim_add_finrank Ambient.automorphismRepresentation (X.map φ)
  rw [hfixed,finrank_span_singleton h.point_ne_zero,hdim] at h1
  rw [← heq,finrank_m12Heart] at h2
  omega

private theorem remaining
    (h : Section10.Hypothesis ρ B v E X X₀)
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple ρ X C C
      (finrank (ZMod 2) (Additive X)))
    (hS : NormalSylow ρ v X) (hd : 6 ≤ finrank (ZMod 2) W)
    (halt : fixedSpace ρ X = Submodule.span (ZMod 2) {v} ∨ LowRankWitness ρ v X)
    (hbender : ¬ ClassificationModels.IsBenderModel C)
    (hsp : ∀ n, 2 ≤ n → ¬ ClassicalGroup.IsPSp C 2 (2^n))
    (hg2 : ∀ n, 2 ≤ n → ¬ ClassificationModels.IsG2At C (2^n)) :
    (IsSimpleGroup C ∧ (SmallCarrier C ∨
      (fixedSpace ρ X = Submodule.span (ZMod 2) {v} ∧ ¬ LowRankWitness ρ v X ∧
        Nonempty (C ≃* Sporadic.Mathieu.M22)))) ∨
    (IsM22Cover C ∧ finrank (ZMod 2) W = 12) := by
  have hdual := LargeWhole.selfDual (L := C) h
  have not_five (e : C ≃* alternatingGroup (Fin 5)) : False := by
    let k := GaloisField 2 2
    have hc : Nat.card k = 4 := by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      norm_num
    obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
    exact hbender (.linear 2 (by decide)
      ⟨k,inferInstance,inferInstance,hc,⟨e.trans f.symm⟩⟩)
  have not_linear (n : ℕ) (hn : 0 < n) (hm : ClassicalGroup.IsPSL C 3 (2^n)) : False :=
    WholeLinearThree.not_binary_model h9 hdual hn (Or.inl hm)
  rcases h9.single_component_models with ⟨hi,models⟩ | ⟨hz,models⟩
  · let := hi
    let : IsQuasisimple C := h9.component.2
    let : IsIrreducible (ρ.comp C.subtype) := h9.irreducible
    have hcenter : center C = ⊥ := by
      rcases (inferInstance : (center C).Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · exact (Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp ht)).elim
    let q : C ⧸ center C ≃* C :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    left
    refine ⟨hi,?_⟩
    cases models with
    | alternating n hn he =>
      have hn' : n=5 ∨ n=6 ∨ n=7 ∨ n=8 := by omega
      rcases hn' with rfl | rfl | rfl | rfl
      · exact (not_five he.some).elim
      · exact (WholeAlternating.not_six h9 hd he.some).elim
      · exact Or.inl (.seven he)
      · exact Or.inl (.eight he)
    | linear_odd p a hp ho ha _ hm =>
      rcases Section07.OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
        (ρ.comp C.subtype) (h9.faithful.comp C.subtype_injective) hp ho
        (by rcases ha with rfl | rfl <;> decide) hm h9.single_component_degree_bound with hb | hl | he
      · exact (hbender (.linear 2 (by decide) hb)).elim
      · exact (not_linear 1 (by decide) (by simpa using hl)).elim
      · exact (WholeAlternating.not_six h9 hd (he.some.trans
          (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))).elim
    | three_odd p hp ho u hm =>
      have hmodel : Section07.OddCharacteristic.IsLinearUnitaryThree C p := by
        cases u with
        | false => exact .inl hm
        | true => exact .inr (.inr (.inl hm))
      obtain ⟨he,_⟩ := Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
        (ρ.comp C.subtype) (h9.faithful.comp C.subtype_injective) hp ho hmodel
        h9.single_component_degree_bound
      exact .inl (.binary_g2 he)
    | rank_one hm => exact (hbender hm).elim
    | rank_two hm =>
      cases hm with
      | linear n hn hm => exact (not_linear n hn hm).elim
      | symplectic n hn hm => exact (hsp n hn hm).elim
      | g2 n hn hm => exact (hg2 n hn hm).elim
      | symplectic_derived he =>
        exact (WholeAlternating.not_six h9 hd (he.some.trans
          Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).elim
      | g2_derived he => exact .inl (.binary_g2 he)
      | triality n hn hm =>
        exact (TwistedExclusions.not_triality_positive_exponent h9 hn hm).elim
      | ree n hn hm =>
        obtain ⟨a,he⟩ := hm
        exact (TwistedExclusions.not_ree_of_local_block h9 hn a he.some).elim
      | tits he => exact (TwistedExclusions.not_tits_of_source_component h9 he.some).elim
    | binary_linear n hn hm =>
      obtain ⟨k,_,_,hcard,⟨e⟩⟩ := hm
      let : Fintype k := Fintype.ofFinite k
      let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hcard)
      rcases hn with rfl | rfl
      · exact .inl (.eight ⟨(e.trans (Atlas.fieldEquivPSL 4 a)).trans
          Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm⟩)
      · exact (h9.not_even_models (AlternatingForm.even_finrank B h.alternating h.nondegenerate)
          hdual (.inr (.inr ⟨e.trans (Atlas.fieldEquivPSL 5 a)⟩))).elim
    | janko_one he => exact (h9.not_j1_central_quotient (q.trans he.some)).elim
    | sporadic name hne he =>
      cases name with
      | m11 => exact (h9.not_m11_central_quotient (q.trans he.some)).elim
      | m12 =>
        have hno : ¬ LowRankWitness ρ v X := fun hw => WholeSporadic.not_mathieu_twelve h h9 hw he.some
        exact (not_mathieu_fixed_line h h9 (halt.resolve_right hno) he.some).elim
      | m22 =>
        have hno : ¬ LowRankWitness ρ v X := fun hw => WholeSporadic.not_mathieu_twenty_two h h9 hw he.some
        exact .inr ⟨halt.resolve_right hno,hno,he⟩
      | j2 => exact (WholeSporadic.not_janko_two h h9 hS he.some).elim
      | m23 => exact (h9.not_m23 he.some).elim
      | m24 => exact (h9.not_m24_of_even_degree
          (AlternatingForm.even_finrank B h.alternating h.nondegenerate) he.some).elim
      | j3 => exact (hne rfl).elim
      | j4 => exact (h9.not_janko_four he.some).elim
      | hs => exact (h9.not_higman_sims he.some).elim
      | he => exact (h9.not_held he.some).elim
      | ru => exact (h9.not_rudvalis he.some).elim
  · have hc : Nat.card (center C) = 3 := (Nat.card_congr hz.some.toEquiv).trans (by simp)
    cases models with
    | classical u q hq hm => exact (LargeWhole.not_single_classical_cover h h9 hc u q hq hm).elim
    | alternating_six hm => exact (LargeWhole.not_single_triple_alternating_six h h9 hm).elim
    | alternating_seven hm => exact (h9.not_triple_alternating_seven hm.2.2.some hc).elim
    | mathieu hm => exact .inr ⟨hm,triple_degree h9 hm⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SingleComponent

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A normal component acting irreducibly on the original large quotient is
A₇, A₈, G₂(2)′, a fixed-line M₂₂, or the actual triple-M₂₂ cover in
degree twelve. All models are attached to the literal component; no carrier
or fixed-point recognition premise is added to the original hypotheses. -/
theorem source_large_single_component_reduction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) :
    (IsSimpleGroup C ∧ (ChapterG.Section11.LargeWhole.SmallCarrier C ∨
      (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
        Nonempty (C ≃* Sporadic.Mathieu.M22)))) ∨
    (Chapter1.Section02.LocalModels.IsM22Cover C ∧ finrank (ZMod 2) (Additive F.Uhat) = 12) := by
  obtain ⟨_,_,B,v,hyp,hline,hfix⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v
      (F.terminalDot (F.X g)) :=
    ⟨_,hfix,source_terminal_actor_normal_in_sylow d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
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
  have halt : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} ∨
      ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
    rcases source_terminal_fixed_point_alternative d earlier hq chosen structural alternatives
        F hne g hgP hgH v hline with hf | ⟨a,_,hr,hv⟩
    · exact .inl hf
    · exact .inr ⟨a,a.property,hr,hv⟩
  have hb := source_large_no_bender_component d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH C hC hm hirr
  have hs := fun n hn => source_no_nonbinary_symplectic_component d earlier hq chosen structural
    alternatives F hne g hgP hgH C hC hm hirr (n := n) hn
  have hg := fun n hn => source_no_nonbinary_g2_component d earlier hq chosen structural
    alternatives F hne g hgP hgH C hC hm hirr (n := n) hn
  rcases SingleComponent.remaining hyp h9 hS hd halt hb hs hg with
    ⟨hi,hsmall | ⟨hf,_,hmodel⟩⟩ | hc
  · exact .inl ⟨hi,.inl hsmall⟩
  · exact .inl ⟨hi,.inr ⟨hf.trans hline,hmodel⟩⟩
  · exact .inr hc
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
