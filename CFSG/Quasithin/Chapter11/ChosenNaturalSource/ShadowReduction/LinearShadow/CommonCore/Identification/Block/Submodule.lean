module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Radical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Line

public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# The original omega-center span and flag line

A point of Z intersect P centralizes the original Sylow group. The literal
pair-action kernel first places it in V, and the fixed-vector description
of the SL₃ Sylow flag places it in V₁. Conversely the actual odd Hall
scalars span V₁ from its omega-center points. Hence the original subgroup
V_K = ⟨(Z intersect P)^H⟩ is exactly ⟨V₁^H⟩.

Since H = KT and T preserves V₁ and K, this is also ⟨V₁^K⟩. These
identities feed the natural-action and core-intersection application in
`Block.NaturalSubmodule`. Only the permitted preceding action and Cartan conclusions
remain explicit; the counterexample application there supplies the pair
identifications. Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

theorem seed_sylow_fixed_le_line
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a)) :
    V ⊓ centralizer (T : Set G) ≤ f.Vi 0 := by
  let c : Coordinates D S.field := .sl3 a
  have he : f.Vi 0 = (SL3.flag D S a).Vi 0 := congrArg c.preimage
    (SL3.flag_unique D S a 0 (f.space 0) (f.dimension 0) (f.invariant 0))
  rw [he]
  rintro x ⟨hx,hc⟩
  let v : V := ⟨x,hx⟩
  apply (c.mem_preimage _ v).mpr
  apply (SL3.Model.pointFor_fixed _ _ (SL3.alignment_sylow D S a) _).mpr
  intro p hp
  rw [SL3.innerSylow_eq] at hp
  obtain ⟨l,hl,rfl⟩ := hp
  have hconj : V.normalizerMonoidHom (inclusion D.normalizes l) v = v := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hc l hl)
  exact (c.projection_component_conjugation l v).symm.trans
    (congrArg (fun w => (c.projection w).toAdd) hconj)

theorem omega_pair_le_line
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a))
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h) :
    omegaCenter T ⊓ pairCore V H h ≤ f.Vi 0 := by
  apply le_trans _ (seed_sylow_fixed_le_line a f)
  refine le_inf ?_ (inf_le_left.trans (omegaCenter_le_sylow_centralizer T))
  rintro x ⟨hz,hp⟩
  exact ((pairCore_fixed_eq_axis s hf hh hk).le
    ⟨hp,centralizer_le D.le_sylow (omegaCenter_le_sylow_centralizer T hz)⟩).1

private theorem line_le_normalized_of_orbit
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (A W : Subgroup G) (hA : A ≤ normalizer (W : Set G))
    (hZ : f.Vi 0 ⊓ omegaCenter T ≤ W)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hspan : (f.space 0).toAddSubgroup ≤ AddSubgroup.closure
      {w : c.Space | ∃ (z : V) (d : L), (z : G) ∈ f.Vi 0 ⊓ omegaCenter T ∧
        (d : G) ∈ A ∧ w = c.modelAction (c.quotientMap d) (c.projection z).toAdd}) :
    f.Vi 0 ≤ W := by
  let Q := (W.subgroupOf V).map c.projection
  have hi : Function.Injective c.projection := by
    apply c.projection.ker_eq_bot_iff.mp
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hfixed.le ⟨v.property,(c.projection_eq_one_iff v).mp hv⟩
  have hs : AddSubgroup.closure
      {w : c.Space | ∃ (z : V) (d : L), (z : G) ∈ f.Vi 0 ⊓ omegaCenter T ∧
        (d : G) ∈ A ∧ w = c.modelAction (c.quotientMap d) (c.projection z).toAdd} ≤
      Q.toAddSubgroup := by
    apply (AddSubgroup.closure_le _).mpr
    rintro w ⟨z,d,hz,hd,rfl⟩
    rw [←c.projection_component_conjugation]
    exact mem_map_of_mem c.projection ((hA hd z.val).mp (hZ hz))
  intro v hv
  let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
  have hm : c.projection v' ∈ Q := hs (hspan ((c.mem_preimage _ v').mp hv))
  obtain ⟨u,hu,he⟩ := hm
  have hvW : v' ∈ W.subgroupOf V := hi he ▸ hu
  exact hvW

/-- The literal source V_K, using the original omega center and pair core. -/
@[expose] def pairNaturalSpan (T : Sylow 2 G) (V H : Subgroup G) (h : G) : Subgroup G :=
  conjugateSpanBy (omegaCenter T ⊓ pairCore V H h) H

theorem pairNaturalSpan_eq_line_span
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a)) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h)
    (hB : axis V H = f.Vi 1)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (cK : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X) :
    pairNaturalSpan T V H h = conjugateSpanBy (f.Vi 0) H := by
  apply le_antisymm
  · exact conjugateSpanBy_mono (omega_pair_le_line a f s hh hf hk) le_rfl
  · apply conjugateSpanBy_le _ (le_normalizer_conjugateSpanBy _ _)
    have hline : f.Vi 0 ≤ pairCore V H h :=
      (f.Vi_mono (show (0 : Fin 3) ≤ 1 by decide)).trans (hB.symm.le.trans le_sup_left)
    apply line_le_normalized_of_orbit (.sl3 a) f (oddCartanPart A) _
      (((oddCartanPart_le A).trans (hA.trans inf_le_left)).trans
        (le_normalizer_conjugateSpanBy _ _))
      ((le_inf inf_le_right (inf_le_left.trans hline)).trans (le_conjugateSpanBy _ _)) hfixed
    exact (source_scalar_and_orbit_of_fixed_spaces (.sl3 a) f hu s cK A X hA hHall
      hX hAX hfixed hf).2

theorem line_span_eq_residual_span
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (s : Hypothesis1131At D S U₁ H) :
    conjugateSpanBy (f.Vi 0) H = conjugateSpanBy (f.Vi 0) (outsideResidual H) := by
  apply le_antisymm
  · apply conjugateSpanBy_le (le_conjugateSpanBy _ _)
    nth_rw 1 [←outsideResidual_sup_sylow T H s.outside.1.1.2]
    exact sup_le (le_normalizer_conjugateSpanBy _ _)
      (normalizes_conjugateSpanBy _ _ _ (f.invariant 0)
        (s.outside.1.1.2.trans (outsideResidual_normalized H)))
  · exact conjugateSpanBy_mono le_rfl (outsideResidual_le H)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
