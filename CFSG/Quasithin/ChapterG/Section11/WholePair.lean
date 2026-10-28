module
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.SharpDegree
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction
public import Theory.LinearAlgebra.AlternatingFinrank

/-!
# Two-dimensional tensor factors in the whole-component branch

The actual common-field construction, the full known-simple A.1.34 list and
its automorphism ranks force tensor factor dimension at most three. If it
were three, even whole-space dimension forces component rank at least four.
The binary SL2 Schur-degree alternatives and the Suzuki degree lower bound
then contradict the tensor degree. No small-module classification callback
is used. `StrictWholePair` applies this to the original strict quotient.

Source: Aschbacher--Smith G.9.3, G.11.7 and 6.2.18--19,
printed pp.354--356,366--368,690--691.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section11.WholePair
open Section09 Section09.TwoComponents
open Section09.TwoComponents.FactorReduction.ModelRestrictions
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {X L H : Subgroup G} {m : ℕ}

open scoped MatrixGroups MonoidAlgebra

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem factor_faithful {L₂ : Subgroup G} (T : TensorData ρ L L₂) :
    Function.Injective (Representation.restrictScalars T.left :
      Representation (ZMod 2) L T.I) := by
  intro a b hab
  apply T.left_faithful
  ext x
  exact congrArg (fun f : Module.End (ZMod 2) T.I => f x) hab

private theorem not_factor_three {L₂ : Subgroup G}
    (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ X L H m)
    (T : TensorData ρ L L₂) (hm : m≤2*primeRank 2 L)
    (hmodels : 4≤primeRank 2 L → FactorReduction.LargeRankModel L)
    (heven : Even (finrank (ZMod 2) V)) (hk : T.k=3) : False := by
  have hd := h.degree_le
  have hdeg := T.degree_eq
  have hfac := T.factor_degree_eq
  have hn := T.n_pos
  rw [hk] at hdeg hfac
  norm_num at hdeg hfac
  have hsmall : finrank (ZMod 2) T.I ≤ 2*(primeRank 2 L+1) := by omega
  have hr : 4≤primeRank 2 L := by
    obtain ⟨d,he⟩ := heven
    omega
  let τ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  have hf : Function.Injective τ := factor_faithful T
  rcases hmodels hr with ⟨F,_,_,_,hc,⟨e⟩⟩ | ⟨s,hs,⟨e⟩⟩
  · let σ : Representation (ZMod 2) SL(2,F) T.I := τ.comp e.symm.toMonoidHom
    let : IsIrreducible σ :=
      (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr T.left_irreducible
    have hnt : ∃ g,σ g≠1 := by
      let : IsQuasisimple L := h.component.2
      let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
      let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
      obtain ⟨l,hl⟩ := exists_ne (1 : L)
      refine ⟨e l,fun he => hl (hf ?_)⟩
      simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply,map_one] using he
    have hsch := T.left_schur_degree_comp e.symm
    change finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] σ.asModule)=T.n at hsch
    rcases DefiningCharacteristic.binary_small_degree_schur_alternatives σ hnt
      (primeRank 2 L) (by omega) hc hsmall with hh | hh | hh
    all_goals rw [hsch] at hh; omega
  · let σ := τ.comp e.symm.toMonoidHom
    have hlo := Representation.Suzuki.finrank_ge (by omega : 1≤s) σ (hf.comp e.symm.injective)
    have hrank : primeRank 2 L=2*s+1 :=
      (primeRank_equiv 2 e).trans (BenderSuzuki.MatrixGroups.suzuki_two_rank s hs)
    omega

/-- The actual component pair has a common-field tensor realization with
factor dimension two. All source rank and large-factor premises
are discharged for the original full known-simple cover. -/
theorem component_pair_data
    (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ X L H m)
    (hne : H≠L) (heven : Even (finrank (ZMod 2) V)) :
    ∃ L₂ : Subgroup G, IsComponent G L₂ ∧ H=L⊔L₂ ∧ L≠L₂ ∧
      Nonempty (L ≃* L₂) ∧ center L=⊥ ∧ m≤2*primeRank 2 L ∧
      ∃ T : TensorData ρ L L₂, T.k=2 := by
  rcases h.components with he | ⟨L₂,hL₂,hH,hq⟩
  · exact (hne he).elim
  have hne₂ : L≠L₂ := by
    intro he
    exact hne (by simpa only [←he,sup_idem] using hH)
  obtain ⟨T⟩ := CommonField.tensorConstruction ρ L L₂ h.faithful h.component hL₂ hne₂
    (hH ▸ h.irreducible) hq
  have hb : BinaryAutomorphismRankTheorem := fun _ _ _ _ _ hn hc =>
    Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hc
  obtain ⟨hz,hpos,hfactor,hmodels⟩ := component_model_restrictions
    semisimpleSectionRank_knownSimple sourceA134Three_knownSimple hb
    h hL₂ hH hne₂ hq T
  have hsz : FactorReduction.SuzukiBinaryDegreeTheorem.{v} := by
    intro s hs W _ _ _ σ hi hf
    exact Representation.Suzuki.finrank_ge (by omega) σ hf
  obtain ⟨hm,hk⟩ := rank_and_factor_dimension_of_restrictions
    FactorReduction.square_automorphism_rank_theorem hsz h hL₂ hH hne₂ hq T
    hz hpos hfactor hmodels
  have he : Nonempty (L ≃* L₂) := by
    rcases hq with ⟨e,_,_⟩ | ⟨e,_,_⟩ <;> exact ⟨e⟩
  have hk2 : T.k=2 := hk.resolve_right (not_factor_three h T hm hmodels heven)
  exact ⟨L₂,hL₂,hH,hne₂,he,hz,hm,T,hk2⟩
end CFSG.Quasithin.ChapterG.Section11.WholePair
