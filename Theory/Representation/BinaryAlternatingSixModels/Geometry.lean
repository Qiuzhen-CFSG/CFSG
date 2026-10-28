module

public import Theory.Representation.BinaryAlternatingSixModels
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The two marked binary natural modules

On the duad action, the point parabolic fixes the base nonzero vector and has
no invariant two-dimensional subspace: any other nonzero vector has a
stabilizer orbit of length six or eight, too large for a binary plane. The
syntheme parabolic preserves its actual isotropic plane. Pulling back along
the aligned exceptional automorphism reverses these statements, proving that
the two natural representations are inequivalent.

A line here is a projective line, namely an invariant two-dimensional vector
subspace. It need not be fixed pointwise. The final exclusion removes the
trivial and both natural alternatives from a four-model catalogue, leaving an
actual equivariant isomorphism to the tensor action. Exhaustion and Steinberg
identification remain separate inputs to the source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.1(2) and
G.5.2, printed pp.342–343 (PDF pp.353–354).
-/

public section
namespace BinaryAlternatingSix
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule

theorem first_fixes_point (g : A6) (hg : g ∈ a6DuadStabilizer) :
    alternatingNaturalAction g (polarVector 0).val = (polarVector 0).val := by
  have he : g • (0 : Duad) = 0 := by
    rw [← a6_duad_stabilizer_zero] at hg
    exact hg
  change polarAction g.val (polarVector 0).val = _
  rw [polarAction_vector]
  exact congrArg (fun d => (polarVector d).val) he

theorem first_preserves_line (g : A6) (hg : g ∈ a6SynthemeStabilizer)
    (v : NaturalModule) (hv : v ∈ polarLine 0) :
    alternatingNaturalAction g v ∈ polarLine 0 := by
  have he : synthemeAct g.val 0 = 0 := by
    have hh : g.val ∈ synthemeStabilizer := hg
    rw [← syntheme_stabilizer_zero] at hh
    exact hh
  have hm := Submodule.mem_map_of_mem (f := polarLinearMap g.val) hv
  rw [← polarLine_act, he] at hm
  exact hm

private theorem polarVector_val_injective :
    Function.Injective (fun d => (polarVector d).val) := by
  intro d e h
  exact polarVector_injective (Subtype.ext h)

private theorem duad_vector_mem (W : Submodule (ZMod 2) NaturalModule)
    (hW : ∀ g ∈ a6DuadStabilizer, ∀ v ∈ W, alternatingNaturalAction g v ∈ W)
    (d e : Duad) (hd : (polarVector d).val ∈ W)
    (g : A6) (hg : g • (0 : Duad) = 0) (hge : g • d = e) :
    (polarVector e).val ∈ W := by
  have hg' : g ∈ a6DuadStabilizer := by
    rw [← a6_duad_stabilizer_zero]
    exact hg
  have hm := hW g hg' (polarVector d).val hd
  change polarAction g.val (polarVector d).val ∈ W at hm
  rw [polarAction_vector] at hm
  exact hge ▸ hm

/-- Every subspace of dimension at most two invariant under the marked point
parabolic lies in its fixed point. In particular, it has no invariant plane. -/
theorem first_small_invariant_subspace
    (W : Submodule (ZMod 2) NaturalModule)
    (hW : ∀ g ∈ a6DuadStabilizer, ∀ v ∈ W, alternatingNaturalAction g v ∈ W)
    (hdim : Module.finrank (ZMod 2) W ≤ 2) :
    W ≤ Submodule.span (ZMod 2) {(polarVector 0).val} := by
  classical
  have hc : Nat.card W ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hdim
  intro v hv
  by_cases hz : v = 0
  · simpa only [hz] using (Submodule.zero_mem (Submodule.span (ZMod 2) {(polarVector 0).val}))
  obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨v, hz⟩
  have he : (polarVector d).val = v := congrArg Subtype.val hd
  have hdW : (polarVector d).val ∈ W := he.symm ▸ hv
  by_cases hd0 : d = 0
  · rw [← he, hd0]
    exact Submodule.subset_span (Set.mem_singleton _)
  exfalso
  by_cases hcol : duadCollinear 0 d
  · have hm (e : {e : Duad // duadCollinear 0 e}) : (polarVector e.val).val ∈ W := by
      obtain ⟨g, hg, hge⟩ := a6_duad_collinear_transporter 0 d e.val hcol e.property
      exact duad_vector_mem W hW d e.val hdW g hg hge
    let f : {e : Duad // duadCollinear 0 e} → W := fun e => ⟨_, hm e⟩
    have hi : Function.Injective f := by
      intro e f h
      exact Subtype.ext (polarVector_val_injective (congrArg (fun w : W => w.val) h))
    have hb := Nat.card_le_card_of_injective f hi
    have hs : Nat.card {e : Duad // duadCollinear 0 e} = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact duad_collinear_six 0
    omega
  · have hm (e : {e : Duad // e ≠ 0 ∧ ¬duadCollinear 0 e}) :
        (polarVector e.val).val ∈ W := by
      obtain ⟨g, hg, hge⟩ := a6_duad_noncollinear_transporter 0 d e.val
        ⟨hd0, hcol⟩ e.property
      exact duad_vector_mem W hW d e.val hdW g hg hge
    let f : {e : Duad // e ≠ 0 ∧ ¬duadCollinear 0 e} → W := fun e => ⟨_, hm e⟩
    have hi : Function.Injective f := by
      intro e f h
      exact Subtype.ext (polarVector_val_injective (congrArg (fun w : W => w.val) h))
    have hb := Nat.card_le_card_of_injective f hi
    have hs : Nat.card {e : Duad // e ≠ 0 ∧ ¬duadCollinear 0 e} = 8 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact duad_noncollinear_eight 0
    omega

theorem first_no_invariant_line
    (W : Submodule (ZMod 2) NaturalModule)
    (hW : ∀ g ∈ a6DuadStabilizer, ∀ v ∈ W, alternatingNaturalAction g v ∈ W) :
    Module.finrank (ZMod 2) W ≠ 2 := by
  intro hd
  have hle := Submodule.finrank_mono (first_small_invariant_subspace W hW hd.le)
  rw [finrank_span_singleton (polarVector 0).property, hd] at hle
  omega


/-- A projective line is a two-dimensional invariant subspace; its vectors
need not be fixed pointwise. -/
@[expose] def HasInvariantLine {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (P : Subgroup H) : Prop :=
  ∃ W : Submodule (ZMod 2) V, Module.finrank (ZMod 2) W = 2 ∧
    ∀ g ∈ P, ∀ v ∈ W, ρ g v ∈ W

theorem hasInvariantLine_of_equiv {H V W : Type*} [Group H]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H V} {σ : Representation (ZMod 2) H W}
    (e : ρ.Equiv σ) (P : Subgroup H) (h : HasInvariantLine ρ P) :
    HasInvariantLine σ P := by
  obtain ⟨U, hd, hU⟩ := h
  refine ⟨U.map e.toLinearMap, ?_, ?_⟩
  · exact (e.toLinearEquiv.finrank_map_eq U).trans hd
  · rintro g hg _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hU g hg v hv, Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v⟩

theorem first_has_line : HasInvariantLine firstAlternating a6SynthemeStabilizer :=
  ⟨polarLine 0, polarLine_finrank 0, first_preserves_line⟩

theorem first_has_no_line : ¬ HasInvariantLine firstAlternating a6DuadStabilizer := by
  rintro ⟨W, hd, hW⟩
  exact first_no_invariant_line W hW hd

theorem second_fixes_point (g : A6) (hg : g ∈ a6SynthemeStabilizer) :
    secondAlternating g (polarVector 0).val = (polarVector 0).val :=
  first_fixes_point (alternatingDiagramAut g) ((alternatingDiagramAut_mem_duad g).mpr hg)

theorem second_has_line : HasInvariantLine secondAlternating a6DuadStabilizer := by
  refine ⟨polarLine 0, polarLine_finrank 0, ?_⟩
  intro g hg v hv
  exact first_preserves_line (alternatingDiagramAut g)
    ((alternatingDiagramAut_mem_syntheme g).mpr hg) v hv

theorem second_has_no_line : ¬ HasInvariantLine secondAlternating a6SynthemeStabilizer := by
  rintro ⟨W, hd, hW⟩
  apply first_no_invariant_line W ?_ hd
  intro g hg v hv
  have hh : alternatingDiagramAut.symm g ∈ a6SynthemeStabilizer := by
    apply (alternatingDiagramAut_mem_duad _).mp
    simpa only [MulEquiv.apply_symm_apply] using hg
  have hm := hW (alternatingDiagramAut.symm g) hh v hv
  simpa only [secondAlternating_apply, MulEquiv.apply_symm_apply] using hm

/-- The two four-dimensional actions are inequivalent as representations of
this marked A₆, although an exceptional automorphism exchanges them. -/
theorem natural_inequivalent : IsEmpty (Representation.Equiv firstAlternating secondAlternating) := by
  refine ⟨fun e => ?_⟩
  exact first_has_no_line (hasInvariantLine_of_equiv e.symm _ second_has_line)

/-- The automorphism is retained in the comparison used in G.9. -/
theorem natural_comparison {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A6 V)
    (h : Nonempty (ρ.Equiv firstAlternating) ∨ Nonempty (ρ.Equiv secondAlternating)) :
    ∃ α : MulAut A6, ∃ e : V ≃ₗ[ZMod 2] NaturalModule,
      ∀ g v, e (ρ g v) = firstAlternating (α g) (e v) := by
  rcases h with h | h
  all_goals obtain ⟨e⟩ := h
  · exact ⟨MulEquiv.refl A6, e.toLinearEquiv, Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap⟩
  · exact ⟨alternatingDiagramAut, e.toLinearEquiv, Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap⟩

open Representation

private theorem no_line_one_dimensional {H V : Type*} [Group H]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (P : Subgroup H)
    (hd : Module.finrank (ZMod 2) V = 1) : ¬ HasInvariantLine ρ P := by
  rintro ⟨W, hW, _⟩
  have := W.finrank_le
  omega

private def restrictEquiv {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) S6 V} {σ : Representation (ZMod 2) S6 W}
    (e : ρ.Equiv σ) : Representation.Equiv (ρ.comp A6.subtype) (σ.comp A6.subtype) :=
  .mk e.toLinearEquiv (fun g => e.isIntertwining' g.val)

/-- The three small model branches in G.5.2 are excluded using actual
invariant projective lines. Exhaustion by the four models is a separate input. -/
theorem tensor_of_invariant_lines_of_model {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) (hmodel : IsSymmetricModel ρ)
    (h₁ : HasInvariantLine (ρ.comp A6.subtype) a6DuadStabilizer)
    (h₂ : HasInvariantLine (ρ.comp A6.subtype) a6SynthemeStabilizer) :
    Nonempty (ρ.Equiv tensorAction) := by
  rcases hmodel with h | h | h | h
  · obtain ⟨e⟩ := h
    exact (no_line_one_dimensional trivialAlternating a6DuadStabilizer (by simp)
      (hasInvariantLine_of_equiv (restrictEquiv e) _ h₁)).elim
  · obtain ⟨e⟩ := h
    exact (first_has_no_line (hasInvariantLine_of_equiv (restrictEquiv e) _ h₁)).elim
  · obtain ⟨e⟩ := h
    exact (second_has_no_line (hasInvariantLine_of_equiv (restrictEquiv e) _ h₂)).elim
  · exact h

end BinaryAlternatingSix
