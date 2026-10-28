module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Intersections
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt

/-!
# Intersections at the original ambient group and Sylow subgroup

These are the same source arguments as `Intersections`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable (S : Setup T L V) (D : S.LocalAnalysis)

theorem intersection_weight_four_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {g x : G} (hg : g ∉ normalizer (V : Set G))
    (hx : x ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom) (hx1 : x ≠ 1) :
    weight (D.model.coordinates ⟨x, hx.1⟩).toAdd.val = 4 := by
  have hxv : (⟨x, hx.1⟩ : V) ≠ 1 := fun he => hx1 (congrArg Subtype.val he)
  have hword : (D.model.coordinates ⟨x, hx.1⟩).toAdd.val ≠ 0 := by
    intro he
    have he' : D.model.coordinates ⟨x, hx.1⟩ = 1 := Subtype.ext he
    exact hxv (D.model.coordinates.map_eq_one_iff.mp he')
  suffices hn : ¬ (weight (D.model.coordinates ⟨x, hx.1⟩).toAdd.val = 2 ∨
      weight (D.model.coordinates ⟨x, hx.1⟩).toAdd.val = 6) by
    rcases weight_of_mem_evenWords (D.model.coordinates ⟨x, hx.1⟩).toAdd.property
      hword with htwo | hfour | hsix
    · exact (hn (Or.inl htwo)).elim
    · exact hfour
    · exact (hn (Or.inr hsix)).elim
  intro hw
  have hc := D.pointCentralizers ⟨x, hx.1⟩ hxv hw
  obtain ⟨y, hy, he⟩ := hx.2
  have he' : g⁻¹ * x * (g⁻¹)⁻¹ = y := by
    rw [← he]
    change g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y
    group
  have hy1 : y ≠ 1 := by
    intro hy1
    exact hx1 (he.symm.trans (by simp [hy1]))
  obtain ⟨l, hl, hf⟩ := D.controlsFusion x y hx.1 hy hx1 hy1 ⟨g⁻¹, he'⟩
  have hginv := conjugator_mem_of_centralizer_le hc
    ⟨l, L.le_normalizer hl, hf.trans he'.symm⟩
  have hgM : g ∈ normalizer (L : Set G) := by simpa using inv_mem hginv
  rcases S.hypothesis.source_chosen_TI_at structural S.chosen g hgM with hd | hn
  · exact hx1 (mem_bot.mp (hd ▸ hx))
  · exact hg (mem_normalizer_iff_map_conj_eq.mpr hn)

theorem local_simplex_centralizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    normalizer (L : Set G) ⊓ centralizer (D.model.simplex : Set G) =
      normalizer (L : Set G) ⊓ centralizer (V : Set G) := by
  apply le_antisymm
  · apply le_inf inf_le_left
    have hTI := inf_centralizer_le_normalizer_of_trivial_intersections
      (S.hypothesis.source_chosen_TI_at structural S.chosen)
      D.model.simplex_ne_bot D.model.simplex_le
    exact (le_inf hTI inf_le_right).trans D.model.normalizer_inf_simplex_centralizer.le
  · exact inf_le_inf_left _ (centralizer_le D.model.simplex_le)

theorem weight_four_escape_at
    (escape : ∃ x ∈ V, x ≠ 1 ∧
      ¬ centralizer ({x} : Set G) ≤ normalizer (L : Set G)) :
    ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 4 ∧
      ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨x, hx, hx1, hc⟩ := escape
  let v : V := ⟨x, hx⟩
  have hv : v ≠ 1 := fun he => hx1 (congrArg Subtype.val he)
  have hw : (D.model.coordinates v).toAdd.val ≠ 0 := by
    intro he
    exact hv (D.model.coordinates.map_eq_one_iff.mp (Subtype.ext he))
  refine ⟨v, hv, ?_, hc⟩
  rcases weight_of_mem_evenWords (D.model.coordinates v).toAdd.property hw with
    htwo | hfour | hsix
  · exact (hc (D.pointCentralizers v hv (Or.inl htwo))).elim
  · exact hfour
  · exact (hc (D.pointCentralizers v hv (Or.inr hsix))).elim

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

