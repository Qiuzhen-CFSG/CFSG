module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Setup
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource

/-!
# Intersections and the local simplex centralizer in the A₇ branch

Fusion control and the weight-two/six centralizer bounds force every
nonidentity element of an escaping intersection V ∩ Vᵍ to have weight four.
For the displayed simplex subgroup U, local TI and coordinate separation
also give C_M(U) = C_M(V), where M = N_G(L). This does not bound C_G(U):
the missing ambient containment is precisely what the false plane-maximality
shortcut in the printed argument fails to prove.

The original chosen module, original normalizers, and actual action marking
are retained throughout. Source: Aschbacher--Smith, 12.2.6 and 12.3.9(1),
printed pp.797,810. `LocalAnalysis` remains an explicit earlier obligation.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable (S : Setup T L V) (D : S.LocalAnalysis)

/-- The normalizer model contains the actual A₇ permutation subgroup. -/
theorem alternating_le_permutation_range :
    alternatingGroup (Fin 7) ≤ D.model.permutation.range := by
  intro a ha
  obtain ⟨l, hl⟩ := S.projection_surjective ⟨a, ha⟩
  refine ⟨⟨l, S.chosen.normalizes l.property⟩, ?_⟩
  rw [D.component_action, hl]

/-- Source 12.3.9(1), conditional on the genuine local analysis 12.3.3--8. -/
theorem intersection_weight_four
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
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
  rcases S.hypothesis.source_chosen_TI structural S.chosen g hgM with hd | hn
  · exact hx1 (mem_bot.mp (hd ▸ hx))
  · exact hg (mem_normalizer_iff_map_conj_eq.mpr hn)

/-- The local simplex centralizer is controlled by the genuine TI theorem.
Only elements outside M remain to be handled by the ambient argument. -/
theorem local_simplex_centralizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    normalizer (L : Set G) ⊓ centralizer (D.model.simplex : Set G) =
      normalizer (L : Set G) ⊓ centralizer (V : Set G) := by
  apply le_antisymm
  · apply le_inf inf_le_left
    have hTI := inf_centralizer_le_normalizer_of_trivial_intersections
      (S.hypothesis.source_chosen_TI structural S.chosen)
      D.model.simplex_ne_bot D.model.simplex_le
    exact (le_inf hTI inf_le_right).trans D.model.normalizer_inf_simplex_centralizer.le
  · exact inf_le_inf_left _ (centralizer_le D.model.simplex_le)

/-- Any escaping point supplied by 12.2.13 must have weight four, once the
weight-two/six centralizers have been controlled. This is the point used
to begin the terminal A₅-component argument on printed p.811. -/
theorem weight_four_escape
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
