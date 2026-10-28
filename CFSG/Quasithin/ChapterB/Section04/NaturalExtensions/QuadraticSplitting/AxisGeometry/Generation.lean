module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation.Contracts
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation.Cubes
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation.LeviTransports
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation.RootLines
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Propagation
/-!
# Full Levi generation of the marked axis group

The proof reduces the matrix input to literal pair conjugations. Outside
F₄, an independent pair in E supplies conjugates through each nonidentity
element of Q; the full Levi's scalar cubes additively generate the axis
plane. In binary higher dimension every independent target pair is reached.
For F₄, the actual binary planes outside root lines belong to AvailableFour
and generate Q. The same marking is used throughout.

The final `axisGeneration` theorem discharges both matrix inputs using the
constructed full Levi transports and the root-line comparison through the
original marking. Its `axis_quadratic_of_source` application proves that Q
is quadratic on the original action from the source hypotheses and the
quadratic four-group E. Quotient coordinates are supplied explicitly;
their construction and the subsequent splitting remain separate results.

Source: Aschbacher–Smith B.4.9(1), printed pp.92–93, combined manuscript
of 1 March 2004.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ}
namespace QuotientCoordinates
variable (m : QuotientCoordinates d) (j : Fin n)

theorem exists_outside_parameter_line (hn : 3 ≤ n)
    (e : coordinateHyperplane F n j) (he : e ≠ 0) :
    ∃ x : coordinateHyperplane F n j, x ∉ Submodule.span F.Carrier {e} := by
  have hlt : Submodule.span F.Carrier {e} < ⊤ := by
    apply Submodule.lt_top_of_finrank_lt_finrank
    rw [finrank_span_singleton he, coordinateHyperplane_finrank]
    omega
  obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt hlt
  exact ⟨x, hx⟩

theorem axisPair_not_inRootGroup (hr : m.RootLineDescription j)
    (e x : coordinateHyperplane F n j) (h : LinearIndependent F.Carrier ![e,x]) :
    ¬ InRootGroup d (m.axisPair j e x) := by
  intro hroot
  obtain ⟨w, _, hw⟩ := (hr _ (m.axisPair_le_Q j e x)).mp hroot
  obtain ⟨a, ha⟩ := hw _ (m.axisPair_left j e x)
  obtain ⟨b, hb⟩ := hw _ (m.axisPair_right j e x)
  have hae : a • w = e := m.axisShear_injective j ha
  have hbx : b • w = x := m.axisShear_injective j hb
  have he : e ≠ 0 := h.ne_zero 0
  have ha0 : a ≠ 0 := by
    intro hh
    rw [hh, zero_smul] at hae
    exact he hae.symm
  apply (LinearIndependent.pair_iff' he).mp h (b/a)
  rw [← hae, smul_smul, div_mul_cancel₀ _ ha0, hbx]

private theorem card_le_field_of_parameter_line (E : Subgroup G)
    (u : coordinateHyperplane F n j)
    (hline : ∀ a ∈ E, ∃ c : F.Carrier, m.axisShear j (c • u) = a) :
    Nat.card E ≤ Nat.card F.Carrier := by
  let f : F.Carrier → G := fun c => m.axisShear j (c • u)
  let i : E → Set.range f := fun a => ⟨a, hline a a.property⟩
  have hi : Function.Injective i := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : Set.range f => (z : G)) h
  exact (Nat.card_le_card_of_injective i hi).trans (Nat.card_le_card_of_surjective (Set.rangeFactorization f) Set.rangeFactorization_surjective)

/-- A source four-group contains two defining-field independent shear parameters.
The binary case uses its order four; degree three uses the actual root exclusion. -/
theorem exists_independent_axis_parameters (hr : m.RootLineDescription j)
    (hf : SourceFamily F n) (E : Subgroup G) (hE : IsAxisFour d E)
    (hEQ : E ≤ m.Q j) (hroot : n = 3 → ¬ InRootGroup d E) :
    ∃ u v : coordinateHyperplane F n j,
      m.axisShear j u ∈ E ∧ m.axisShear j v ∈ E ∧
      LinearIndependent F.Carrier ![u,v] := by
  classical
  have hbot : E ≠ ⊥ := by
    intro hh
    have hc := hE.2.1
    rw [hh, Subgroup.card_bot] at hc
    omega
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨u, hu⟩ := m.exists_axisShear j ⟨a, hEQ ha⟩
  change m.axisShear j u = a at hu
  have hu0 : u ≠ 0 := by
    intro hh
    apply ha1
    apply Subtype.ext
    change a = 1
    rw [← hu, hh, m.axisShear_zero]
  have huE : m.axisShear j u ∈ E := hu.symm ▸ ha
  suffices ∃ v : coordinateHyperplane F n j,
      m.axisShear j v ∈ E ∧ LinearIndependent F.Carrier ![u,v] by
    obtain ⟨v, hv, huv⟩ := this
    exact ⟨u,v,huE,hv,huv⟩
  by_contra! h
  have hline : ∀ b ∈ E, ∃ c : F.Carrier, m.axisShear j (c • u) = b := by
    intro b hb
    obtain ⟨v, hv⟩ := m.exists_axisShear j ⟨b, hEQ hb⟩
    change m.axisShear j v = b at hv
    have hnot := h v (hv.symm ▸ hb)
    rw [LinearIndependent.pair_iff' hu0] at hnot
    push Not at hnot
    obtain ⟨c, hc⟩ := hnot
    exact ⟨c, (congrArg (m.axisShear j) hc).trans hv⟩
  rcases hf with hn | ⟨hF, _⟩
  · exact hroot hn ((hr E hEQ).mpr ⟨u, hu0, hline⟩)
  · have hc := m.card_le_field_of_parameter_line j E u hline
    rw [hE.2.1, F.card_eq, hF] at hc
    norm_num at hc

private theorem independent_of_outside_line (e x : coordinateHyperplane F n j)
    (he : e ≠ 0) (hx : x ∉ Submodule.span F.Carrier {e}) :
    LinearIndependent F.Carrier ![e,x] := by
  rw [LinearIndependent.pair_iff' he]
  intro a ha
  exact hx (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)

/-- The full group generation argument, with the two precise matrix obligations
explicit. Cubic scalars and the exceptional F₄ family are discharged here. -/
theorem axisGeneration_of_levi_and_roots
    (ht : m.LeviPairTransports j) (hr : m.RootLineDescription j)
    (hf : SourceFamily F n) (E : Subgroup G) (hE : IsAxisFour d E)
    (hEQ : E ≤ m.Q j) (hroot : n = 3 → ¬ InRootGroup d E) :
    AxisGeneration d E (m.Q j) := by
  have hn : 3 ≤ n := by rcases hf with h | ⟨_, h⟩ <;> omega
  intro g hg hg1
  obtain ⟨e, he⟩ := m.exists_axisShear j ⟨g, hg⟩
  change m.axisShear j e = g at he
  have he0 : e ≠ 0 := by
    intro hh
    apply hg1
    rw [← he, hh, m.axisShear_zero]
  let H : Subgroup G := ⨆ (A : Subgroup G) (_ : g ∈ A ∧ AvailableFour d E A), A
  let S := m.axisParameters j H
  have hconj (u v z : coordinateHyperplane F n j)
      (hu : m.axisShear j u ∈ E) (hv : m.axisShear j v ∈ E)
      (k : G) (hke : k * m.axisShear j u * k⁻¹ = m.axisShear j e)
      (hkz : k * m.axisShear j v * k⁻¹ = m.axisShear j z) : z ∈ S := by
    let A := E.map (MulAut.conj k).toMonoidHom
    have hga : g ∈ A := ⟨m.axisShear j u, hu, hke.trans he⟩
    have hA : A ≤ H := le_iSup_of_le A (le_iSup_of_le ⟨hga, Or.inl ⟨k, rfl⟩⟩ le_rfl)
    exact hA ⟨m.axisShear j v, hv, hkz⟩
  have htop : S = ⊤ := by
    by_cases hF : F.degree = 2
    · obtain ⟨x, hx⟩ := exists_outside_parameter_line j hn e he0
      apply CubeGeneration.eq_top_of_outside_subspace S (Submodule.span F.Carrier {e}) x hx
      intro z hz
      have hiz := independent_of_outside_line j e z he0 hz
      let A := m.axisPair j e z
      have hga : g ∈ A := he ▸ m.axisPair_left j e z
      have hrootA := m.axisPair_not_inRootGroup j hr e z hiz
      have hA := m.availableFour_of_le_Q j (by omega) hF E A
        (m.axisPair_le_Q j e z) (m.axisPair_card j e z hiz) hrootA
      have hle : A ≤ H := le_iSup_of_le A (le_iSup_of_le ⟨hga, hA⟩ le_rfl)
      exact hle (m.axisPair_right j e z)
    · obtain ⟨u, v, hu, hv, huv⟩ :=
        m.exists_independent_axis_parameters j hr hf E hE hEQ hroot
      rcases hf with hn3 | ⟨hF1, _⟩
      · obtain ⟨x, hspan, htrans⟩ := ht.cubic hn3 u v huv e he0
        apply CubeGeneration.eq_top_of_cubic_orbit F hF S e x hspan
        intro a t ht0
        obtain ⟨k, hke, hkz⟩ := htrans a t ht0
        exact hconj u v _ hu hv k hke hkz
      · obtain ⟨x, hx⟩ := exists_outside_parameter_line j hn e he0
        apply CubeGeneration.eq_top_of_outside_subspace S (Submodule.span F.Carrier {e}) x hx
        intro z hz
        obtain ⟨k, hke, hkz⟩ := ht.binary hF1 hn u v huv e z
          (independent_of_outside_line j e z he0 hz)
        exact hconj u v z hu hv k hke hkz
  intro q hq
  obtain ⟨w, hw⟩ := m.exists_axisShear j ⟨q, hq⟩
  change m.axisShear j w = q at hw
  rw [← hw]
  exact (show w ∈ S from htop.symm ▸ AddSubgroup.mem_top w)

/-- Consumer application to the original quadratic action, after the displayed
matrix obligations have been supplied. Both are discharged below. -/
theorem axis_quadratic_of_levi_and_roots
    (ht : m.LeviPairTransports j) (hr : m.RootLineDescription j)
    (h : SourceHypotheses d) (E : Subgroup G) (hE : IsAxisFour d E)
    (hEQ : E ≤ m.Q j) (hroot : n = 3 → ¬ InRootGroup d E)
    (hquad : IsQuadratic ρ E) : IsQuadratic ρ (m.Q j) :=
  axis_quadratic d h E (m.Q j) hquad
    (m.axisGeneration_of_levi_and_roots j ht hr h.family E hE hEQ hroot)

/-- The full marked axis group is generated through every nonidentity element
by the available four-groups of B.4.9(1). This includes both quotient
orientations, every binary dimension at least four, all defining fields in
dimension three, and the exceptional F₄ family. -/
theorem axisGeneration (hf : SourceFamily F n) (E : Subgroup G)
    (hE : IsAxisFour d E) (hEQ : E ≤ m.Q j)
    (hroot : n = 3 → ¬ InRootGroup d E) : AxisGeneration d E (m.Q j) := by
  have hn : 3 ≤ n := by rcases hf with h | ⟨_, h⟩ <;> omega
  exact m.axisGeneration_of_levi_and_roots j
    (m.leviPairTransports j) (m.rootLineDescription j hn) hf E hE hEQ hroot

/-- The generation step of B.4.9(1) makes the actual quotient axis group
quadratic on V. The source's universal F₄ clause supplies quadraticity of
the exceptional available four-groups. No matrix-generation premise remains. -/
theorem axis_quadratic_of_source (h : SourceHypotheses d) (E : Subgroup G)
    (hE : IsAxisFour d E) (hEQ : E ≤ m.Q j)
    (hroot : n = 3 → ¬ InRootGroup d E) (hquad : IsQuadratic ρ E) :
    IsQuadratic ρ (m.Q j) :=
  axis_quadratic d h E (m.Q j) hquad
    (m.axisGeneration j h.family E hE hEQ hroot)

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
