module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Calculations
public import Theory.SpecificGroups.PSL3Two.Automorphisms

/-!
# Inner and graph coverage on the exact binary linear carrier

The graph automorphism is not inner: two independent point translations
cannot both be conjugated to their line counterparts. Thus the 168 inner
maps and their 168 graph translates are distinct. The checked automorphism
order 336 proves that these maps exhaust all automorphisms.

Source: the diagram-action step of Aschbacher–Smith 13.8.21(1), p.957.
-/

public section
namespace Matrix.PSL3Two.MarkedAutomorphisms

theorem diagram_apply_twice (g : SL) : diagram (diagram g) = g :=
  diagram_involutive g

private theorem involutive_conj_transport {G : Type*} [Group G]
    (δ α : MulAut G) (hi : Function.Involutive δ) (g : G)
    (he : δ * α * δ = MulAut.conj g) : α = MulAut.conj (δ g) := by
  apply MulEquiv.ext
  intro x
  have hh := congrArg δ (MulEquiv.congr_fun he (δ x))
  change α x = δ g * x * (δ g)⁻¹
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at hh
  have hδ (y : G) : δ (δ y) = y := hi y
  simpa only [hδ] using hh

theorem diagram_conj_transport (α : MulAut SL) (g : SL)
    (he : diagram * α * diagram = MulAut.conj g) :
    α = MulAut.conj (diagram g) :=
  involutive_conj_transport diagram α diagram_involutive g he

private theorem involutive_preserves_transport {G : Type*} [Group G]
    (A : Subgroup G) (δ α : MulAut G) (hi : Function.Involutive δ)
    (h : ∀ a ∈ A.comap δ.toMonoidHom, α a ∈ A.comap δ.toMonoidHom) :
    ∀ a ∈ A, (δ * α * δ) a ∈ A := by
  intro a ha
  have hm : δ a ∈ A.comap δ.toMonoidHom := by
    change δ (δ a) ∈ A
    rwa [hi]
  exact h (δ a) hm

theorem line_preserving_transport (α : MulAut SL)
    (h : ∀ a ∈ lineA, α a ∈ lineA) :
    ∀ a ∈ pointA, (diagram * α * diagram) a ∈ pointA :=
  involutive_preserves_transport pointA diagram α diagram_involutive h

theorem involutive_displacement_transport {G : Type*} [Group G]
    (A V : Subgroup G) (δ α : MulAut G) (hi : Function.Involutive δ)
    (h : ∀ a ∈ A.comap δ.toMonoidHom,
      α a * a⁻¹ ∈ V.comap δ.toMonoidHom) :
    ∀ a ∈ A, (δ * α * δ) a * a⁻¹ ∈ V := by
  intro a ha
  have hm : δ a ∈ A.comap δ.toMonoidHom := by
    change δ (δ a) ∈ A
    rwa [hi]
  have hh := h (δ a) hm
  change δ (α (δ a) * (δ a)⁻¹) ∈ V at hh
  have hδ (x : G) : δ (δ x) = x := hi x
  simpa only [MulAut.mul_apply, map_mul, map_inv, hδ] using hh

theorem conj_injective : Function.Injective (MulAut.conj : SL →* MulAut SL) :=
  MulAut.conj_injective_of_center_eq_bot center_eq_bot

theorem diagram_ne_conj (g : SL) : diagram ≠ MulAut.conj g := by
  intro h
  apply graph_not_inner_test g
  constructor
  · have he := MulEquiv.congr_fun h (Bruhat.upper 1)
    exact (mul_inv_eq_iff_eq_mul).mp he.symm
  · have he := MulEquiv.congr_fun h (Bruhat.upper 2)
    exact (mul_inv_eq_iff_eq_mul).mp he.symm

private def standardForm (x : Bool × SL) : MulAut SL :=
  if x.1 then MulAut.conj x.2 * diagram else MulAut.conj x.2

private theorem standardForm_injective : Function.Injective standardForm := by
  rintro ⟨b, g⟩ ⟨c, h⟩ he
  cases b <;> cases c
  · have : g = h := conj_injective he
    subst h
    rfl
  · change MulAut.conj g = MulAut.conj h * diagram at he
    exfalso
    apply diagram_ne_conj (h⁻¹ * g)
    calc
      diagram = (MulAut.conj h)⁻¹ * MulAut.conj g := by rw [he]; group
      _ = MulAut.conj (h⁻¹ * g) := by rw [map_mul, map_inv]
  · change MulAut.conj g * diagram = MulAut.conj h at he
    exfalso
    apply diagram_ne_conj (g⁻¹ * h)
    calc
      diagram = (MulAut.conj g)⁻¹ * MulAut.conj h := by rw [← he]; group
      _ = MulAut.conj (g⁻¹ * h) := by rw [map_mul, map_inv]
  · change MulAut.conj g * diagram = MulAut.conj h * diagram at he
    have : g = h := conj_injective (mul_right_cancel he)
    subst h
    rfl

/-- Coverage does not assume that an automorphism is inner. -/
theorem inner_or_graph (α : MulAut SL) :
    ∃ g : SL, α = MulAut.conj g ∨ α = MulAut.conj g * diagram := by
  have hc : Nat.card (MulAut SL) = 336 :=
    (Nat.card_congr (MulAut.congr equiv).toEquiv).trans Automorphisms.card_aut
  have hcard : Nat.card (Bool × SL) = Nat.card (MulAut SL) := by
    rw [Nat.card_prod, card_SL, hc]
    norm_num [Nat.card_eq_fintype_card]
  obtain ⟨⟨b, g⟩, hg⟩ :=
    ((Nat.bijective_iff_injective_and_card standardForm).mpr
      ⟨standardForm_injective, hcard⟩).2 α
  refine ⟨g, ?_⟩
  cases b
  · exact Or.inl hg.symm
  · exact Or.inr hg.symm

/-- A point residual invariant under an arbitrary automorphism excludes its
outer graph coset, and locates the inner implementer in the point parabolic. -/
theorem point_implementer (α : MulAut SL)
    (hA : ∀ a ∈ pointA, α a ∈ pointA) :
    ∃ g ∈ pointParabolicSL, α = MulAut.conj g := by
  obtain ⟨g, hg | hg⟩ := inner_or_graph α
  · refine ⟨g, inner_preserving_test g ?_ ?_, hg⟩
    · simpa only [hg, MulAut.conj_apply] using hA _ translations_mem.1
    · simpa only [hg, MulAut.conj_apply] using hA _ translations_mem.2
  · exfalso
    apply outer_exclusion_test g
    constructor
    · simpa only [hg, MulAut.mul_apply, MulAut.conj_apply] using hA _ translations_mem.1
    · simpa only [hg, MulAut.mul_apply, MulAut.conj_apply] using hA _ translations_mem.2

/-- The line result uses the very same diagram map and matrix carrier. -/
theorem line_implementer (α : MulAut SL)
    (hA : ∀ a ∈ lineA, α a ∈ lineA) :
    ∃ g ∈ lineParabolicSL, α = MulAut.conj g := by
  obtain ⟨g, hg, he⟩ := point_implementer (diagram * α * diagram)
    (line_preserving_transport α hA)
  exact ⟨diagram g, (diagram_point_line g).mpr hg, diagram_conj_transport α g he⟩

end Matrix.PSL3Two.MarkedAutomorphisms
