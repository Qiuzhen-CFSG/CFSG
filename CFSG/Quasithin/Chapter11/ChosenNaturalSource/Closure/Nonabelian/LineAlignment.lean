module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Conditions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Plane
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Movement

/-!
# Assembly of line alignment from the elementary plane-action rank

The corank estimate first makes V₂ normalize Vᵍ. The source intersection
theorem then bounds [V₂,Vᵍ∩T] by a field line in V. The plane-movement
calculation identifies this nontrivial commutator with V₁. Applying the
intersection theorem to g⁻¹ bounds the same V₁ by an Lᵍ-conjugate of V₁ᵍ.
These groups have equal orders, so they are equal. The resulting right
correction g*l normalizes V₁ and preserves Vᵍ.

This last equal-cardinality argument avoids needing a separate recognition
of the transvections on Vᵍ. Movement.lean proves the original plane calculation,
including removal of field automorphisms at q=4. The elementary plane-action
rank remains an explicit prerequisite. Consequently this is a conditional
assembly, not a proof of 11.5.3(3). The final application supplies both literal
weak-closure bounds used by the original source argument.
Source: Aschbacher--Smith, 11.5.3(3), printed pp.779--780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterE CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (F₀ : MarkedFlag E)

omit [Finite G] in
private theorem conjugate_mul (P : Subgroup G) (g l : G) :
    P.map (MulAut.conj (g*l)).toMonoidHom =
      (P.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    mul_inv_rev, mul_assoc]

include F₀ in
/-- The second intersection line and equality of orders finish the geometric
step once the original plane commutator has been identified with V₁. -/
theorem align_of_commutator_eq_point
    (hintersection : ∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
        E.V₁.map (MulAut.conj l).toMonoidHom)
    (g : G) (hg : g ∉ normalizer (V : Set G))
    (hnorm : E.V₂ ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hpoint : ⁅E.V₂, V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G)⁆ = E.V₁) :
    ∃ c ∈ E.G₁, V.map (MulAut.conj c).toMonoidHom = V.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨_, _, l, hl, hlines⟩ := intersection_two_lines hintersection g hg
  have hle : E.V₁ ≤ (E.V₁.map (MulAut.conj l).toMonoidHom).map
      (MulAut.conj g).toMonoidHom := by
    have hc := commutator_le_intersection F₀ g hnorm
    rw [hpoint] at hc
    exact hc.trans (hlines.trans inf_le_right)
  have he : (E.V₁.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom = E.V₁ := by
    apply (eq_of_le_of_card_ge hle ?_).symm
    rw [card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (MulAut.conj l).injective]
  refine ⟨g*l, ?_, ?_⟩
  · exact mem_normalizer_iff_map_conj_eq.mpr ((conjugate_mul E.V₁ g l).trans he)
  · have hv : V.map (MulAut.conj l).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (D.normalizes hl)
    rw [conjugate_mul, hv]

/-- Conditional final assembly. Its two local model premises must be proved
from the full natural marking before asserting the source line alignment. -/
theorem of_plane_calculations
    (hintersection : ∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
        E.V₁.map (MulAut.conj l).toMonoidHom)
    (hr : (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ globalR V)
    (hrank : PlaneActionRankBound (E := E)) (hmove : PlaneMovement (E := E)) :
    Nonabelian.LineAlignment E := by
  intro g hcor hne
  change subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
    (V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G)) ≤ 1 at hcor
  change ¬ E.V₂ ≤ centralizer
    ((V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G) : Subgroup G) : Set G) at hne
  change ∃ c ∈ E.G₁, V.map (MulAut.conj c).toMonoidHom = V.map (MulAut.conj g).toMonoidHom
  by_cases hg : g ∈ normalizer (V : Set G)
  · refine ⟨1, E.G₁.one_mem, ?_⟩
    have hi : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
    rw [hi, map_id]
    exact (mem_normalizer_iff_map_conj_eq.mp hg).symm
  · let := D.elementary
    let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
      IsElementaryAbelian.map _
    let _ : IsElementaryAbelian 2
        (V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G) : Subgroup G) :=
      IsElementaryAbelian.of_le (show V.map (MulAut.conj g).toMonoidHom ⊓
        (T : Subgroup G) ≤ V.map (MulAut.conj g).toMonoidHom from inf_le_left)
    have hn := plane_normalizes F₀ g hr hcor (hrank _ inf_le_right inferInstance)
    apply align_of_commutator_eq_point F₀ hintersection g hg hn
    apply hmove _ inf_le_right inferInstance hne
    obtain ⟨l, hl, hline⟩ := hintersection g hg
    exact ⟨l, hl, (commutator_le_intersection F₀ g hn).trans hline⟩

/-- The actual downstream application, with precisely the two outstanding
plane-action calculations retained as premises. -/
theorem plane_le_weakCentralizer_of_plane_calculations
    (hintersection : ∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
        E.V₁.map (MulAut.conj l).toMonoidHom)
    (hr : (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ globalR V)
    (hrank : PlaneActionRankBound (E := E)) (hmove : PlaneMovement (E := E))
    (habelian : IsMulCommutative E.W) :
    E.V₂ ≤ weakCentralizer V (T : Subgroup G) 1 :=
  plane_le_weakCentralizer_of_alignment E
    (of_plane_calculations F₀ hintersection hr hrank hmove) habelian

/-- The original fixed-space and normalizer conditions discharge the plane
movement premise. Only the elementary induced-action rank remains to be proved. -/
theorem of_plane_rank
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ E.M)
    (hintersection : ∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
        E.V₁.map (MulAut.conj l).toMonoidHom)
    (hr : (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ globalR V)
    (hrank : PlaneActionRankBound (E := E)) : Nonabelian.LineAlignment E :=
  of_plane_calculations F₀ hintersection hr hrank (plane_movement F₀ hfixed hNV)

/-- Both bounds for the actual source E.3.19 application, now retaining only
the elementary plane-action rank in addition to the preceding source facts. -/
theorem weakClosure_bounds_of_plane_rank
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ E.M)
    (hintersection : ∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
        E.V₁.map (MulAut.conj l).toMonoidHom)
    (hr : (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ globalR V)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hobstruction : Chapter11.Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (hrank : PlaneActionRankBound (E := E)) (habelian : IsMulCommutative E.W) :
    centralizer (weakCentralizer V (T : Subgroup G) 1 : Set G) ≤ E.M ∧
      E.H ⊓ normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ E.M := by
  apply weakClosure_bounds_of_abelian E F₀ hfixed hNV _ hH hobstruction
    (of_plane_rank F₀ hfixed hNV hintersection hr hrank) habelian
  rwa [corank_line F₀ hfixed]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
