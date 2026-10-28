module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Coordinates.Projections

/-!
# Extending the marked six-point action

The symmetric supplement is a complement to the original cubic factor. Its
quotient isomorphism extends the local marked action to all of G. Cubic
fixation makes the same linear equivalence intertwine that full action; the
original alternating marking identifies the parity fiber. Both the natural
module and the five-dimensional augmentation core are retained.

Source: Aschbacher–Smith, B.5.7, printed p.106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
universe u v w
variable {G : Type u} [Group G]
variable (c : ChapterB.OuterSixThreeShape G)
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V) (d : Recovered c ρ)

private theorem extend_six_marking
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) W)
    (e : MarkedActionEquiv d.model.sectionData.space.toRepresentation ⊤
      (c.first.subgroupOf (c.first ⊔ d.offender)) σ (alternatingGroup (Fin 6))) :
    ∃ f : G →* Equiv.Perm (Fin 6), Function.Surjective f ∧
      f.ker = c.second ∧
      (alternatingGroup (Fin 6)).comap f = c.first ⊔ c.second ∧
      ∃ b : (firstMoved c ρ).toSubmodule ≃ₗ[ZMod 2] W,
        ∀ (g : G) (w : (firstMoved c ρ).toSubmodule),
          b ((firstMoved c ρ).toRepresentation g w) = σ (f g) (b w) := by
  let : c.second.Normal := second_normal c
  let H := c.first ⊔ d.offender
  let q := QuotientGroup.mk' c.second
  let qH := q.comp H.subtype
  have hsplit (g : G) : ∃ h ∈ H, ∃ x ∈ c.second, h * x = g := by
    exact mem_sup_of_normal_right.mp (d.supplement.symm ▸ mem_top g)
  have hqH : Function.Bijective qH := by
    constructor
    · apply (MonoidHom.ker_eq_bot_iff qH).mp
      apply bot_unique
      intro h hh
      have hh' : (h : G) ∈ c.second := (QuotientGroup.eq_one_iff (h : G)).mp hh
      apply Subtype.ext
      exact disjoint_def.mp d.supplement_disjoint h.property hh'
    · intro a
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective c.second a
      obtain ⟨h, hh, x, hx, rfl⟩ := hsplit g
      refine ⟨⟨h, hh⟩, ?_⟩
      change q h = q (h * x)
      have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [map_mul, hqx, mul_one]
  let j := MulEquiv.ofBijective qH hqH
  let s : H ≃* Equiv.Perm (Fin 6) := Subgroup.topEquiv.symm.trans e.action.groupEquiv
  let f : G →* Equiv.Perm (Fin 6) := (j.symm.trans s).toMonoidHom.comp q
  have hfH (h : H) : f h = s h := by
    change s (j.symm (j h)) = s h
    rw [j.symm_apply_apply]
  have hker : f.ker = c.second := by
    ext g
    change (j.symm.trans s) (q g) = 1 ↔ g ∈ c.second
    rw [map_eq_one_iff (j.symm.trans s) (j.symm.trans s).injective]
    exact QuotientGroup.eq_one_iff g
  have hfX (x : G) (hx : x ∈ c.second) : f x = 1 := by
    exact (show x ∈ f.ker from hker.symm ▸ hx)
  have hmark (h : H) : s h ∈ alternatingGroup (Fin 6) ↔ (h : G) ∈ c.first := by
    constructor
    · intro hh
      obtain ⟨l, hl⟩ := e.subgroupEquiv.surjective ⟨s h, hh⟩
      have he : s l = s h := (e.compatible l).trans (congrArg Subtype.val hl)
      have he' : l.val = h := s.injective he
      exact he' ▸ l.property
    · intro hh
      rw [show s h = (e.subgroupEquiv ⟨h, hh⟩ : Equiv.Perm (Fin 6)) from e.compatible ⟨h, hh⟩]
      exact (e.subgroupEquiv ⟨h, hh⟩).property
  have heven : (alternatingGroup (Fin 6)).comap f = c.first ⊔ c.second := by
    apply le_antisymm
    · intro g hg
      obtain ⟨h, hh, x, hx, rfl⟩ := hsplit g
      change f (h * x) ∈ alternatingGroup (Fin 6) at hg
      rw [map_mul, hfX x hx, mul_one, hfH ⟨h, hh⟩] at hg
      exact (c.first ⊔ c.second).mul_mem ((le_sup_left : c.first ≤ c.first ⊔ c.second) ((hmark ⟨h, hh⟩).mp hg))
        ((le_sup_right : c.second ≤ c.first ⊔ c.second) hx)
    · apply sup_le
      · intro l hl
        change f l ∈ alternatingGroup (Fin 6)
        rw [hfH ⟨l, (le_sup_left : c.first ≤ H) hl⟩]
        exact (hmark ⟨l, (le_sup_left : c.first ≤ H) hl⟩).mpr hl
      · intro x hx
        change f x ∈ alternatingGroup (Fin 6)
        rw [hfX x hx]
        exact one_mem _
  let b0 : (firstMoved c ρ).toSubmodule ≃ₗ[ZMod 2] d.model.sectionData.space.toSubmodule :=
    LinearEquiv.ofEq _ _ (model_space_eq ρ d.model).symm
  let b := b0.trans e.action.linearEquiv
  have hbH (h : H) (w : (firstMoved c ρ).toSubmodule) :
      b ((firstMoved c ρ).toRepresentation h w) = σ (s h) (b w) := by
    exact e.action.intertwines ⟨h, mem_top _⟩ (b0 w)
  have hbX (x : G) (hx : x ∈ c.second) (w : (firstMoved c ρ).toSubmodule) :
      (firstMoved c ρ).toRepresentation x w = w := by
    apply Subtype.ext
    exact d.first_fixed w.property ⟨x, hx⟩
  refine ⟨f, (j.symm.trans s).surjective.comp (QuotientGroup.mk'_surjective c.second),
    hker, heven, b, ?_⟩
  intro g w
  obtain ⟨h, hh, x, hx, rfl⟩ := hsplit g
  rw [map_mul, Module.End.mul_apply, hbX x hx, hbH ⟨h, hh⟩,
    map_mul, hfX x hx, mul_one, hfH ⟨h, hh⟩]

include d in
/-- Extend the recovered marked six-point action to every element of G.
The projection is the quotient by the original cubic factor. -/
theorem six_coordinates : Nonempty (SixCoordinates c ρ) := by
  rcases d.marking with hn | hc
  · obtain ⟨e⟩ := hn
    obtain ⟨f, hs, hk, he, b, hb⟩ := extend_six_marking c ρ d
      (BinaryPermutation.naturalRepresentation (Fin 6)) e
    exact ⟨⟨f, hs, hk, he, Or.inl ⟨b, hb⟩⟩⟩
  · obtain ⟨e⟩ := hc
    obtain ⟨f, hs, hk, he, b, hb⟩ := extend_six_marking c ρ d
      (BinaryPermutation.coreRepresentation (Fin 6)) e
    exact ⟨⟨f, hs, hk, he, Or.inr ⟨b, hb⟩⟩⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
