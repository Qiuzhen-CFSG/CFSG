module

public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.RootComponents
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SylowPointwiseInner
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Sylow-fixed symplectic automorphisms and their C-components

Given the diagram-preserving semilinear classification, an automorphism
fixing a Sylow two-subgroup pointwise is inner. Triviality of the symplectic
center retains the order of its conjugating element. Given the root/c₂
involution table, a nonsolvable fixed group must therefore be a root
centralizer. The explicit root-centralizer extension transports over the
same field, and its only relative C-component is the entire fixed group.

The classification and involution-table premises are deliberately explicit.
The root-centralizer component calculation is proved independently in
`RootComponents`; this module does not assert either remaining classification.

Source: Aschbacher--Smith, E.6.25, printed p.256, and 16.1.4/16.1.6,
printed pp.1171--1172 (combined manuscript of 1 March 2004).
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open DiagramAutomorphisms InvolutionTypes
variable {F H : Type*} [Field F] [Finite F] [CharP F 2] [Group H] [Finite H]

/-- Nonsolvability selects a root centralizer; the natural extension retains F. -/
theorem fixed_naturalExtension_of_model_calculations {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (htable : ∀ g : Sp F, orderOf g = 2 →
      IsRootElement g ∨ IsPGroup 2 (centralizer ({g} : Set (Sp F))))
    (e : H ≃* Sp F) (a : MulAut H) (ha : orderOf a = 2)
    (S : Sylow 2 H) (hS : ∀ x ∈ (S : Subgroup H), a x = x)
    (hns : ¬ Group.IsSolvable a.fixedSubgroup) :
    ∃ (Q : Subgroup a.fixedSubgroup) (_ : Q.Normal),
      Nonempty (NaturalExtension (F := F) Q) := by
  let b := MulAut.congr e a
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  have hP : ∀ x ∈ (P : Subgroup (Sp F)), b x = x := by
    rintro x ⟨y, hy, rfl⟩
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hS y hy]
  obtain ⟨g, _, hg⟩ := aut_fixing_sylow_inner hcard hn hclass P b hP
  have hg2 : orderOf g = 2 := by
    rw [hg, MulAut.conj_orderOf_of_center_eq_bot EvenProjective.center_eq_bot] at hb
    exact hb
  have hfix : b.fixedSubgroup = centralizer ({g} : Set (Sp F)) := by
    rw [hg, MulAut.fixedSubgroup_conj]
  let c := (MulAut.fixedSubgroupCongr e a).trans (MulEquiv.subgroupCongr hfix)
  rcases htable g hg2 with hr | hp
  · obtain ⟨Q, hQ, ⟨d⟩⟩ := root_centralizer_naturalExtension hcard hn g hr
    let := hQ
    exact ⟨Q.comap c.toMonoidHom, inferInstance, ⟨d.comap c⟩⟩
  · let : Group.IsNilpotent (centralizer ({g} : Set (Sp F))) := hp.isNilpotent
    exact (hns (Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective)).elim

/-- Construct the relative component's extension, including its natural module. -/
theorem fixed_cComponent_naturalExtension_of_model_calculations {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (htable : ∀ g : Sp F, orderOf g = 2 →
      IsRootElement g ∨ IsPGroup 2 (centralizer ({g} : Set (Sp F))))
    (e : H ≃* Sp F) (a : MulAut H) (ha : orderOf a = 2)
    (S : Sylow 2 H) (hS : ∀ x ∈ (S : Subgroup H), a x = x)
    {B : Subgroup H} (hBfix : B ≤ a.fixedSubgroup)
    (hB : (B.subgroupOf a.fixedSubgroup).IsCComponent) :
    B = a.fixedSubgroup ∧ ∃ (Q : Subgroup B) (_ : Q.Normal),
      Nonempty (NaturalExtension (F := F) Q) := by
  have hns : ¬ Group.IsSolvable a.fixedSubgroup := by
    intro hs
    let := hs
    exact hB.not_isSolvable inferInstance
  obtain ⟨Q, hQ, ⟨d⟩⟩ := fixed_naturalExtension_of_model_calculations
    hcard hn hclass htable e a ha S hS hns
  let := hQ
  have hF : 2 < Nat.card F := by
    rw [hcard]
    exact lt_of_eq_of_lt (by decide : 2 = 2 ^ 1)
      (Nat.pow_lt_pow_right (by decide) hn)
  have he : B = a.fixedSubgroup :=
    le_antisymm hBfix (subgroupOf_eq_top.mp (d.cComponent_eq_top hF hB))
  refine ⟨he, ?_⟩
  subst B
  exact ⟨Q, hQ, ⟨d⟩⟩
end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
