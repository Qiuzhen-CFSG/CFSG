module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.Basic

/-!
# Centralizer bounds before the two-group calculation

An outside conjugate of H cannot contain a subgroup of either factor whose
order exceeds two, by clause (c). Applied to the fixed subgroup of t in the
factor intersection, this gives the centralizer bound used to recognize
(A₁ ∩ A₂)⟨t⟩. Once the intersection has order two, either dihedral or
semidihedral factor model would give the full exceptional alternative,
including a conjugator fused into A₁. This argument handles a starting
involution in either factor.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the intersecting branch of contrary fusion.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

theorem LocalControl.factor_centralizer_card_le_two
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hg : g ∉ intersectionGenerated A₁ A₂) (X : Subgroup G) (hX : X ≤ A₁ ∨ X ≤ A₂) :
    Nat.card (X ⊓ centralizer ({g⁻¹ * a * g} : Set G) : Subgroup G) ≤ 2 := by
  by_contra hn
  have hcard : 2 < Nat.card (X ⊓ centralizer ({g⁻¹ * a * g} : Set G) : Subgroup G) :=
    Nat.lt_of_not_ge hn
  have hfactor : X ⊓ centralizer ({g⁻¹ * a * g} : Set G) ≤ A₁ ∨
      X ⊓ centralizer ({g⁻¹ * a * g} : Set G) ≤ A₂ :=
    hX.imp (inf_le_left.trans ·) (inf_le_left.trans ·)
  have hconj : conjugate (X ⊓ centralizer ({g⁻¹ * a * g} : Set G)) g⁻¹ ≤
      intersectionGenerated A₁ A₂ := by
    rintro _ ⟨b, hb, rfl⟩
    apply h.centralizer_le_generated ha ha1
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp hb.2)
    simpa [MulAut.conj_apply, mul_assoc] using hh
  have hgi := ((l.unique_large _ hfactor hcard).2 g⁻¹).mp hconj
  exact hg ((intersectionGenerated A₁ A₂).inv_mem_iff.mp hgi)

theorem LocalControl.intersection_centralizer_card_le_two
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hg : g ∉ intersectionGenerated A₁ A₂) :
    Nat.card ((A₁ ⊓ A₂) ⊓ centralizer ({g⁻¹ * a * g} : Set G) : Subgroup G) ≤ 2 :=
  l.factor_centralizer_card_le_two h ha ha1 hg (A₁ ⊓ A₂) (Or.inl inf_le_left)

theorem MinimalCounterexample.not_model_of_intersection_card_two
    (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) :
    ¬ DihedralOrSemidihedral A₁ := by
  intro hm
  let t := g⁻¹ * a * g
  have hs := l.swap_of_outside_transporter m.setup ha ha1 hg ht
  have hfused : ∃ k : G, k⁻¹ * t * k ∈ A₁ := by
    rcases ha with ha | ha
    · refine ⟨g⁻¹, ?_⟩
      have he : (g⁻¹)⁻¹ * t * g⁻¹ = a := by dsimp [t]; group
      rw [he]
      exact ha
    · refine ⟨g⁻¹ * t, ?_⟩
      have hat : t⁻¹ * a * t ∈ A₁ := by
        rw [← hs.2]
        exact mem_map.mpr ⟨a, ha, by simp [t, mul_assoc]⟩
      convert hat using 1
      dsimp [t]
      group
  exact m.fails (Or.inr (Or.inr ⟨⟨t, hs.1, hfused⟩, hm, hcap⟩))

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
