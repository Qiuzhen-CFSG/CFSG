module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityOddMarking
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.DisplacementDegree

/-!
# The degree-three parity branch in the original chosen-module setup

The genuine natural marking and the completed residual producer build the
parity seed once global TI and F.8 geometry are supplied. The fixed-free
Cartan and critical-pair degree bound then reduce every odd exponent to
three. Consequently the final parity assembly needs the nine-dimensional
displacement calculation only for that degree, with the literal U/Z₁ and
quotient actors retained.

The global geometry and the remaining order-seven multiplicity proof are
still owned by qt-d-1222-linear-field-parity; no unconditional parity result
is asserted here. Source: Aschbacher–Smith 5.1.17, pp.640–642, and its
application in 12.2.2, p.795 (refs/quasithin.pdf).
-/

open Subgroup Theory.GroupTheory
public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- Under the actual odd F.8 geometry the field degree is exactly three. -/
theorem rankOne_odd_degree_eq_three_of_chosen_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hf : (setup T L V H A).Hypothesis)
    (hti : ∀ g : G,
      (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁) :
    n = 3 := by
  obtain ⟨s⟩ := D.rankOne_odd_seed_of_chosen_geometry h hmany hn hpsl hH hlinear c hodd hf hti
  exact s.exponent_eq_three_of_odd D.sylow_normalizes_component hpsl c hn hodd

/-- The original parity problem now has only the odd degree-three branch. -/
theorem rankOne_even_or_three_of_chosen_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgeometry : ∀ A B : Subgroup G, CartanPair T L H A B → Odd n →
      (setup T L V H A).Hypothesis ∧
        ∀ g : G,
          (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
            (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁) :
    Even n ∨ n = 3 := by
  rcases Nat.even_or_odd n with he | ho
  · exact Or.inl he
  · obtain ⟨A,B,c⟩ := D.rankOne_exists_cartanPair h.toHypothesis1221 hn hpsl hH hgen
    obtain ⟨hf,hti⟩ := hgeometry A B c ho
    exact Or.inr (D.rankOne_odd_degree_eq_three_of_chosen_geometry
      h hmany hn hpsl hH hlinear c ho hf hti)

/-- The final parity assembly needs the displacement calculation only in degree three. -/
theorem rankOne_even_exponent_of_geometry_and_degree_three_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgeometry : ∀ A B : Subgroup G, CartanPair T L H A B → Odd n →
      (setup T L V H A).Hypothesis ∧
        ∀ g : G,
          (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
            (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁)
    (hthree : n = 3 → DisplacementSource T L H n) : Even n := by
  apply D.rankOne_even_exponent_of_chosen_geometry_and_displacement
    h hmany hn hpsl hH hgen hlinear hgeometry
  intro A B c ho s
  exact hthree (s.exponent_eq_three_of_odd D.sylow_normalizes_component hpsl c hn ho) A B c ho s
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
