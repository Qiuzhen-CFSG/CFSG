module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionOdd
public import Theory.SpecificGroups.OddThreeSectionRank
public import Theory.SpecificGroups.PSL2.RootTwoRank
/-!
# Source degrees in the odd ternary rows

The secondary image is a literal subgroup of the inner component. Its binary
PSL₂ quotient supplies an elementary subgroup of rank n. Every section of an
odd ternary model has two-rank at most three, so n is at most three. The proof
uses the actual subgroup inclusion and quotient by its two-core; it does not
assume monotonicity of ordinary two-rank under arbitrary quotients.
Source: Aschbacher--Smith A.2.3 and 4.3.16, printed pp.33 and 618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

private theorem secondary_degree_le_of_section_bound
    (s : SecondaryActionData c n) {A : Type*} [Group A] [Finite A]
    (e : SecondaryActionData.componentImage s ≃* A)
    (hb : ∀ B : Subgroup A, primeRank 2 (B ⧸ pCore 2 B) ≤ 3) : n ≤ 3 := by
  let := s.normal
  let X := SecondaryActionData.secondaryImage s
  let I := SecondaryActionData.componentImage s
  have hXI : X ≤ I := SecondaryActionData.secondaryImage_le_componentImage s
  let f := e.toMonoidHom.comp (inclusion hXI)
  have hf : Function.Injective f := e.injective.comp (inclusion_injective hXI)
  let a : X ≃* f.range := MonoidHom.ofInjective hf
  let b := QuotientGroup.congr (pCore 2 X) (pCore 2 f.range) a (pCore_map_iso 2 a)
  have hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^n) :=
    SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
  obtain ⟨F,_,_,hF,⟨d⟩⟩ := hm
  have hl := Theory.PSL2.root_two_rank_ge F hF
  rw [←primeRank_congr 2 d,primeRank_congr 2 b] at hl
  exact hl.trans (hb f.range)

/-- Every odd ternary inner model bounds the original source degree by three. -/
theorem SecondaryActionData.odd_ternary_degree_le_three
    (s : SecondaryActionData c n) {p : ℕ} (_hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
      ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p) : n ≤ 3 := by
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact secondary_degree_le_of_section_bound s e (fun B =>
      Theory.SpecificGroups.OddThreeSectionRank.psl3_subgroup_quotient_twoRank_le_three
        (by rwa [hF]) B (pCore 2 B))
  · obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_equiv (SecondaryActionData.componentImage s) e.toEquiv
    exact secondary_degree_le_of_section_bound s e (fun B =>
      Theory.SpecificGroups.OddThreeSectionRank.psu3_subgroup_quotient_twoRank_le_three J
        (by rw [hF]; exact ho.pow) B (pCore 2 B))
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
