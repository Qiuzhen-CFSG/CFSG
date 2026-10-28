module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearSourceExtension
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearFixed

/-!
# The original cubic extension and its radical fixed-point bound

The cubic chosen in O₂,Z(K) simultaneously gives the marked PGL₃(4)
extension of K_Z and an exact complement of order sixteen to Q in R₂.
The extension projection has kernel the mapped intrinsic O₂(K_Z), and
its action is the same normalQuotientAction as the corrected source sieve.
In particular the cubic used for the fixed-point calculation is the one
in the extension, with no change of its diagonal action.

The component-core section theorem applies the bound through both original
subtype maps. It discharges the ambient fixed-point bound needed in the
terminal representation argument. Recognition of that actual extension
module, including the determinant twist, remains with this nonblock owner,
as do construction of MSData and the source geometry. This module does not
assert the final nonblock contradiction.
Source: Aschbacher--Smith, conclusion of original 4.3.2, pp.618--619.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  {T : Sylow 2 G} {L V : Subgroup G} {c : SourceConfiguration T L}

/-- The same actual cubic supplies the marked extension, its literal quotient
conjugation, and the exact whole-radical fixed-point calculation. -/
theorem exists_source_cubic_extension_with_fixed_radical (d : MSData c 2)
    (m : RootCoordinates d) (s : SecondarySourceData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hF : Nat.card F = 4) (e : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F)) :
    ∃ X : Subgroup G, Nat.card X = 3 ∧ X ≤ (K c).coreCenterIn 2 ∧
      X ≤ rootNormalizer c ∧ X ⊓ s.component.map (rootNormalizer c).subtype = ⊥ ∧
      Q c ⊓ centralizer (X : Set G) = ⊥ ∧
      ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2 ∧ ⁅Q c,X⁆ = Q c ∧
      ⁅R₂ c,X⁆ = Q c ∧
      Q c ⊔ (R₂ c ⊓ centralizer (X : Set G)) = R₂ c ∧
      Nat.card (R₂ c ⊓ centralizer (X : Set G) : Subgroup G) = 16 ∧
      ∃ φ : cubicExtension s X →* Matrix.ProjGenLinGroup (Fin 3) F,
        Function.Surjective φ ∧
        φ.ker = (pCore 2 s.component).map (cubicComponentInclusion s X) ∧
        pCore 2 (cubicExtension s X) =
          (pCore 2 s.component).map (cubicComponentInclusion s X) ∧
        (∀ b : s.component, φ (cubicComponentInclusion s X b) =
          Matrix.ProjectiveSpecialLinearGroup.toPGL
            (e (QuotientGroup.mk' (pCore 2 s.component) b))) ∧
        ∀ (g : cubicExtension s X) (z : s.component ⧸ pCore 2 s.component),
          e (s.action g z) = (pglEquivInnerDiagonal F (φ g)).val (e z) := by
  obtain ⟨X,hX,hXK,hr,hdisj,hfix,hcomm,hmoved,φ,hφ,hker,hcore,hmark,haction⟩ :=
    exists_source_cubic_extension d s D h hF e
  exact ⟨X,hX,hXK,hr,hdisj,hfix,hcomm,hmoved,
    m.radical_cubic_commutator D s X hXK hmoved,
    (m.radical_cubic_complement D s X hX hXK hfix).1,
    m.radical_cubic_fixed_card D s X hX hXK hfix,
    φ,hφ,hker,hcore,hmark,haction⟩

/-- Every invariant section of the actual extension's two-core satisfies the
same fixed-point bound. The exact core identity comes from the marked extension;
no identification of the extension representation is inferred from its restriction. -/
theorem cubic_extension_core_section_fixed_card_le (d : MSData c 2)
    (m : RootCoordinates d) (s : SecondarySourceData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
    (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
    (hcore : pCore 2 (cubicExtension s X) =
      (pCore 2 s.component).map (cubicComponentInclusion s X))
    (A : Subgroup G)
    (hA : A ≤ ((pCore 2 (cubicExtension s X)).map (cubicExtension s X).subtype).map
      (rootNormalizer c).subtype)
    [Normalizes X A] {M : Type*} [Group M] [MulDistribMulAction X M]
    (f : A →* M) (hf : Function.Surjective f)
    (he : ∀ (x : X) (a : A), f (x • a) = x • f a) :
    Nat.card (FixedPoints.subgroup X M) ≤ 16 := by
  apply m.cubic_component_section_fixed_card_le D s X hX hXK hfix A _ f hf he
  have hc : (pCore 2 (cubicExtension s X)).map (cubicExtension s X).subtype =
      (pCore 2 s.component).map s.component.subtype := by
    rw [hcore, map_map]
    rfl
  rwa [hc] at hA

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
