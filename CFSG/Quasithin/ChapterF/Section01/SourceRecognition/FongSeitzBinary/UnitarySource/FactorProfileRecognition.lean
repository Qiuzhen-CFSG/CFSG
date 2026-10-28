module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OriginalActorQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.QuadraticProfileRecognition

/-!
# The quadratic U₄ comparison from the original factor markings

Start with actual PSL₂ quotient isomorphisms on the two original factors,
with quadratic field orders, an elementary larger-root parabolic core and
a nonabelian opposite core. OriginalActorQuotient extends those given maps
to the full actors S L_i with exactly the parabolic-core kernels. Their
Sylow restrictions prove both elementary quotient clauses; the same marked
panels give both full-Borel indices. The existing quadratic-profile theorem
then constructs the full U₄ amalgam comparison.

Thus no actor extension, actor-kernel equality, elementary Sylow quotient,
Borel-index equality, or local regularity is an additional premise here.
Both orientations and all positive binary degrees are retained. The same
quotient and full amalgam marking supply both endpoint squares. The actual
Chapter 12 application keeps its proper-K and full KnownSimple preparation.

The original quadratic profile, genuine marked split quotient and rotation
order four remain earlier DGS inputs. Exhaustive source selection and the
other rank-two rows remain separate obligations of final assembly.
Source: DGS (11.5)--(11.7), pp.173--175 and Theorem D, p.224;
Fong--Seitz I (6A)(b), pp.37--38, II (8B), pp.201--202; AS 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X F k : Type*} [Group G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
  (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
  (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥)
  (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n)

include mark h split hm hij μi μj hfields helem hne hk in
/-- Actual original factor isomorphisms discharge every auxiliary local marking
premise of the selected quadratic U₄ comparison. -/
theorem marked_quadratic_factor_unitaryFour_catalogue :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  obtain ⟨fi,hfi,hki,_⟩ := MarkedLocal.linear_actor_quotient_of_factor Q mark h split i μi
  obtain ⟨fj,hfj,hkj,_⟩ := MarkedLocal.linear_actor_quotient_of_factor Q mark h split j μj
  have hQi := MarkedLocal.sylow_core_elementary_of_linear_actor h i fi hki
  have hQj := MarkedLocal.sylow_core_elementary_of_linear_actor h j fj hkj
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hindexi : (commonBorel L S).relIndex (parabolic L S i) = Nat.card F + 1 := by
    rw [QuadrangleStructure.marked_commonBorel_root_index Q mark h split i,
      MarkedLocal.simpleRoot_card_linear Q mark h split i Ti hTi μi, Nat.add_comm]
  have hindexj : (commonBorel L S).relIndex (parabolic L S j) = Nat.card k + 1 := by
    rw [QuadrangleStructure.marked_commonBorel_root_index Q mark h split j,
      MarkedLocal.simpleRoot_card_linear Q mark h split j Tj hTj μj, Nat.add_comm]
  exact marked_quadratic_profile_unitaryFour_catalogue Q mark h split hm i j hij
    fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source
open ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X F k : Type*} [Group G] [Finite G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : (((![L,R] : Fin 2 → Subgroup G) i) ⧸
    pCore 2 ((![L,R] : Fin 2 → Subgroup G) i)) ≃* PSL(2,F))
  (μj : (((![L,R] : Fin 2 → Subgroup G) j) ⧸
    pCore 2 ((![L,R] : Fin 2 → Subgroup G) j)) ≃* PSL(2,k))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (helem : IsElementaryAbelian 2
    ((parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) i).pCoreIn 2))
  (hne : ⁅(parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) j).pCoreIn 2,
    (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) j).pCoreIn 2⁆ ≠ ⊥)
  (m : ℕ) [NeZero m] (hk : Nat.card k = 2^m)

include D h hmany hn hpsl hH d mark split hm hij μi μj hfields helem hne hk in
/-- The literal Chapter 12 pair obtains its full comparison from its quadratic
factor profile, with no extra actor or Sylow quotient hypotheses. -/
theorem rankOne_unitaryFour_quadratic_factor_comparison :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
  exact marked_quadratic_factor_unitaryFour_catalogue Q mark hf split hm i j hij μi μj
    hfields helem hne m hk

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
