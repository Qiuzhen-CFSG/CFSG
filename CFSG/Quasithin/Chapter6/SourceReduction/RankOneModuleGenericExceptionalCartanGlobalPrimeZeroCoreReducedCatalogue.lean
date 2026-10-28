module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreReduced
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreUnitaryExtensions
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue

/-!
# Broad reduced comparisons on the original Cartan prime pair

The literal reduced diagram is identified with the original zero-core
pair before applying any model exclusion. All seven regular families,
the degree-two unitary extension and the exceptional parabolic comparisons
are retained in the input. The general U₅(q) input is separate: quasithinness
forces q = 4 through its actual endpoint embedding. Small Ree type clauses
are handled by their quotient solvability, without supplying an Iso.

These are restrictions of supplied earlier DGS comparisons, not an
exhaustiveness theorem. In particular they neither assume the four final
cubic rows nor identify the selected R with a component of H.
Source: Aschbacher–Smith F.1.12, pp.263–264, and 5.2.2, pp.647–648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
  (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
  (hz : (generated L H D R).pCoreIn 2 = ⊥)

private theorem exclude_transported
    {A B C A' B' C' X Y Z : Type*}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    [Group X] [Group Y] [Group Z]
    {α : RankTwoAmalgam A B C} {β : RankTwoAmalgam A' B' C'}
    {γ : RankTwoAmalgam X Y Z} (f : Iso α β)
    (hn : ¬ Nonempty (ParabolicEquiv α γ) ∧ ¬ Nonempty (ParabolicEquiv α γ.reverse))
    (he : Nonempty (Iso β γ) ∨ Nonempty (Iso β γ.reverse)) : False := by
  rcases he with he | he
  · exact hn.1 ⟨(f.trans he.some).toParabolicEquiv⟩
  · exact hn.2 ⟨(f.trans he.some).toParabolicEquiv⟩

private theorem transport_exceptional
    {A B C A' B' C' : Type*}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    {α : RankTwoAmalgam A B C} {β : RankTwoAmalgam A' B' C'}
    (f : Iso α β) (k : ExceptionalModels.Case)
    (he : ExceptionalModels.ParabolicModel k β) : ExceptionalModels.ParabolicModel k α := by
  cases k <;> obtain ⟨e⟩ := he <;> exact ⟨f.toParabolicEquiv.trans e⟩

include d h hH c hd hz in
/-- Every concrete broad reduced catalogue row is excluded on the SAME
selected pair, with both regular squares and the weaker exceptional maps. -/
theorem LocalData.zeroCore_not_reduced_comparison :
    ¬ Global.ConcreteAmalgamComparison
      (reducedAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) := by
  intro hc
  let f := d.zeroCoreReducedIso h hH c hd hz
  cases hc with
  | linear F m hm hF he =>
    exact exclude_transported f (d.zeroCore_not_linear_parabolic h hH c hd hz hm hF) he
  | symplectic F m hm hF he =>
    exact exclude_transported f (d.zeroCore_not_symplectic_parabolic h hH c hd hz hm hF) he
  | g2 F he =>
    let : Fintype F := Fintype.ofFinite F
    obtain ⟨m,_,hm⟩ := FiniteField.card F 2
    have hF : Nat.card F = 2^(m : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hm
    exact exclude_transported f (d.zeroCore_not_g2_parabolic h hH c hd hz m.pos hF) he
  | triality m hm he =>
    exact exclude_transported f (d.zeroCore_not_triality_parabolic h hH c hd hz m hm) he
  | ree m he =>
    exact exclude_transported f (d.zeroCore_not_ree_parabolic h hH c hd hz m) he
  | unitary m hm he =>
    exact exclude_transported f (d.zeroCore_not_unitaryFour_parabolic h hH c hd hz m hm) he
  | unitaryExtension m hm he =>
    exact exclude_transported f (d.zeroCore_not_unitaryFourExtension_parabolic h hH c hd hz m hm) he
  | unitaryFive M he =>
    exact exclude_transported f (d.zeroCore_not_unitaryFive_parabolic h hH c hd hz M) he
  | exceptional k he =>
    have hn := d.zeroCore_not_exceptional_parabolic h hH c hd hz k
    exact he.elim (fun e => hn.1 (transport_exceptional f k e))
      (fun e => hn.2 (transport_exceptional f.reverse k e))

include d h hH c hd hz in
/-- General U₅(q) reduced recognition is filtered at its actual parameter,
before restricting q to four. Both endpoint orientations are allowed. -/
theorem LocalData.zeroCore_not_reduced_unitaryFive
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (M : UnitaryFive.Model q) :
    ¬ (Nonempty (Iso (reducedAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H))
        M.amalgam) ∨
      Nonempty (Iso (reducedAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H))
        M.amalgam.reverse)) := by
  apply exclude_transported (d.zeroCoreReducedIso h hH c hd hz)
  exact d.zeroCore_not_unitaryFive_extension h hH c hd hz hq heven M M.amalgam
    (MonoidHom.id _) Function.injective_id (MonoidHom.id _) Function.injective_id

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
