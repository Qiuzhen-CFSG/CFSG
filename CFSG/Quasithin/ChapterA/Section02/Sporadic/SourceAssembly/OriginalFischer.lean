module
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.FischerSymplectic
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
/-!
# Fischer sections in the literal source quotient S/Z(S)

The original reduction supplies a surjection G onto S, and the semisimple S
is perfect. Its central quotient is therefore centerless. A supplied Fischer
involution-centralizer section lifts to a proper two-local of G; the actual
PSp6(2) section and the original proper-section induction contradict its
ordinary three-rank. No numerical two-rank theorem for the Fischer carrier,
quasisimplicity of G, or quasithinness of S/Z(S) is required.
Source: Aschbacher--Smith A.2.12 and A.2.19, printed pp.36,40--41.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u v
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Group S] [Finite G] [Finite S]
  {H : Type v} [Group H] {p : ℕ}
/-- A concrete Fischer centralizer section contradicts the original A counterexample. -/
theorem CounterexampleToTheoremA.centralQuotient_no_fischer_of_source_data
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (e : S ⧸ center S ≃* H)
    (d : InvolutionCentralizerQuotientData H _root_.Sporadic.Fischer.Fi22.Carrier) : False := by
  let : Group.IsPerfect S := h.2.2.2.1.isPerfect
  obtain ⟨f,hf⟩ := h.exists_surjective ih.theoremA
  let π := e.toMonoidHom.comp ((QuotientGroup.mk' (center S)).comp f)
  have hπ : Function.Surjective π := e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hf)
  have hZ : center H = ⊥ := by
    apply bot_unique
    intro x hx
    have hz : e.symm x ∈ center (S ⧸ center S) := ((Subgroup.centerCongr e).symm ⟨x,hx⟩).property
    rw [Group.IsPerfect.center_quotient_center_eq_bot S] at hz
    exact mem_bot.mpr (e.symm.injective ((mem_bot.mp hz).trans e.symm.map_one.symm))
  obtain ⟨j,hj⟩ := Theory.SpecificGroups.U6Two.SymplecticEmbedding.exists_embedding
  let du := Sporadic.SourceAssembly.fischer_unitary_data d
  let ds := (du.restrictTarget j.range).mapTarget (MonoidHom.ofInjective hj).symm
  let : IsSimpleGroup (ClassicalGroup.PSp 3 (ZMod 2)) :=
    leechPSp6Two_simple
  exact Sporadic.SourceAssembly.false_of_centralizer_quotient ih h.1 h.2.1 π hπ hZ ds
    leechPSp6Two_nonabelian
    leechPSp6Two_primeRank_three_gt_two
end CFSG.Quasithin.ChapterA.Section02
