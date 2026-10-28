module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly.Components
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly.SourceAction
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Actual component inputs for the source irreducible exclusion

The marked elementary actor embeds in the automorphism group of the
irreducibly acting normal subgroup, giving the needed binary degree bound.
When that subgroup is itself a component, its already proved trivial center
makes it simple. The actual two-core quotient is SQTK, so the proved Theorem C
supplies its full model catalogue. No universal G.9 classification is assumed.

Source: Aschbacher--Smith, 15.3.58, printed p.1149; G.9.3, printed pp.354--357.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
open ChapterG.Section09 Theory.GroupTheory
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- The original actor bounds the degree through automorphisms of the actual normal subgroup. -/
theorem SourceData.degree_le_component_automorphisms (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) :
    Module.finrank (ZMod 2) W ≤ 2 * (primeRank 2 (MulAut K) + 1) := by
  let : Representation.IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  have hn : X ≤ normalizer (K : Set H) := by
    rw [normalizer_eq_top_iff.mpr hK.normal]
    exact le_top
  exact h.setup.degree_le.trans (Nat.mul_le_mul_left 2
    (Nat.add_le_add_right (h.setup.rank_le_automorphisms hn) 1))

/-- A simple normal component supplies the exact single-component G.9 input. -/
theorem SourceData.simple_componentHypothesis (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hq : IsSQTK KnownSimple.IsKnownSimple H)
    (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K) :
    ComponentHypothesis KnownSimple.IsKnownSimple ρ X K K (s + 1) := by
  let := hsimple
  let : IsQuasisimple K := ChapterA.Section02.Sporadic.SourceAssembly.simple_quasisimple hnonab
  exact { h.setup with
    quotient := ⟨{
      Cover := H
      sqtk := hq
      projection := MonoidHom.id H
      surjective := Function.surjective_id }⟩
    component := ⟨hK.normal.isSubnormal, inferInstance⟩
    noncentral := h.actor_noncentral hK
    normal_H := hK.normal
    irreducible := hK.irreducible
    components := Or.inl rfl }

omit [FiniteDimensional (ZMod 2) W] in
/-- The source component join is centerless, so it is simple whenever it is a component. -/
theorem ComponentData.simple_of_component (hK : ComponentData ρ K)
    (hc : IsComponent H K) : IsSimpleGroup K ∧ ¬ IsMulCommutative K := by
  let : IsQuasisimple K := hc.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let e : K ≃* (K ⧸ center K) :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hK.center_eq_bot.symm)
  refine ⟨e.isSimpleGroup, ?_⟩
  intro hab
  let := hab
  exact hK.nonsolvable inferInstance

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction ChapterA.Section02
variable {G : Type*} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {v : ActorQuotient Z} {s : ℕ}

/-- The completed Theorem C classifies the actual irreducible component in the actor quotient. -/
theorem NormalReduction.EarlierSourceInputs.model_of_component
    (d : EarlierSourceInputs Z ZS V M KnownSimple.IsKnownSimple v s)
    {K : Subgroup (ActorQuotient Z)}
    (hK : IrreducibleSieve.ComponentData (actorRepresentation Z ZS d.kernel) K)
    (hc : Theory.GroupTheory.IsComponent (ActorQuotient Z) K) :
    IsSimpleGroup K ∧ ¬ IsMulCommutative K ∧ IsTheoremCModel K := by
  obtain ⟨hs, hn⟩ := hK.simple_of_component hc
  have hqt := actor_sqtk Z d.sqtk
  exact ⟨hs, hn, theoremC_knownSimple hs hn (hqt.stronglyQuasithin.subgroup K)
    (hqt.isKGroup.subgroup K)⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
