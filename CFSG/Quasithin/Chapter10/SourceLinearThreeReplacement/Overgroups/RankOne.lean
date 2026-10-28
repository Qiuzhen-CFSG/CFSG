module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Span
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# The actual rank-one embedding exclusion in the replacement argument

A component K of K_zT is local for the original full Sylow subgroup T.
Restricting that local condition to M₊ uses the literal subgroup inclusions.
If a containing C-component I of M₊ has quasisimple two-core quotient
PSL₂(2^n), the rank-one Sylow-overgroup theorem forces K=I. Their actual
T-orbits are consequently equal. No inference is made from an abstract
A₅ quotient or from equality of quotient images alone.

Source: Aschbacher--Smith §10.3, printed p.757, invoking the rank-one
non-enlargement case of A.3.12/A.3.14, printed pp.47--50.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
open Chapter3.Section02
open Theory.SpecificGroups.SymmetricFive.WreathComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- The complete local, Sylow and literal-core application of the rank-one
embedding theorem to the original replacement component. -/
theorem component_eq_binary_overcomponent
    (d : CentralizerData T D s)
    (e : (componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃* W)
    {K M I : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)))
    (hJM : componentJoin T L (d.first * d.second) ≤ M)
    (hI : I ∈ Chapter1.cComponentsIn M) (hKI : K ≤ I)
    (hq : IsQuasisimple (I ⧸ pCore 2 I))
    {n : ℕ} (hmodel : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (2 ^ n)) : K = I := by
  have hlocal := (component_of_wreath (T := T) le_sup_right d.join_core_ne_bot e hK).1
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hJM
  have hKM : K ≤ M := hK.1.trans hJM
  let S := T.subtype hTM
  have hlocalM : K.subgroupOf M ∈ ChapterA.Section03.localCComponents (S : Subgroup M) :=
    ChapterA.Section03.SourceEmbeddings.local_restrict hlocal.1 hKM
  let a := subgroupOfEquivOfLe hI.1
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsQuasisimple (I ⧸ pCore 2 I) := hq
  let : IsQuasisimple ((I.subgroupOf M) ⧸ pCore 2 (I.subgroupOf M)) :=
    IsQuasisimple.of_mulEquiv b.symm
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let eSL := eI.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let f := eSL.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 I)).comp a.toMonoidHom)
  have hf : Function.Surjective f := eSL.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp a.surjective)
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_rankOne_cover S hlocalM hI.2
    (comap_mono hKI) f hf
  have hh := congrArg (map M.subtype) he
  simpa only [map_subgroupOf_eq_of_le hKM,map_subgroupOf_eq_of_le hI.1] using hh

/-- Consumer of the literal overcomponent: its normal-closure orbit equals
K_z, after the source alternatives have supplied this containing component. -/
theorem span_eq_of_containing_binary_component
    (d : CentralizerData T D s)
    (e : (componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃* W)
    (horbit : ∀ K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)),
      componentOrbit K (T : Subgroup G) = componentSpan T L (d.first * d.second))
    {K M I : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)))
    (hJM : componentJoin T L (d.first * d.second) ≤ M)
    (hI : I ∈ Chapter1.cComponentsIn M) (hKI : K ≤ I)
    (hq : IsQuasisimple (I ⧸ pCore 2 I))
    {n : ℕ} (hmodel : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (2 ^ n))
    (hgen : conjugateSpanBy (centralizerSeed T L (d.first * d.second)) M =
      componentOrbit I (T : Subgroup G)) :
    conjugateSpanBy (centralizerSeed T L (d.first * d.second)) M =
      componentSpan T L (d.first * d.second) := by
  rw [hgen, ←component_eq_binary_overcomponent d e hK hJM hI hKI hq hmodel]
  exact horbit K hK

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
