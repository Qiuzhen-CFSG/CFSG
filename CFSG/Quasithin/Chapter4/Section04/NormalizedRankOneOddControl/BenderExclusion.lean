module
import all CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.BinaryRankOne
import all CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.BinaryUnitaryExclusion
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ComponentModels
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.Models

/-!
# Excluding the Bender component rows

A perfect group mapping to a characteristic-two Bender model kills its two-core.
For the fixed residual, that would make the nontrivial commutator module central,
which is impossible. Thus the normal-component output for the actual large orbit
has a relative-rank-two quotient. This is the Bender exclusion in the reduction
of Aschbacher--Smith 4.4.12, printed pp.621--623.

The proof-only `import all` declarations reuse the existing perfect-core
calculations for the unitary and Suzuki carriers without changing their modules'
public interfaces. The quotient markings and the original embedded residual
are retained throughout.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open ClassificationModels
variable {G : Type*} [Group G] [Finite G]

private theorem bender_perfect_core_le_ker
    {S F : Type*} [Group S] [Finite S] [Group F] [Group.IsPerfect F]
    (h : IsBenderModel S) (q : F →* S) : pCore 2 F ≤ q.ker := by
  cases h with
  | linear n hn hm =>
    obtain ⟨E,hE,hfinite,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let r := e.trans (Theory.PSL2.sl2QuotientEquiv E).symm
    have hh := Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker (r.toMonoidHom.comp q)
    intro x hx
    apply r.injective
    simpa only [map_one] using (show r (q x) = 1 from hh hx)
  | unitary n hn hm =>
    exact ChapterC.OrdinaryPlacement.BinaryUnitary.perfect_core_le_ker (by omega) hm q
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    have hh := ChapterC.HypothesisC28.suzuki_perfect_core_le_ker (by omega : 0 < m)
      (e.toMonoidHom.comp q)
    intro x hx
    apply e.injective
    simpa only [map_one] using (show e (q x) = 1 from hh hx)

/-- No Bender component can contain the original nontrivial commutator
module in the two-core of its perfect fixed residual. -/
theorem no_bender_of_residual_module
    {N : Type*} [Group N] [Finite N] (K F W : Subgroup N)
    [Group.IsPerfect F] (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2)
    (hW : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hm : IsBenderModel (K ⧸ center K)) : False := by
  let q : F →* K ⧸ center K :=
    (QuotientGroup.mk' (center K)).comp (inclusion hFK)
  have hk := bender_perfect_core_le_ker hm q
  have hcentral : F.pCoreIn 2 ≤ centralizer (F : Set N) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    have hz : inclusion hFK x ∈ center K := (QuotientGroup.eq_one_iff _).mp (hk hx)
    exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hFK hy⟩)
  exact hW (hcomm.trans (commutator_eq_bot_iff_le_centralizer.mpr (hWF.trans hcentral)))

/-- The actual remaining relative-rank-two component, with its original
embedding and simple quotient section. This is an output configuration. -/
@[expose] def RankTwoComponentCase (L V A : Subgroup G) (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧
      (∃ f : ℕ, IsRankTwoModel (K ⧸ center K) f) ∧
      V ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      12 ≤ primeRank 2 (K ⧸ center K) ∧
      ∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f

/-- The literal chosen-module normal-component configuration has only
relative-rank-two characteristic-two quotient models. -/
theorem rankTwo_component_of_normal_case
    {S : Type*} [Group S] {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hr : 12 ≤ primeRank 2 V) (hc : NormalComponentCase L V A S) :
    RankTwoComponentCase L V A S := by
  obtain ⟨K,hK,hn,hout,hcore,hm,hv,hf,hcent,hrK,hsection⟩ := lie_component_of_rank_twelve hc hr
  refine ⟨K,hK,hn,hout,hcore,?_,hv,hf,hcent,hrK,hsection⟩
  rcases hm with hb | hrank
  · exfalso
    let N := normalizer (A : Set G)
    let F := oddActorResidual L A
    let J := K.map N.subtype
    have hi : F ≤ J := hf
    let : Group.IsPerfect F := oddActorResidual_isPerfect L A
    obtain ⟨_,he,hWF,_⟩ := chosen_oddActorResidual_cover h D A hAN hcomm ho hAV
    let e : J ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
    let z : (J ⧸ center J) ≃* (K ⧸ center K) := QuotientGroup.congr _ _ e (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro y hy
        exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
    exact no_bender_of_residual_module J F V hi hWF D.ne_bot he (hb.of_mulEquiv z)
  · exact hrank

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
