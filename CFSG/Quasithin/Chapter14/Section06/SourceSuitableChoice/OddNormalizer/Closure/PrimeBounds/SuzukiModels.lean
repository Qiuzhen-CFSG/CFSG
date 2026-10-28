module
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.ComponentSolvableBorelExtension
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki

/-!
# Concrete Suzuki Borels in solvable overgroups

The normalizer of any Sylow two-subgroup in Sz(2^(2m+1)) is a conjugate
of the root--torus Borel. Its order is divisible by 2^(2m+1)-1.
Solvable Sylow control and the component Borel extension theorem construct
an actual solvable overgroup of H with this divisor, whether H stabilizes
or exchanges the component. All model comparisons are group isomorphisms.

Source: Aschbacher--Smith, proof of 14.6.14, printed pp.1032--1033;
Huppert--Blackburn III, XI.3, for the concrete Suzuki subgroup facts.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- The odd defining torus divides the order of every Suzuki Sylow normalizer. -/
theorem suzuki_sylow_normalizer_torus_dvd {m : ℕ} (hm : 0 < m)
    (P : Sylow 2 (SuzukiMatrixGroup m)) :
    2 ^ (2 * m + 1) - 1 ∣ Nat.card (normalizer (P : Set (SuzukiMatrixGroup m))) := by
  obtain ⟨g,hg⟩ := ChapterF.Source.suzuki_sylow_normalizer_eq_conjugate_borel m P
  rw [hg,card_map_of_injective (MulAut.conj g).injective]
  rw [← suzukiSplitTorus_card m hm]
  exact card_dvd_of_le (by rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_right)

/-- A genuine Suzuki component produces a solvable overgroup with the forbidden torus divisor. -/
theorem suzuki_component_solvable_extension
    (T : Sylow 2 G) (H L : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hH : Group.IsSolvable H) (hL : L.IsCComponent)
    {m : ℕ} (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) :
    ∃ J : Subgroup G, H ≤ J ∧ Group.IsSolvable J ∧
      2 ^ (2 * m + 1) - 1 ∣ Nat.card J := by
  let : Fact (0 < m) := ⟨hm⟩
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e.symm
  have hc : SolvableSylowControl 2 L := SolvableSylowControl.of_equiv e
    (SolvableSylowControl.of_proper_overgroups
      (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm)
      (fun P A hPA hA => (ChapterF.Source.suzuki_rankOneSylowFacts m P).unique_maximal A hPA hA))
  have he (P : Sylow 2 L) : (normalizer (P : Set L)).map e.toMonoidHom =
      normalizer (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set (SuzukiMatrixGroup m)) :=
    by
    exact map_normalizer_eq_of_bijective (P : Subgroup L) e.bijective
  have hs (P : Sylow 2 L) : Group.IsSolvable (normalizer (P : Set L)) := by
    let := (ChapterF.Source.suzuki_rankOneSylowFacts m (P.mapSurjective (f := e.toMonoidHom) e.surjective)).solvable
    let f := (normalizer (P : Set L)).equivMapOfInjective e.toMonoidHom e.injective
    let : Group.IsSolvable ((normalizer (P : Set L)).map e.toMonoidHom) := he P ▸ inferInstance
    exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  obtain ⟨P,_,hsP⟩ := (show IsComponent G L from ⟨hL.subnormal,inferInstance⟩).solvable_borel_extension
    T H L hTH hH hc hs
  let B := (normalizer (P : Set L)).map L.subtype
  refine ⟨B ⊔ H,le_sup_right,hsP,?_⟩
  have hd : 2 ^ (2 * m + 1) - 1 ∣ Nat.card B := by
    rw [card_map_of_injective L.subtype_injective,
      ← card_map_of_injective (K := normalizer (P : Set L)) (f := e.toMonoidHom) e.injective, he P]
    exact suzuki_sylow_normalizer_torus_dvd hm _
  exact hd.trans (card_dvd_of_le (show B ≤ B ⊔ H from le_sup_left))
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
