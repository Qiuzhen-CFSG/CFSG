module
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosure
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import Theory.SpecificGroups.Alternating.FiveMovedCentralQuotient
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
/-!
# The original A₅ moved factor in a central quotient

The full module normalizes L in the nonnormal pair configuration. Its moved
factor lies in L and is elementary abelian. Conjugation places this same
factor inside the selected overcomponent K. The A₅ action survives the
central two-core of quasisimple K, forcing two-rank at least four in K/O₂(K).
No chosen representation or later point-centralizer control is used.

Source: Aschbacher–Smith, proof of 10.2.6, printed pp.748–749.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
private theorem uniq : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- Every quasisimple overgroup of the original conjugate has large two-core quotient rank. -/
theorem source_a5_quasisimple_overgroup_quotient_twoRank
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} {K : Subgroup G} [IsQuasisimple K]
    (hBK : L.map (MulAut.conj t).toMonoidHom ≤ K) :
    4 ≤ primeRank 2 (K ⧸ pCore 2 K) := by
  let c := (MulAut.conj t).toMonoidHom
  let U₀ := ⁅D.fullModule,L⁆
  let U := U₀.map c
  let B := L.map c
  let A := B.subgroupOf K
  let E := U.subgroupOf K
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hU₀V : U₀ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp hLV
  have hU₀L : U₀ ≤ L := le_normalizer_iff_commutator_le_right.mp
    (D.fullModule_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hUB : U ≤ B := map_mono hU₀L
  have hUK : U ≤ K := hUB.trans hBK
  let := D.fullModule_elementary (uniq D)
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.of_injective
    (inclusion hU₀V) (inclusion_injective hU₀V)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map c
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hUK
  let j : A ≃* L := (subgroupOfEquivOfLe hBK).trans
    (L.equivMapOfInjective c (MulAut.conj t).injective).symm
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := j.symm.toMonoidHom) j.symm.surjective
  have hp : IsPPerfect 2 A := D.faithful.1.2.1.of_surjective
    j.symm.toMonoidHom j.symm.surjective
  let eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans e
  have hBU : B ≤ normalizer (U : Set G) :=
    (map_mono (normalizer_commutator_ge_right D.fullModule L)).trans (U₀.le_normalizer_map c)
  have hAE : A ≤ normalizer (E : Set K) := by
    rw [←subgroupOf_normalizer_eq hUK]
    exact comap_mono hBU
  have hne : ⁅E,A⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (map K.subtype) hz
    rw [map_commutator,map_subgroupOf_eq_of_le hUK,map_subgroupOf_eq_of_le hBK,
      Subgroup.map_bot] at hh
    have hzero : ⁅U₀,L⁆ = ⊥ := by
      apply (map_eq_bot_iff_of_injective (f := c) _ (MulAut.conj t).injective).mp
      simpa only [map_commutator] using hh
    exact source_full_moved_ne_bot D
      (commutator_eq_bot_of_iterated_eq_bot D.fullModule L hzero)
  exact alternatingGroup.FiveChiefDegree.four_le_twoRank_central_quotient
    A E (pCore 2 K) hp eA hAE hne (IsQuasisimple.pCore_le_center 2)
end CFSG.Quasithin.Chapter10
