module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Preparation
public import Theory.GroupTheory.CComponent.SylowOrbit
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The actual component-orbit reduction in the terminal sieve

Odd-prime rank at most two and the equality of the solvable radical with
the two-core make the Sylow orbit of each relative C-component normal in H.
It is perfect and nontrivial. Applying original 14.6.1(4) therefore places
its join with T in H(T,M), and shows that the component itself escapes M.
The final lemma identifies T intersect K as an actual Sylow of K, without
assuming that T normalizes K.

Source: Aschbacher--Smith 14.6.19--20, printed p.1037. Only original 14.6.18
remains explicit, owned by qt-e-14625-source. The quotient-model sieve and
natural-module recognition remain with qt-e-suitable-component-supports.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- The literal T-orbit of a relative component is normal in the original H. -/
theorem source_component_orbit_normal
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    H ≤ normalizer (conjugateSpanBy K (T : Subgroup G) : Set G) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.2
  have hr := (Chapter3.sqtk_of_mem_H hG hH.1.1).stronglyQuasithin
  let D := conjugateSpanBy (K.subgroupOf H) (T.subtype hTH : Subgroup H)
  let : D.Normal := hK.sylow_orbit_normal_of_radical_eq_core
    (source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv H hH)
    hr (T.subtype hTH)
  have he : D.map H.subtype = conjugateSpanBy K (T : Subgroup G) := by
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hKH, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH]
  have hn := D.le_normalizer_map H.subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, he] using hn

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- The source reduction H₀=⟨K^T⟩T remains in H(T,M), including an exchanged component. -/
theorem source_component_orbit_outside
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) ∈
      Chapter1.HOutside G (T : Set G) (M : Set G) := by
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  let X := conjugateSpanBy K (T : Subgroup G)
  let : Group.IsPerfect X := conjugateSpanBy_isPerfect K (T : Subgroup G)
  have hp : IsPPerfect 2 X := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent (X ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (X ⧸ N) inferInstance
  have hne : X ≠ ⊥ := by
    intro he
    have hkb : K = ⊥ := le_bot_iff.mp ((le_conjugateSpanBy K _).trans he.le)
    exact hK.ne_bot (by rw [hkb]; simp)
  exact source_lemma_14_6_1_4 hG T hempty hM hunique hmany hcard e hab H hH X
    (conjugateSpanBy_le hKH (hH.1.2.trans H.le_normalizer))
    (source_component_orbit_normal hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK)
    hp hne

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- No original relative component is contained in M; relative normality is unnecessary. -/
theorem source_component_not_le
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) : ¬ K ≤ M := by
  intro hKM
  exact (source_component_orbit_outside hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK).2
    (sup_le (conjugateSpanBy_le hKM (hM.1.2.trans M.le_normalizer)) hM.1.2)

/-- Intersecting the original T with a relative component gives its actual Sylow subgroup. -/
theorem source_component_sylow (T : Sylow 2 G) (H K : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    ∃ P : Sylow 2 K, (P : Subgroup K) = (T : Subgroup G).subgroupOf K := by
  obtain ⟨P,hP⟩ := (T.subtype hTH).exists_subgroupOf_eq_of_subnormal _ hK.subnormal
  let a := subgroupOfEquivOfLe hKH
  refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
  change (P : Subgroup (K.subgroupOf H)).map a.toMonoidHom = _
  rw [hP]
  ext k
  constructor
  · rintro ⟨l,hl,rfl⟩
    exact hl
  · intro hk
    exact ⟨⟨⟨k,hKH k.property⟩,k.property⟩,hk,rfl⟩
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
