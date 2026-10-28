module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection
public import Theory.GroupTheory.PCoreFrattiniTransport
/-!
# Separate components in the original moved-factor normalizer

Put W = [V,L] and H = N_G(W). A conjugate B of L centralizes W, while L
moves W. The centralizer of W is normal in H. A proper normal subgroup of
a C-component is solvable, so any C-component containing B centralizes W.
Thus its component is distinct from the component containing L.

In H/O₂(H) these distinct components commute. The actual image of B has
A₅ quotient modulo its two-core, so it has odd rank one at both 3 and 5 and
a two-group center. Rank addition in the strongly quasithin quotient bounds
the other component's ranks by one.

Source: Aschbacher–Smith, Lemma 10.2.6, printed pp.748–749.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem a5_center_le_twoCore
    (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 5)) :
    center G ≤ pCore 2 G := by
  intro z hz
  apply (QuotientGroup.eq_one_iff z).mp
  apply e.injective
  rw [e.map_one]
  have hc : e (QuotientGroup.mk' (pCore 2 G) z) ∈ center (alternatingGroup (Fin 5)) := by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨g,hg⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 G))) a
    rw [←hg]
    simpa only [Function.comp_apply,map_mul] using
      congrArg (fun x : G => e (QuotientGroup.mk' (pCore 2 G) x))
        (mem_center_iff.mp hz g)
  rwa [alternatingGroup.center_eq_bot (by simp),mem_bot] at hc

private theorem a5_other_component_rank
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {I J B : Subgroup G} (hI : I.IsCComponent) (hJ : J.IsCComponent)
    (hne : I ≠ J) (hBJ : B ≤ J)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5) : primeRank p I ≤ 1 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let := pCore_isNilpotent (p := 2) (G := G)
  let E := I.map q
  let F := B.map q
  have ho : Odd p := by rcases hp with rfl | rfl <;> decide
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
    refine ⟨?_, hG.isKGroup.quotient _⟩
    intro r hr hor
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r hor _ pCore_isPGroup).trans
      (hG.stronglyQuasithin r hr hor)
  have hcomm : E ≤ centralizer (F : Set (G ⧸ pCore 2 G)) := by
    apply (commutator_eq_bot_iff_le_centralizer.mp
      (ChapterA.Section03.CComponentCommutation.commutator_eq_bot hQ
        (pCore_quotient_pCore_eq_bot 2) (hI.map_quotient _) (hJ.map_quotient _)
        (fun he => hne (hI.eq_of_map_quotient_eq hJ _ he)))).trans
    exact centralizer_le (map_mono hBJ)
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hq.comap_of_injective B.subtype B.subtype_injective
  let eF : (F ⧸ pCore 2 F) ≃* alternatingGroup (Fin 5) :=
    ((q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hk).symm.trans e
  have hz : Nat.Coprime p (Nat.card (center F)) := by
    obtain ⟨n,hn⟩ := ((pCore_isPGroup (p := 2) (G := F)).to_le (a5_center_le_twoCore eF)).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  have hsum := ResidualCentralizerRank.primeRank_add_le_of_center_coprime E F hcomm hz
  have hF : primeRank p F = 1 := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q hq,
      ←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 B) pCore_isPGroup,
      primeRank_congr p e]
    rcases hp with rfl | rfl <;>
      rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 _ (by decide) (by decide)]
  have hE : primeRank p E = primeRank p I :=
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q hq I
  have hbound := hQ.stronglyQuasithin p (Fact.out : p.Prime) ho
  omega

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The components containing the moving original factor and its centralizing
conjugate in N_G([V,L]) are distinct. -/
theorem source_a5_moved_normalizer_components_ne
    {t : G} {I J : Subgroup G}
    (hI : I ∈ cComponentsIn (normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)))
    (hJ : J ∈ cComponentsIn (normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)))
    (hLI : L ≤ I) (hBJ : L.map (MulAut.conj t).toMonoidHom ≤ J)
    (hcross : ⁅⁅D.fullModule,L⁆,L.map (MulAut.conj t).toMonoidHom⁆ = ⊥) : I ≠ J := by
  let W := ⁅D.fullModule,L⁆
  let H := normalizer (W : Set G)
  let A := L.subgroupOf H
  let B := (L.map (MulAut.conj t).toMonoidHom).subgroupOf H
  have hLH : L ≤ H := hLI.trans hI.1
  have hBH : L.map (MulAut.conj t).toMonoidHom ≤ H := hBJ.trans hJ.1
  let j : B ≃* L := (subgroupOfEquivOfLe hBH).trans
    ((MulAut.conj t).subgroupMap L).symm
  have hnB : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact mem_L_not_isSolvable D.maximal.1
      (Group.isSolvable_of_isSolvable_injective (f := j.symm.toMonoidHom) j.symm.injective)
  have hm : ⁅W.subgroupOf H,A⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (map H.subtype) hz
    rw [map_commutator,map_subgroupOf_eq_of_le W.le_normalizer,
      map_subgroupOf_eq_of_le hLH,Subgroup.map_bot] at hh
    exact source_full_moved_ne_bot D ((source_full_moved_eq_commutator D).symm.trans hh)
  have hc : ⁅W.subgroupOf H,B⁆ = ⊥ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le W.le_normalizer,
      map_subgroupOf_eq_of_le hBH,Subgroup.map_bot]
    exact hcross
  have hne : I.subgroupOf H ≠ J.subgroupOf H :=
    hI.2.ne_of_moving_and_centralizing (comap_mono hLI) (comap_mono hBJ) hnB hm hc
  intro he
  exact hne (congrArg (fun K : Subgroup G => K.subgroupOf H) he)

/-- In the original moved-factor normalizer, the component containing L has
rank at most one at both odd primes dividing its A₅ quotient. -/
theorem source_a5_moved_normalizer_component_rank
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hH : IsSQTK KnownSimple.IsKnownSimple (normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)))
    {t : G} {I J : Subgroup G}
    (hI : I ∈ cComponentsIn (normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)))
    (hJ : J ∈ cComponentsIn (normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)))
    (hLI : L ≤ I) (hBJ : L.map (MulAut.conj t).toMonoidHom ≤ J)
    (hcross : ⁅⁅D.fullModule,L⁆,L.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5) : primeRank p I ≤ 1 := by
  let H := normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)
  let B := (L.map (MulAut.conj t).toMonoidHom).subgroupOf H
  have hBH : L.map (MulAut.conj t).toMonoidHom ≤ H := hBJ.trans hJ.1
  let j : B ≃* L := (subgroupOfEquivOfLe hBH).trans
    ((MulAut.conj t).subgroupMap L).symm
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans e
  have hne : I.subgroupOf H ≠ J.subgroupOf H := by
    intro he
    apply source_a5_moved_normalizer_components_ne D hI hJ hLI hBJ hcross
    have hm := congrArg (map H.subtype) he
    rwa [map_subgroupOf_eq_of_le hI.1,map_subgroupOf_eq_of_le hJ.1] at hm
  have hr := a5_other_component_rank hH hI.2 hJ.2 hne (comap_mono hBJ) eB hp
  rwa [primeRank_congr p (subgroupOfEquivOfLe hI.1)] at hr
end CFSG.Quasithin.Chapter10
