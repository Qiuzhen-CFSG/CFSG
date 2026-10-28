module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Contracts
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.OppositeComponent
public import Theory.GroupTheory.TwoOrbitOddPrime.Residual

/-!
# Prime scalar obstruction in the original nonnormal pair

The two components commute modulo their two-cores. If the smaller core
quotient is centerless, the section centralizer inside their orbit fixes
[V,L]. For an odd prime dividing that quotient and prime to its outer
automorphism group, the ambient rank bound puts every element of that
prime order in the orbit. Thus a scalar centralizing the core quotient
cannot move the original module.

This applies to the literal escaping-point configuration of 10.2.9.
The symplectic application must still construct its marked parabolic and
choose a scalar prime satisfying these two arithmetic conditions.
Source: Aschbacher--Smith, 10.1.3 and 10.2.9, printed pp.742,750--751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02 Chapter4
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem sectionCentralizer_self_le_core
    (hz : center (L ⧸ pCore 2 L) = ⊥) :
    L ⊓ sectionCentralizer L ≤ L.pCoreIn 2 := by
  intro x hx
  let xL : L := ⟨x,hx.1⟩
  let q := QuotientGroup.mk' (pCore 2 L)
  have hc : q xL ∈ center (L ⧸ pCore 2 L) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) y
    have hh : ⁅x,(z : G)⁆ ∈ L.pCoreIn 2 :=
      commutator_le.mp ((le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl).2
        x hx.2 z z.property
    have hk : ⁅xL,z⁆ ∈ pCore 2 L := by
      obtain ⟨u,hu,he⟩ := hh
      exact (Subtype.ext he : u = ⁅xL,z⁆) ▸ hu
    have hq : ⁅q xL,q z⁆ = 1 := by
      rw [←map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hk
    exact (commutatorElement_eq_one_iff_mul_comm.mp hq).symm
  rw [hz, mem_bot] at hc
  have hk : xL ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp hc
  exact mem_map_of_mem L.subtype hk

theorem orbit_sectionCentralizer_centralizes_moved
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    localOrbit T L ⊓ sectionCentralizer L ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let B := L.map (MulAut.conj t).toMonoidHom
  have hpair : localOrbit T L = L ⊔ B :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn
  have hBL : B ≤ sectionCentralizer L := by
    apply (le_sectionCentralizer_iff B L).mpr
    constructor
    · exact (le_sup_right.trans hpair.ge).trans (source_nonnormal_orbit_le_normalizer D hn)
    · have hcomm : ⁅L,B⁆ ≤ L.pCoreIn 2 := by
        let H := L ⊔ (T : Subgroup G)
        let A := L.subgroupOf H
        let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
        have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
        have hmapB : (A.map (MulAut.conj tH).toMonoidHom).map H.subtype = B := by
          rw [map_map,show H.subtype.comp (MulAut.conj tH).toMonoidHom =
            (MulAut.conj t).toMonoidHom.comp H.subtype from rfl,←map_map,hmapA]
        have hc : ⁅A,A.map (MulAut.conj tH).toMonoidHom⁆ ≤ pCore 2 H := by
          apply (map_le_map_iff_of_injective H.subtype_injective).mp
          rw [map_commutator,hmapA,hmapB]
          exact source_conjugate_commutator_le_core D.simpleQTKE D.maximal.1 ht htn
        rw [commutator_comm] at hc
        have hc' := (section_kernel_controls_cComponent D.maximal.1.1 hc).2
        have hm := map_mono (f := H.subtype) hc'
        rw [map_commutator,map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
          hmapA,hmapB,commutator_comm] at hm
        exact hm
      rwa [commutator_comm]
  have hBN : B ≤ normalizer (L : Set G) :=
    ((le_sectionCentralizer_iff B L).mp hBL).1
  intro x hx
  have hp : x ∈ (L : Set G) * (B : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left L B hBN,←hpair]
    exact hx.1
  obtain ⟨l,hl,b,hb,rfl⟩ := hp
  have hlC : l ∈ sectionCentralizer L := by
    simpa only [mul_inv_cancel_right] using
      (sectionCentralizer L).mul_mem hx.2 ((sectionCentralizer L).inv_mem (hBL hb))
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  exact (centralizer _).mul_mem
    (centralizer_le hWV (source_component_core_centralizes_fullModule D
      (sectionCentralizer_self_le_core hz ⟨hl,hlC⟩))) (hsep hb)

/-- The source orbit is the prime-to-p residual whenever the simple smaller
quotient has p in its order but its outer automorphism group does not. -/
theorem primeToResidual_eq_orbit
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L))
    (ho : Nat.Coprime p (Nat.card (MulAut.Outer (L ⧸ pCore 2 L)))) :
    (primeToResidual p D.maximalLocal).map D.maximalLocal.subtype = localOrbit T L := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hlocal : IsSQTK KnownSimple.IsKnownSimple M :=
    D.simpleQTKE.twoLocal_sqtk hu.normalizer_maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hlocal.isKGroup.quotient _⟩
    intro r hr hr2
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r hr2 _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin r hr hr2)
  have hnot : ¬ A.Normal := fun ha =>
    hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  obtain ⟨hi,_⟩ := (Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot
  let eA : (A ⧸ pCore 2 A) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM) (pCore_map_iso 2 _)
  let := D.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  let : IsSimpleGroup (A ⧸ pCore 2 A) := eA.isSimpleGroup
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eA.symm
  have hzA : center (A ⧸ pCore 2 A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz'
    have he := (centerCongr eA ⟨z,hz'⟩).property
    change eA z ∈ center (L ⧸ pCore 2 L) at he
    rw [hz,mem_bot] at he
    exact eA.map_eq_one_iff.mp he
  have hdA : p ∣ Nat.card (A ⧸ pCore 2 A) := by
    rwa [Nat.card_congr eA.toEquiv]
  have hoA : Nat.Coprime p (Nat.card (MulAut.Outer (A ⧸ pCore 2 A))) := by
    rwa [Nat.card_congr (MulAut.outerCongr eA).toEquiv]
  have hr := TwoOrbitOddPrime.nonnormal_component_primeToResidual p hp
    D.component_in_maximalLocal hi hzA hdA
    (hlocal.stronglyQuasithin p Fact.out ((Fact.out : p.Prime).odd_of_ne_two hp)) hoA
  rw [hr,map_conjugateSpanBy,map_subgroupOf_eq_of_le hLM]
  have htop : (⊤ : Subgroup M).map M.subtype = M := by
    ext g
    exact ⟨fun ⟨m,_,he⟩ => he ▸ m.property,fun hg => ⟨⟨g,hg⟩,mem_top _,rfl⟩⟩
  rw [htop]
  apply le_antisymm (conjugateSpanBy_le (le_componentOrbit L T) le_rfl)
  change (⨆ t : (T : Subgroup G), L.map (MulAut.conj (t : G)).toMonoidHom) ≤ _
  apply iSup_le
  intro t x hx
  obtain ⟨l,hl,rfl⟩ := hx
  exact subset_closure ⟨t,hTM t.property,l,hl,rfl⟩

/-- The scalar obstruction on the actual moved module, with the prime
conditions that the symplectic torus producer must discharge. -/
theorem prime_scalar_fixes_moved
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L))
    (ho : Nat.Coprime p (Nat.card (MulAut.Outer (L ⧸ pCore 2 L))))
    {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
    {x : G} (hx : orderOf x = p) (hxL : x ∈ sectionCentralizer L) :
    x ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun h => c.t_not_normalizes (h c.t_mem)
  have hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (source_a5_moved_normalizer_opposite_cross D c.t_mem c.t_not_normalizes c.crossed))
  have hxM : x ∈ D.maximalLocal := c.component_normalizer
    (((le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl).1 hxL)
  have hx0 : x ∈ localOrbit T L := by
    rw [←primeToResidual_eq_orbit D hn hz p hp hd ho]
    let xM : D.maximalLocal := ⟨x,hxM⟩
    apply mem_map_of_mem D.maximalLocal.subtype (x := xM)
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    change x ^ (p ^ 1) = 1
    simpa only [pow_one,←hx] using pow_orderOf_eq_one x
  exact orbit_sectionCentralizer_centralizes_moved D hz hn c.t_mem c.t_not_normalizes
    hsep ⟨hx0,hxL⟩

/-- Actual 10.2.9 consumer: a prime torus scalar moving the original W is
impossible. No A₅ marking, module irreducibility or generation bound is used. -/
theorem moving_prime_scalar_impossible
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L))
    (ho : Nat.Coprime p (Nat.card (MulAut.Outer (L ⧸ pCore 2 L))))
    {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
    {x : G} (hx : orderOf x = p) (hxL : x ∈ sectionCentralizer L)
    (hmove : x ∉ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) : False :=
  hmove (prime_scalar_fixes_moved D hz p hp hd ho c hx hxL)

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
