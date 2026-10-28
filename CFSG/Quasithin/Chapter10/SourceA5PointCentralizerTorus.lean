module
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerControl
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerResidual
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
/-!
# Excluding the cubic torus in the original A5 point-centralizer argument

The two original components form the actual orbit L₀. If the opposite
component centralizes W=[V,L], then the section centralizer of L inside
L₀ also centralizes W: its first coordinate lies in O₂(L), since A5 is
centerless. The cubic residual identity L₀=O^{3′}(M) puts every element
of order three in M inside L₀. Hence the cubic torus required by either
rank-two embedding alternative cannot move W.

The separate-factor condition and source10.2.6 normalizer bound remain
explicit, exactly as required by the chosen-module source application.
Source: Aschbacher–Smith10.2.9, printed pp.750–751, using10.1.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem sectionCentralizer_self_le_core
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
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
  have he : e (q xL) ∈ center (alternatingGroup (Fin 5)) :=
    (centerCongr e ⟨_,hc⟩).property
  rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
  have hk : xL ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp
    (e.injective (he.trans e.map_one.symm))
  exact mem_map_of_mem L.subtype hk

theorem source_a5_orbit_sectionCentralizer_centralizes_moved
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
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
      (sectionCentralizer_self_le_core e ⟨hl,hlC⟩))) (hsep hb)
/-- The cubic scalar required by both rank-two embedding branches cannot
occur in the original maximal local group. -/
theorem source_a5_cubic_sectionCentralizer_fixes_moved
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    {x : G} (hxM : x ∈ D.maximalLocal) (hx3 : orderOf x = 3)
    (hxL : x ∈ sectionCentralizer L) :
    x ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hx0 : x ∈ localOrbit T L := by
    rw [←source_nonnormal_cubic_residual D hn hd]
    let xM : D.maximalLocal := ⟨x,hxM⟩
    apply mem_map_of_mem D.maximalLocal.subtype (x := xM)
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    change x ^ (3 ^ 1) = 1
    simpa only [pow_one,←hx3] using pow_orderOf_eq_one x
  exact source_a5_orbit_sectionCentralizer_centralizes_moved D e hn ht htn hsep ⟨hx0,hxL⟩

/-- With source10.2.6 normalizer containment, neither the quasisimple nor
constrained rank-two alternative can supply its required cubic scalar. -/
theorem source_a5_no_moving_cubic_sectionCentralizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) :
    ¬ ∃ x : G, orderOf x = 3 ∧ x ∈ sectionCentralizer L ∧
      x ∉ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  rintro ⟨x,hx3,hxL,hxW⟩
  exact hxW (source_a5_cubic_sectionCentralizer_fixes_moved D e hn ht htn hsep
    (hNL (((le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl).1 hxL)) hx3 hxL)
end CFSG.Quasithin.Chapter10
