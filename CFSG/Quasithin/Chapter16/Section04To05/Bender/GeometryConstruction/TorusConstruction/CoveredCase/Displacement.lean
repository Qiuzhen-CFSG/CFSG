module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.CoveredCase.Intrinsic
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.Consequences
/-!
# Displacements of the whole Sylow subgroup

The factorization T = T_L T_C gives [T,Ω₁(T_L)] ≤ Z(L). Source 16.4.11
makes R centralize T_C. Since U ≤ V, the commutator [R,U] lies in both
Z(L) and R; faithfulness forces it to be trivial. Conjugating R = T_C^g
back proves [T_C,Ω₁(T_C)] = 1. Thus every displacement of T on V lies
in the actual component center, without any ambient normality of R.

Source: Aschbacher–Smith, 16.4.11 and 16.5.1, printed pp.1193–1194;
16.4.2(1),(4), p.1183. This argument does not enter the proof of 16.4.10.
-/

@[expose] public section

open Subgroup
open scoped Pointwise commutatorElement
open CFSG.Quasithin.Chapter16 CFSG.Quasithin.Chapter16.CoverAndSylowElimination
open CFSG.Quasithin.Chapter16.Intersections CFSG.Quasithin.Chapter16.Intersections.Bender
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {z : G}

omit [Finite G] in
theorem factor_space {v : G} (hv : v ∈ benderSpace T L) :
    ∃ w ∈ omegaOneAmbient (commutingSylow T L), ∃ a ∈ sylowOmega T L, v = w*a := by
  have hc : omegaOneAmbient (commutingSylow T L) ≤ centralizer (sylowOmega T L : Set G) :=
    ((omegaOneAmbient_le _).trans inf_le_right).trans (centralizer_le (sylowOmega_le.trans inf_le_right))
  have hp : v ∈ (omegaOneAmbient (commutingSylow T L) : Set G) * (sylowOmega T L : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ (hc.trans (centralizer_le_normalizer _))]
    exact hv
  obtain ⟨w,hw,a,ha,he⟩ := hp
  exact ⟨w,hw,a,ha,he.symm⟩

omit [Finite G] in
theorem center_le_centralizer : componentCenter L ≤ centralizer (L : Set G) := by
  rintro x ⟨x,hx,rfl⟩ y hy
  exact congrArg L.subtype (mem_center_iff.mp hx ⟨y,hy⟩)

theorem sylow_component_displacement (h : StandardSetup T z L) (d : SuzukiCoverInput T L) :
    ⁅(T : Subgroup G), sylowOmega T L⁆ ≤ componentCenter L := by
  apply commutator_le.mpr
  intro t ht a ha
  obtain ⟨s,hs,hc⟩ := sylow_inner_witness h d ht
  have hca : ⁅s⁻¹*t,a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (hc.2 a (sylowOmega_le ha).2).symm
  have he : ⁅t,a⁆ = ⁅s,a⁆ := by
    conv_lhs => rw [← show s * (s⁻¹*t) = t by group]
    rw [commutatorElement_mul_left_eq_conj_mul, hca, mul_one, mul_inv_cancel, one_mul]
  rw [he]
  exact (component_quotient_facts h d).2.2 (commutator_mem_commutator hs ha)

theorem commuting_centralizes_omega {g : G} {R : Subgroup G}
    (h : IntersectionSetup T z L g R) (d : SuzukiCoverInput T L)
    (hconj : R = (commutingSylow T L).conjBy g)
    (hRC : R ≤ centralizer (commutingSylow T L : Set G))
    (hU : omegaOneAmbient R ≤ benderSpace T L)
    (hfaith : Disjoint R (centralizer (L : Set G))) :
    commutingSylow T L ≤ centralizer (omegaOneAmbient (commutingSylow T L) : Set G) := by
  have hRU : R ≤ centralizer (omegaOneAmbient R : Set G) := by
    intro r hr u hu
    obtain ⟨w,hw,a,ha,rfl⟩ := factor_space (hU hu)
    have hrw : ⁅r,w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (hRC hr w (omegaOneAmbient_le _ hw)).symm
    have hcomm : ⁅r,a⁆ ∈ componentCenter L :=
      sylow_component_displacement h.toStandardSetup d
        (commutator_mem_commutator (h.le_sylow hr) ha)
    have hd : ⁅r,w*a⁆ ∈ componentCenter L := by
      rw [commutatorElement_mul_right_eq_mul_conj, hrw, one_mul]
      have hwc := (omegaOneAmbient_le _ hw).2 _ (componentCenter_le hcomm)
      rw [← hwc, mul_inv_cancel_right]
      exact hcomm
    have hdR : ⁅r,w*a⁆ ∈ R := by
      exact R.mul_mem (R.mul_mem (R.mul_mem hr (omegaOneAmbient_le _ hu)) (R.inv_mem hr))
        (R.inv_mem (omegaOneAmbient_le _ hu))
    have hone := disjoint_def.mp hfaith hdR (center_le_centralizer hd)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  intro c hc w hw
  have hcg : (MulAut.conj g) c ∈ R := hconj ▸ mem_map_of_mem _ hc
  have hwg : (MulAut.conj g) w ∈ omegaOneAmbient R := by
    rw [omega_conjugate hconj]
    exact mem_map_of_mem _ hw
  exact (MulAut.conj g).injective (by simpa only [map_mul] using hRU hcg _ hwg)

theorem whole_sylow_displacement {g : G} {R : Subgroup G}
    (h : IntersectionSetup T z L g R) (d : SuzukiCoverInput T L)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓ normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hU : omegaOneAmbient R ≤ benderSpace T L)
    (hfaith : Disjoint R (centralizer (L : Set G))) :
    ∀ t ∈ (T : Subgroup G), ∀ v ∈ benderSpace T L, t*v*t⁻¹*v⁻¹ ∈ componentCenter L := by
  obtain ⟨hC,_,_,hconj⟩ := SylowSymmetry.centralizing_and_transport h hR e htransport
  have hRC : R ≤ centralizer (commutingSylow T L : Set G) :=
    le_centralizer_iff.mp (show commutingSylow T L ≤ centralizer (R : Set G) from hC ▸ inf_le_right)
  have hCW := commuting_centralizes_omega h d hconj hRC hU hfaith
  have hTW : (T : Subgroup G) ≤ centralizer (omegaOneAmbient (commutingSylow T L) : Set G) := by
    rw [sylow_eq_sup h.toStandardSetup d]
    apply sup_le ?_ hCW
    exact le_centralizer_iff.mp (((omegaOneAmbient_le _).trans inf_le_right).trans
      (centralizer_le inf_le_right))
  intro t ht v hv
  obtain ⟨w,hw,a,ha,rfl⟩ := factor_space hv
  change ⁅t,w*a⁆ ∈ componentCenter L
  have htw : ⁅t,w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hTW ht w hw).symm
  have hd := sylow_component_displacement h.toStandardSetup d (commutator_mem_commutator ht ha)
  rw [commutatorElement_mul_right_eq_mul_conj, htw, one_mul,
    ← (omegaOneAmbient_le _ hw).2 _ (componentCenter_le hd), mul_inv_cancel_right]
  exact hd

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
