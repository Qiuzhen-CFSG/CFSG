module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.CentralizerOrder.Restriction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.SylowFixer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Omega
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.SylowCensus
public import Theory.GroupTheory.CentralizerSylowNormalizerFusion

/-!
# The order-two Sylow subgroup of the circle centralizer

For the actual selected Sylow T of B=C_G(u), set U=C_T(B°). The marked
root theorem gives u as its unique involution. Fusion of u with uz is
realized in N_G(T), because T centralizes both elements. The normal circle
intersection P and the elementary root Omega Q satisfy C_T(P)≤QU by the
concrete pointwise-Sylow automorphism theorem. The fused unique-involution
calculation gives |U|=2. Normal Sylow intersection then proves the same
order for every Sylow subgroup of C_B(B°), through the literal circle map.

Source: GLS IV, Chapter 2, Corollary 16.6(b). The preceding fusion assertion
is retained explicitly in the first theorem and discharged by the source
Sylow census in the final wrapper.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Source 16.6(b), with the preceding actual fusion u~uz explicit. All
normal intersections, model centralizers and the universal Sylow conclusion
are constructed from the original marked configuration. -/
public theorem source16_circle_centralizer_sylow_card_of_fusion
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    (T : Sylow 2 (centralizer ({u} : Set G)))
    (huT : u ∈ (T : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hTz : (T : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ centralizer ({z} : Set G))
    (hfusion : IsConj u (u * z)) :
    ∀ S : Sylow 2 (centralizer
      (localCircle Z (centralizer ({u} : Set G)) : Set (centralizer ({u} : Set G)))),
      Nat.card S = 2 := by
  let B := centralizer ({u} : Set G)
  let C := localCircle Z B
  let L := localCircleIn Z B
  let f := localCircleHom Z B
  let T₁ := (T : Subgroup B).map B.subtype
  have hTB : T₁ ≤ B := map_subtype_le _
  have hBM : ¬ B ≤ M := fun hh => htM (hh (mem_centralizer_singleton_iff.mpr htu.eq))
  have hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M :=
    ⟨z, hz, mem_centralizer_singleton_iff.mpr hzu.eq, hzM⟩
  let : C.Normal := localCircle_normal h.disconnected B hBM hne
  have hns := source16_centralizer_nonsolvable h r ha ht htM hu huD
  obtain ⟨P, hP⟩ := T.exists_subgroupOf_eq_of_normal C
  have hPa : (P : Subgroup C).map f = T₁ ⊓ L := by
    change (P : Subgroup C).map (localCircleHom Z B) = T₁ ⊓ L
    rw [localCircleHom, ← map_map, hP, subgroupOf_map_subtype,
      map_inf _ _ _ B.subtype_injective]
    rfl
  let Q := (omegaOneAmbient (P : Subgroup C)).map f
  obtain ⟨_, _, _, hgeom⟩ := involutionCentralizer_circle_models h r ha hu huD.1 hBM hns
  let : _root_.IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup C)) := (hgeom P).2.1
  let : _root_.IsElementaryAbelian 2 Q := _root_.IsElementaryAbelian.map f
  have hQP : Q ≤ T₁ ⊓ L := by
    rw [← hPa]
    exact map_mono (omegaOneAmbient_le _)
  have hBN : B ≤ normalizer (L : Set G) := by
    intro b hb
    apply le_normalizer_map (H := C) B.subtype
    exact mem_map_of_mem B.subtype (show (⟨b, hb⟩ : B) ∈ normalizer (C : Set B) by
      rw [normalizer_eq_top]; trivial)
  have huL : u ∉ L := by
    intro huL
    let uB : B := ⟨u, mem_centralizer_singleton_iff.mpr rfl⟩
    have huC : uB ∈ C := by
      obtain ⟨v, hv, he⟩ := huL
      exact (show v = uB from Subtype.ext he) ▸ hv
    have hi : PFAppendixIII.IsInvolution (⟨uB, huC⟩ : C) :=
      IsInvolution.subtype (IsInvolution.subtype hu uB.property) huC
    exact (not_mem_Z_of_mem_residualPairStabilizer h.disconnected htM huD)
      (localCircle_involution_mem h.disconnected r B
        (r.involution_centralizer_ne_top h.disconnected hu) hBM hne hi)
  have hzL : z ∈ L := by
    change z ∈ localCircleIn Z B
    rw [localCircleIn_eq_closure]
    exact subset_closure ⟨hz, mem_centralizer_singleton_iff.mpr hzu.eq⟩
  have hTuz : T₁ ≤ centralizer ({u * z} : Set G) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact ((show Commute x u from mem_centralizer_singleton_iff.mp (hTB hx)).mul_right
      (show Commute x z from mem_centralizer_singleton_iff.mp (hTz hx))).eq
  obtain ⟨g, hgT, hgu⟩ := exists_normalizer_conjugator_of_centralizer_sylow u (u*z) T hTuz hfusion
  let a : MulAut T₁ := T₁.normalizerMonoidHom ⟨g, hgT⟩
  let uT : T₁ := ⟨u, huT⟩
  have hau : (a uT : G) = u * z := hgu
  have hmove : a uT ≠ uT := by
    intro he
    have hh : u * z = u * 1 := by
      simpa only [mul_one] using hau.symm.trans (congrArg Subtype.val he)
    exact (h.disconnected.involutions z hz).ne_one (mul_left_cancel hh)
  have hout : (a uT : G) ∉ L := by
    rw [hau]
    intro hh
    apply huL
    have hm := L.mul_mem hh (L.inv_mem hzL)
    simpa only [mul_inv_cancel_right] using hm
  have huC : u ∈ centralizer (L : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (localCircleIn_le Z B hx)
  have hcent : T₁ ⊓ centralizer (T₁ ⊓ L : Subgroup G) ≤ Q ⊔ centralizer (L : Set G) := by
    intro x hx
    apply (sup_le_sup_left (show B ⊓ centralizer (L : Set G) ≤ centralizer (L : Set G)
      from inf_le_right) Q)
    apply source16_circle_sylow_centralizer_le h r ha hu huD.1 hBM hns P
    exact ⟨hTB hx.1, hPa.symm ▸ hx.2⟩
  have hUcard : Nat.card ((centralizer (L : Set G)).subgroupOf T₁) = 2 := by
    apply Section16.NativeSource.centralizer_intersection_card_two T₁ L Q (T.isPGroup'.map B.subtype)
      (hTB.trans hBN) (hQP.trans inf_le_left) (hQP.trans inf_le_right) hcent uT huC
      (by simpa only [uT, Subgroup.orderOf_mk] using orderOf_eq_prime hu.sq_eq_one hu.ne_one)
      ?_ a hmove hout
    intro v hv hv2
    apply Subtype.ext
    have hvi : PFAppendixIII.IsInvolution (v : G) := by
      have he : orderOf (v : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hv2
      exact ⟨(orderOf_eq_prime_iff.mp he).2, (orderOf_eq_prime_iff.mp he).1⟩
    exact source16_unique_involution_circle_centralizer h r ha hg hz hzM ht htM
      hu huD hzu htu hmax hvi (hTB v.property) hv
  let J := centralizer (C : Set B)
  let : J.Normal := inferInstance
  have hJmap : J.map B.subtype = B ⊓ centralizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b.property, ?_⟩
      rintro y ⟨yB, hy, rfl⟩
      exact congrArg Subtype.val (hb yB hy)
    · rintro ⟨hxB, hxC⟩
      refine ⟨⟨x, hxB⟩, ?_, rfl⟩
      intro y hy
      exact Subtype.ext (hxC y (mem_map_of_mem B.subtype hy))
  have hJU : (J.map B.subtype).subgroupOf T₁ = (centralizer (L : Set G)).subgroupOf T₁ := by
    rw [hJmap]
    ext x
    exact and_iff_right (hTB x.property)
  intro S
  exact Section16.NativeSource.sylow_card_eq_of_normal_intersection B J T
    (hJU.symm ▸ hUcard) S

/-- Source 16.6(b) after discharging the fusion premise by the actual
Sylow census. The explicit rank assumption is precisely the preceding
Proposition 16.5, and the remaining data are the selected source configuration. -/
public theorem source16_circle_centralizer_sylow_card_of_pair_rank_one
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    (hrank : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (T : Sylow 2 (centralizer ({u} : Set G)))
    (hTM : (T : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ M)
    (huT : u ∈ (T : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hTz : (T : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ centralizer ({z} : Set G)) :
    ∀ S : Sylow 2 (centralizer
      (localCircle Z (centralizer ({u} : Set G)) : Set (centralizer ({u} : Set G)))),
      Nat.card S = 2 := by
  exact source16_circle_centralizer_sylow_card_of_fusion h r ha hg hz hzM ht htM
    hu huD hzu htu hmax T huT hTz
    (source16_fusion_and_four_of_pair_rank_one h r ha hg hz hzM ht htM hu huD
      hzu htu hmax hrank T hTM huT).1

end BenderSuzuki.ZD
