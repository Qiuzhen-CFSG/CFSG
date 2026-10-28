module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.SmallField.Unitary
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.Nonunitary

/-!
# Excluding the smallest paired-field residual

Move the distinguished inverter t into M, retaining the actual conjugation
of the whole configuration. The final circle is nonsolvable at this base.
Its linear and Suzuki models cannot contain the noncyclic odd residual,
so it is unitary. The conjugated marked u still has circle PSL₂(4) and fixes
t. The fixed-Omega argument therefore forces PSU₃(4). Its cyclic Sylow
three-subgroups contradict the original noncyclic three-subgroup.

Source: GLS IV, Chapter 2, Proposition 16.5, terminal case r=2. No assertion
places the original z in C_G(tuv), and no extra model or field-bound premise
is used in the source consumer.
-/

noncomputable section
namespace BenderSuzuki.ZD.Source16SmallField
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The terminal residual is impossible when the original paired circle
of u is PSL₂(4). The marked u-action may be inner or outer. -/
public theorem false_of_small_paired_circle
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {t u w : G}
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hw : PFAppendixIII.IsInvolution w) (htw : Commute t w)
    (htu : Commute t u) (huw : Commute u w)
    (eu : localCircle Z (centralizer ({u} : Set G)) ≃* PSL2BinaryMatrixGroup 2)
    (R : Subgroup G) (hRp : IsPGroup 3 R)
    (hRD : R ≤ residualPairStabilizer M t) (hRw : R ≤ centralizer ({w} : Set G))
    (htR : t ∈ normalizer R) (hrep : ⁅R,zpowers t⁆ = R) (hnon : ¬ IsCyclic R) : False := by
  have hodd : Odd (Nat.card R) := by
    obtain ⟨k,hk⟩ := hRp.exists_card_eq
    rw [hk]
    exact (by decide : Odd (3 : ℕ)).pow
  obtain ⟨g,hgt,hgw,hcross,hns,n,hn,hperfect,hcenter,hmodel⟩ :=
    source16_final_circle_conjugate_recognition h r ha ht htM hu huD hw htw
      R hodd hRD hRw htR hrep hnon
  let e := MulAut.conj g
  let B := centralizer ({e w} : Set G)
  let C := localCircle Z B
  have hwt : PFAppendixIII.IsInvolution (e w) :=
    IsInvolution.map_of_injective hw e.toMonoidHom e.injective
  have hB : B ≠ ⊤ := r.involution_centralizer_ne_top h.disconnected hwt
  have het : e t ∈ Z := h.disconnected.invariant g t ht
  have htw' : Commute (e t) (e w) := htw.map e.toMonoidHom
  have htB : e t ∈ B := mem_centralizer_singleton_iff.mpr htw'.eq
  have hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M := ⟨e t,het,htB,hgt⟩
  have huB : e u ∈ B := mem_centralizer_singleton_iff.mpr (huw.map e.toMonoidHom).eq
  obtain ⟨ec⟩ := Source16OddResidual.circle_equiv_of_isConj h.disconnected
    (show IsConj w (e w) from isConj_iff.mpr ⟨g,rfl⟩)
  obtain ⟨ecu⟩ := Source16OddResidual.circle_equiv_of_isConj h.disconnected
    (show IsConj u (e u) from isConj_iff.mpr ⟨g,rfl⟩)
  let B₀ := centralizer ({w} : Set G)
  let ec₀ : localCircle Z B₀ ≃* localCircleIn Z B₀ :=
    (localCircle Z B₀).equivMapOfInjective B₀.subtype B₀.subtype_injective
  have hRL : R ≤ localCircleIn Z B₀ :=
    Source16OddResidual.full_commutator_le_circle h.disconnected R ht htw hRw hrep
  let f := ec.toMonoidHom.comp (ec₀.symm.toMonoidHom.comp (inclusion hRL))
  have hf : Function.Injective f := ec.injective.comp
    (ec₀.symm.injective.comp (inclusion_injective hRL))
  obtain ⟨E,hE,hEf,J,hJ,hcard,hfixed,hunitary⟩ :=
    oddCentralCover_unitary_of_noncyclic_pSubgroup hn (by decide : 3 ≠ 2) hRp hnon f hf
      hperfect hcenter hmodel
  let : Field E := hE
  let : Finite E := hEf
  obtain ⟨hn2,⟨ep⟩⟩ := unitary_degree_two_of_small_actor_circle_models h.disconnected r B hB
    hcross hne ⟨e u,huB⟩
    (by rw [← map_pow,hu.sq_eq_one,map_one]) (ecu.symm.trans eu)
    het htB (htu.map e.toMonoidHom) J hn hJ hcard hfixed hunitary
  subst n
  let Q := R.map e.toMonoidHom
  have hQC : Q ≤ centralizer ({e w} : Set G) := by
    rintro x ⟨y,hy,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      ((show Commute y w from mem_centralizer_singleton_iff.mp (hRw hy)).map
        e.toMonoidHom).eq
  have hQrep : ⁅Q,zpowers (e t)⁆ = Q := by
    change ⁅R.map e.toMonoidHom,zpowers (e.toMonoidHom t)⁆ = R.map e.toMonoidHom
    rw [← MonoidHom.map_zpowers,← map_commutator,hrep]
  have hQL : Q ≤ localCircleIn Z B :=
    Source16OddResidual.full_commutator_le_circle h.disconnected Q het htw' hQC hQrep
  have hcyc : IsCyclic Q := three_subgroup_cyclic_in_projective_four_circle B Q hQL
    (hRp.map e.toMonoidHom) J (by norm_num at hcard ⊢; exact hcard)
    (by norm_num at hfixed ⊢; exact hfixed) ep
  let := hcyc
  let er : R ≃* Q := R.equivMapOfInjective e.toMonoidHom e.injective
  exact hnon (isCyclic_of_injective er.toMonoidHom er.injective)

end BenderSuzuki.ZD.Source16SmallField
