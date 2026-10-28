module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.ResidualProfile
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.LargeField
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.SmallField.Source

/-!
# The original pair-rank bound of Proposition 16.5

Assume the two-point stabilizer contains a four-group. Maximal marked
selection and four-centralizer generation give the two actual square-field
circles. For square-root degree one the fixed-omega comparison forces the
terminal unitary circle to be PSU₃(4), whose three-subgroups are cyclic.
For larger degree, the odd-prime or order-nine arguments exclude the same
noncyclic residual. Every model, action, Sylow, order and recognition input
is supplied by the original minimal simple setup and preceding generation.

Source: GLS IV, Chapter 2, Proposition 16.5. The terminal argument uses the
corrected change of distinguished base rather than the printed old-z
containment on page 86.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

public theorem source16_pair_not_twoRank
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    (hn : ¬ IsStronglyEmbedded M) {t : G} (ht : t∈Z) (htM : t∉M) :
    ¬ TwoRankAtLeastTwo (residualPairStabilizer M t) := by
  intro hrank
  classical
  obtain ⟨u,z,t₁,hu,hz,hzM,ht₁,ht₁M,hpair,hmax,W,hWe,hW,hWD,hWz,hWt,huW⟩ :=
    source16_exists_maximal_marked_four h.disconnected r ha hn ht htM hrank
  let := hWe
  have hzu : Commute z u := (mem_centralizer_singleton_iff.mp (hWz huW)).symm
  have htu : Commute t₁ u := (mem_centralizer_singleton_iff.mp (hWt huW)).symm
  obtain ⟨v,hvW,hv,hvuNe,hWgen,hvu,hBu,hneU,hBv,hneV,m,hm,
      ⟨eu⟩,⟨ev⟩,⟨efu⟩,⟨efv⟩,hau,hou,hav,hov,hgeomU,hgeomV⟩ :=
    source16_paired_field_circles h r ha hg hz hzM ht₁ ht₁M hu (hWD huW) hzu htu
      hmax W hW hWD hWz hWt huW
  let Bu := centralizer ({u} : Set G)
  let Bv := centralizer ({v} : Set G)
  let au := source16_circleAction h.disconnected Bu hBu hneU
    ⟨v,mem_centralizer_singleton_iff.mpr hvu.eq⟩
  let av := source16_circleAction h.disconnected Bv hBv hneV
    ⟨u,mem_centralizer_singleton_iff.mpr hvu.symm.eq⟩
  let Tu := residualPairStabilizer M t₁ ⊓ localCircleIn Z Bu
  let Tv := residualPairStabilizer M t₁ ⊓ localCircleIn Z Bv
  by_cases hm1 : m=1
  · subst m
    obtain ⟨_,_,P,hAP,hRD,hRp,hrep,hnon,_,hRC,_⟩ :=
      Source16OddResidual.residual_profile_from_paired_tori h.disconnected ht₁ ht₁M
        W hW hWD hWt huW hvW hWgen Tu Tv (by decide) Nat.prime_three (by norm_num)
        hgeomU.1 hgeomV.1 hgeomU.2.1 hgeomV.2.1 inf_le_left inf_le_left
        (inf_le_right.trans (localCircleIn_le Z Bu)) (inf_le_right.trans (localCircleIn_le Z Bv))
        hgeomU.2.2.2 hgeomV.2.2.2 hgeomU.2.2.1 hgeomV.2.2.1
        eu ev au av hau hav hou hov (fun _ => rfl) (fun _ => rfl)
    let A := W⊔zpowers t₁
    let P₁ := (P : Subgroup (residualOddCore M t₁)).map (residualOddCore M t₁).subtype
    let R := OddInvolutionFrattini.R P₁ t₁
    let := residualFourActor_elementary (h.disconnected.involutions t₁ ht₁) W hWt
    have htA : t₁∈A := mem_sup_right (mem_zpowers t₁)
    have huA : u∈A := mem_sup_left huW
    have hvA : v∈A := mem_sup_left hvW
    have hwA : t₁*u*v∈A := A.mul_mem (A.mul_mem htA huA) hvA
    have hwM : t₁*u*v∉M := by
      intro hh
      have huvM : u*v∈M := M.mul_mem (hWD huW).1 (hWD hvW).1
      have hh' := M.mul_mem hh (M.inv_mem huvM)
      apply ht₁M
      simpa only [mul_inv_rev,←mul_assoc,mul_inv_cancel_right] using hh'
    have hwi : PFAppendixIII.IsInvolution (t₁*u*v) :=
      ⟨fun hh => hwM (hh ▸ M.one_mem),elemPow_eq_one_of_isElementaryAbelian _ hwA⟩
    have htw : Commute t₁ (t₁*u*v) := Subtype.ext_iff.mp
      (mul_comm (⟨t₁,htA⟩:A) ⟨t₁*u*v,hwA⟩)
    have huw : Commute u (t₁*u*v) := Subtype.ext_iff.mp
      (mul_comm (⟨u,huA⟩:A) ⟨t₁*u*v,hwA⟩)
    have htR : t₁∈normalizer R := OddInvolutionFrattini.normalizes_R P₁ A hAP htA htA
    exact Source16SmallField.false_of_small_paired_circle h r ha ht₁ ht₁M hu
      (hWD huW) hwi htw htu huw eu R hRp hRD hRC htR hrep hnon
  · exact Source16OddResidual.paired_tori_false_of_large_field h r ha ht₁ ht₁M
      W hW hWD hWt huW hvW hWgen hu Tu Tv (by omega)
      hgeomU.1 hgeomV.1 hgeomU.2.1 hgeomV.2.1 inf_le_left inf_le_left
      (inf_le_right.trans (localCircleIn_le Z Bu)) (inf_le_right.trans (localCircleIn_le Z Bv))
      hgeomU.2.2.2 hgeomV.2.2.2 hgeomU.2.2.1 hgeomV.2.2.1
      eu ev au av hau hav hou hov (fun _ => rfl) (fun _ => rfl)

end BenderSuzuki.ZD
