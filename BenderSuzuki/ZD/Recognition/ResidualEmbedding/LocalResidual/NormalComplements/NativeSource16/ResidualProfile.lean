module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.MarkedFour
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.Source

/-!
# The actual odd residual forced by two-rank greater than one

The original rank-two assumption supplies the maximal marked four. The two
field circles have the same parameter, so an odd prime dividing its square
root plus one supplies the noncyclic odd residual. The full Frattini argument
places that residual in the distinguished circle of a nondistinguished
involution outside M. Every action, model and cyclic fixed subgroup used in
this construction has been derived from the original source hypotheses.

Source: GLS IV, Chapter 2, Proposition 16.5, up to its terminal cyclicity step.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The original rank-two alternative produces the literal contradictory
odd-residual configuration. Its final cyclicity is the terminal source step. -/
public theorem source16_residual_profile_of_rank_two
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    (hn : ¬ IsStronglyEmbedded M) {t : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hrank : TwoRankAtLeastTwo (residualPairStabilizer M t)) :
    ∃ t₁ w : G, t₁ ∈ Z ∧ t₁ ∉ M ∧
      residualPairStabilizer M t₁ = residualPairStabilizer M t ∧
      PFAppendixIII.IsInvolution w ∧ w ∉ Z ∧ w ∉ M ∧ Commute t₁ w ∧
      ∃ (p : ℕ) (R : Subgroup G), p.Prime ∧ Odd p ∧ IsPGroup p R ∧
        R ≤ residualPairStabilizer M t₁ ∧
        R ≤ localCircleIn Z (centralizer ({w} : Set G)) ∧
        t₁ ∈ normalizer (R : Set G) ∧ ⁅R,zpowers t₁⁆ = R ∧
        ¬ IsCyclic R ∧ Nat.card (R ⧸ frattini R) = p ^ 2 := by
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
  have hr : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega : m ≠ 0) 2
  obtain ⟨p,hp,hpdiv⟩ := Nat.exists_prime_and_dvd (show 2 ^ m + 1 ≠ 1 by omega)
  obtain ⟨hpo,hAcard,P,hAP,hRD,hRp,hrep,hnon,hfrat,hRC,hRL⟩ :=
    Source16OddResidual.residual_profile_from_paired_tori h.disconnected ht₁ ht₁M
      W hW hWD hWt huW hvW hWgen Tu Tv hm hp hpdiv
      hgeomU.1 hgeomV.1 hgeomU.2.1 hgeomV.2.1 inf_le_left inf_le_left
      (inf_le_right.trans (localCircleIn_le Z Bu)) (inf_le_right.trans (localCircleIn_le Z Bv))
      hgeomU.2.2.2 hgeomV.2.2.2 hgeomU.2.2.1 hgeomV.2.2.1
      eu ev au av hau hav hou hov (fun _ => rfl) (fun _ => rfl)
  let A := W ⊔ zpowers t₁
  let P₁ := (P : Subgroup (residualOddCore M t₁)).map (residualOddCore M t₁).subtype
  let R := OddInvolutionFrattini.R P₁ t₁
  let : IsElementaryAbelian 2 A := residualFourActor_elementary (h.disconnected.involutions t₁ ht₁) W hWt
  have htA : t₁ ∈ A := mem_sup_right (mem_zpowers t₁)
  have huA : u ∈ A := mem_sup_left huW
  have hvA : v ∈ A := mem_sup_left hvW
  have hwA : t₁ * u * v ∈ A := A.mul_mem (A.mul_mem htA huA) hvA
  have huvM : u * v ∈ M := M.mul_mem (hWD huW).1 (hWD hvW).1
  have hwM : t₁ * u * v ∉ M := by
    intro hh
    apply ht₁M
    have hprod := M.mul_mem hh (M.inv_mem huvM)
    simpa only [mul_inv_rev,← mul_assoc,mul_inv_cancel_right] using hprod
  have hwi : PFAppendixIII.IsInvolution (t₁ * u * v) :=
    ⟨fun he => hwM (he ▸ M.one_mem),elemPow_eq_one_of_isElementaryAbelian _ hwA⟩
  have htw : Commute t₁ (t₁ * u * v) := Subtype.ext_iff.mp
    (mul_comm (⟨t₁,htA⟩ : A) ⟨t₁*u*v,hwA⟩)
  have huv1 : u * v ≠ 1 := by
    intro he
    apply hvuNe
    calc
      v = u⁻¹ * (u * v) := by group
      _ = u := by rw [he,mul_one,hu.inv_eq_self]
  have huvi : PFAppendixIII.IsInvolution (u * v) :=
    ⟨huv1,elemPow_eq_one_of_isElementaryAbelian _ (W.mul_mem huW hvW)⟩
  have hww : t₁ * (t₁*u*v) = u*v := by
    have ht2 : t₁*t₁=1 := by simpa only [pow_two] using (h.disconnected.involutions t₁ ht₁).sq_eq_one
    rw [← mul_assoc,← mul_assoc,ht2,one_mul]
  have hwZ : t₁*u*v ∉ Z := by
    intro hwZ
    have hC := h.disconnected.product_centralizer t₁ ht₁ (t₁*u*v) hwZ
      (hww.symm ▸ huvi) (hww.symm ▸ huvM)
    apply ht₁M
    apply hC
    rw [hww]
    exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext_iff.mp (mul_comm (⟨t₁,htA⟩ : A) ⟨u*v,A.mul_mem huA hvA⟩))
  have htR : t₁ ∈ normalizer (R : Set G) :=
    OddInvolutionFrattini.normalizes_R P₁ A hAP htA htA
  exact ⟨t₁,t₁*u*v,ht₁,ht₁M,hpair,hwi,hwZ,hwM,htw,p,R,hp,hpo,hRp,hRD,hRL,htR,hrep,hnon,hfrat⟩

end BenderSuzuki.ZD
