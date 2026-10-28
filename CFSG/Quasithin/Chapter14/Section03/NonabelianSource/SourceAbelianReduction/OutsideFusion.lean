module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorSupplement
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NormalSylowResidual
public import Theory.GroupTheory.PResidual.HalfSylowSquares
public import Theory.GroupTheory.QuaternionCentralProductCommutingRoots

/-!
# The final obstruction to fusion outside the original RQ

In the literal orthogonal quotient H/Q, the two-residual has odd order.
Its Sylow two-subgroup therefore maps isomorphically to the residual
quotient, where every square lies in the image of RQ. Consequently a
square in H returning to T belongs to RQ.

If t = z^y and z lies in Q^y, the quaternion central supplement of Q
supplies a square root of t commuting with z. That root lies in H=C_G(z),
contradicting t outside RQ. This proves the final Frattini obstruction
by an explicit square root. The two source centralizer arguments producing
z ∈ Q^y remain explicit in the conditional nonfusion assembly below.

Source: Aschbacher--Smith, Quasithin Groups, 14.3.21(2), printed p.998.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs

/-- Every square of H that belongs to T is already in the original RQ. -/
theorem source_square_mem_rq_of_solvable (s : G) (hsH : s ∈ F.H)
    (hsT : s ^ 2 ∈ (T : Subgroup G)) :
    s ^ 2 ∈ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨_,_,hRP,hRN,hRc⟩ := parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hRne : F.terminalDot R ≠ ⊥ := by
    intro hb
    rw [hb,Subgroup.card_bot] at hRc
    omega
  obtain ⟨_,hres,_⟩ :=
    ChapterG.Section09.FittingRecognition.Four.full_orthogonal_normal_sylow_residual
      F.terminalRepresentation hr P (F.terminalDot R) hRP hRN hRne
  have hPc : Nat.card P = 8 := by
    obtain ⟨a,_,_⟩ := hr
    have hc : Nat.card F.TerminalHdot = 72 :=
      (Nat.card_congr (a.trans topEquiv).toEquiv).trans
        ChapterG.Section09.FittingRecognition.Four.card_orthogonalFour
    rw [Sylow.card_eq_multiplicity,hc]
    decide +kernel
  have hi : (F.terminalDot R).relIndex (P : Subgroup F.TerminalHdot) = 2 := by
    have hh := relIndex_mul_card_of_le hRP
    rw [hRc,hPc] at hh
    change (F.terminalDot R).relIndex (P : Subgroup F.TerminalHdot) * 4 = 8 at hh
    omega
  let a : F.H := ⟨s,hsH⟩
  have hpow : (q a)^2 ∈ (P : Subgroup F.TerminalHdot) := by
    rw [← map_pow]
    exact mem_map_of_mem q (show a^2 ∈ (T : Subgroup G).subgroupOf F.H from hsT)
  have hmem := square_mem_half_sylow_of_odd_residual P (F.terminalDot R) hi
    (by rw [hres]; decide) (q a) hpow
  change (q a)^2 ∈ (R.subgroupOf F.H).map q at hmem
  rw [← map_pow] at hmem
  have hm : a^2 ∈ ((R.subgroupOf F.H).map q).comap q := hmem
  rw [comap_map_eq] at hm
  have hk : q.ker = pCore 2 F.H := by
    rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
  rw [hk] at hm
  have hm' := mem_map_of_mem F.H.subtype hm
  rw [Subgroup.map_sup,subgroupOf_map_subtype] at hm'
  exact (show (R ⊓ F.H) ⊔ F.H.pCoreIn 2 ≤ R ⊔ F.H.pCoreIn 2 from
    sup_le_sup inf_le_left le_rfl) hm'

omit hG hempty hM hu hmany hcard e hnot hne hgP hgH hs
  [IsElementaryAbelian 2 (rankTwoSeed T M)] in
private theorem point_normalizer_eq_centralizer
    {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2)
    (z : G) (hz : z ∈ F.Vi 1) (hzne : z ≠ 1) :
    F.H = centralizer ({z} : Set G) := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hz2 : orderOf z = 2 := by
    have hp : (⟨z,hz⟩ : F.Vi 1)^2 = 1 := by
      simpa [hc] using pow_card_eq_one' (x := (⟨z,hz⟩ : F.Vi 1))
    exact orderOf_eq_prime (congrArg Subtype.val hp) hzne
  have he : zpowers z = F.Vi 1 := eq_of_le_of_card_ge (zpowers_le.mpr hz)
    (by rw [Nat.card_zpowers,hz2,hc])
  change normalizer (F.Vi 1 : Set G) = _
  rw [← he]
  exact normalizer_zpowers_eq_centralizer_of_order_two z hz2

/-- The final contradiction from the source claim z ∈ Q^y, without Q=U. -/
theorem source_conjugate_point_not_outside_of_core_return
    (z : G) (hz : z ∈ F.Vi 1) (hzne : z ≠ 1)
    (t : G) (htT : t ∈ (T : Subgroup G))
    (htout : t ∉ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2)
    (y : G) (hy : y⁻¹ * z * y = t)
    (hreturn : z ∈ conjugate (F.H.pCoreIn 2) y) : False := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  have hQ := core_eq_U_sup_centralizer F dg hZ dU
  obtain ⟨a,ha,hay⟩ := hreturn
  let f : G ≃* G := MulAut.conj y⁻¹
  change f a = z at hay
  have hzU : z ∈ F.U := (F.le_seed 1).trans (le_conjugateSpanBy _ _) hz
  let zU : F.U := ⟨z,hzU⟩
  have hzc : zU ∈ center F.U := by
    have hm : z ∈ F.ZU := hZ.symm ▸ hz
    obtain ⟨w,hw,hwz⟩ := hm
    exact (show w = zU from Subtype.ext hwz) ▸ hw
  have hz2 : orderOf zU = 2 := orderOf_eq_prime
    (dU.center_square ⟨zU,hzc⟩ |> congrArg Subtype.val)
    (fun hh => hzne (congrArg Subtype.val hh))
  obtain ⟨x,hx,hx2,hxa⟩ := commuting_square_root_of_quaternion_supplement
    F.U (F.H.pCoreIn 2) dU hQ zU hz2 hzc a ha
  have hxsq : (f x)^2 = t := by
    rw [← map_pow,hx2]
    simpa only [f,MulAut.conj_apply,inv_inv] using hy
  have hxc : f x ∈ centralizer ({z} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    exact hay ▸ (hxa.map f.toMonoidHom).eq
  have hxH : f x ∈ F.H := (point_normalizer_eq_centralizer F z hz hzne).symm ▸ hxc
  apply htout
  rw [← hxsq]
  exact source_square_mem_rq_of_solvable hG T hempty hM hu hmany hcard e hnot
    F hne g hgP hgH hs (f x) hxH (hxsq.symm ▸ htT)

/-- Original outside nonfusion conditional only on its two core-return cases.
Their proofs are separate source obligations; neither is asserted here. -/
theorem source_outside_point_nonfusion_of_core_returns
    (hfixed : FixedSeedCoreReturn F (sourceResidual M Mc))
    (hmoved : MovedSeedCoreReturn F (sourceResidual M Mc)) :
    OutsidePointNonfusion F (sourceResidual M Mc) := by
  intro z hz hzne t ht ht2 htout hconj
  obtain ⟨y,hy⟩ := isConj_iff.mp hconj
  have hy' : (y⁻¹)⁻¹ * z * y⁻¹ = t := by simpa only [inv_inv] using hy
  apply source_conjugate_point_not_outside_of_core_return
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    z hz hzne t ht htout y⁻¹ hy'
  by_cases hfix : t ∈ centralizer (rankTwoSeed T M : Set G)
  · exact hfixed z hz hzne t ht ht2 htout hfix y⁻¹ hy'
  · exact hmoved z hz hzne t ht ht2 htout hfix y⁻¹ hy'

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
