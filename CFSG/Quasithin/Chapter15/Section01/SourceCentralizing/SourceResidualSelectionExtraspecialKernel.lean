module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialResidualImage
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialCoreInvolution
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelLift
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialCoprime
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer

/-!
# The actual full extraspecial action kernel is prime to three at a third local

The original intersection core supplies an involution modulo O₂(M) which
centralizes the action kernel. Its image fixes the extraspecial center,
so a normal three-subgroup above the action is moved by that involution.
The original cubic residual of the third local is independent of the
kernel and centralized by the same involution. The source three-rank
bound then excludes three-torsion from that kernel.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section02 Chapter14.SourcePreliminaries
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- An actual third maximal local forces the original full extraspecial
action kernel to have order prime to three. -/
theorem PreparedChosenModule.extraspecial_third_action_kernel_coprime
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    Nat.Coprime 3 (Nat.card (actionHom M V h.normalized).rangeRestrict.ker) := by
  let := h.elementary
  let D := internalActionImage M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let Q := pCore 2 M
  let q := QuotientGroup.mk' Q
  have hf : Function.Surjective f := (actionHom M V h.normalized).rangeRestrict_surjective
  have hQ : Q ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    change x ∈ (actionHom M V h.normalized).ker
    rw [actionHom_ker]
    have hi := le_centralizer_iff.mp (h.reduced T hM.1.2).le_centralizer_pCore
    intro v hv
    exact congrArg M.subtype (hi hx ⟨v,h.le_selected hv⟩ hv)
  let g : M ⧸ Q →* D := QuotientGroup.lift Q f hQ
  have hg : Function.Surjective g := by
    intro d
    obtain ⟨m,rfl⟩ := hf d
    exact ⟨q m,rfl⟩
  let K := f.ker.map q
  have hgK : g.ker = K := QuotientGroup.ker_lift Q f hQ
  let Y := sourceResidual N Mc
  let X := (Y.subgroupOf M).map q
  obtain ⟨hYM,_,_,_,_,hCY⟩ := h.extraspecial_third_residual
    hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  obtain ⟨hYker,_⟩ := h.extraspecial_third_residual_original_kernel
    hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  have hYQ := h.extraspecial_third_residual_twoCore_le
    hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  have hXcard : Nat.card X = 3 := (h.extraspecial_third_residual_star_image
    hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc).2
  obtain ⟨r,hr,hrt,hrf,hrK⟩ := h.full_intersection_core_involution
    hG T hempty hM hmany hJ hu hfull hN hNM
  have hrX : q r ∈ centralizer (X : Set (M ⧸ Q)) := by
    rintro x ⟨y,hy,rfl⟩
    have hc := commutator_mem_commutator
      (show (r : G) ∈ (M ⊓ N).pCoreIn 2 from hr) (show (y : G) ∈ Y from hy)
    have hcomm := h.extraspecial_third_residual_intersection_core_commutator
      hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc hc
    have hqcomm : q ⁅r,y⁆ = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      obtain ⟨a,ha,he⟩ := hcomm
      have he' : a = ⁅r,y⁆ := Subtype.ext he
      exact he' ▸ ha
    have he : ⁅q r,q y⁆ = 1 := by rw [←map_commutatorElement]; exact hqcomm
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  have hdisj : Disjoint K X := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hxK,y,hy,hyx⟩
    have hxg : g x = 1 := by
      change x ∈ g.ker
      rwa [hgK]
    have hyf : f y = 1 := by change g (q y) = 1; rwa [hyx]
    have hyc : (y : G) ∈ centralizer (V : Set G) := by
      have hh : y ∈ (actionHom M V h.normalized).ker := congrArg Subtype.val hyf
      rwa [actionHom_ker] at hh
    have hyQ : (y : G) ∈ M.pCoreIn 2 := hYQ (hYker.le ⟨hy,hyc⟩)
    have hyone : q y = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      obtain ⟨a,ha,he⟩ := hyQ
      exact (Subtype.ext he : a = y) ▸ ha
    exact mem_bot.mpr (hyx.symm.trans hyone)
  have hKX : K ≤ normalizer (X : Set (M ⧸ Q)) := by
    apply le_normalizer_iff.mpr
    rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩
    have hac : (a : G) ∈ centralizer (V : Set G) := by
      have hh : a ∈ (actionHom M V h.normalized).ker := congrArg Subtype.val ha
      rwa [actionHom_ker] at hh
    have hn := le_normalizer_iff.mp hCY (a : G) ⟨a.property,hac⟩ (b : G) hb
    exact ⟨a*b*a⁻¹,hn,by simp only [map_mul,map_inv]⟩
  have hexcopy := hex
  obtain ⟨_,_,_,hP,hPc,_,_,_⟩ := hexcopy
  let : IsExtraspecial 3 (pResidual 2 D) := hP
  have hcore : pCore 2 D = ⊥ := by
    subst V
    exact source_localAction_twoCore hG T hM
  have hrcenter := h.extraspecial_intersection_core_centralizes_center
    hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc (mem_map_of_mem f hr)
  have hrK' : q r ∈ centralizer (g.ker : Set (M ⧸ Q)) := hgK.symm ▸ hrK
  have hmoved := SourceExtraspecialModel.not_centralizes_threeCore_of_selfCentralizing_extraspecial_image
    g hg (pResidual 2 D) hPc (centralizer_pResidual_le_of_pCore_eq_bot hcore)
    (q r) hrK' hrf hrcenter
  have hcop : Nat.Coprime 3 (Nat.card K) :=
    SourceExtraspecialModel.coprime_kernel_of_normal_cubic_supplement q
      (QuotientGroup.mk'_surjective Q)
      ((hG.twoLocal_sqtk hM.1.1.1).stronglyQuasithin 3 Nat.prime_three (by decide))
      (pCore 3 (M ⧸ Q)) pCore_isPGroup (q r) hrt hmoved K X hXcard hdisj hKX
      (fun k hk t ht => by obtain rfl := Set.mem_singleton_iff.mp ht; exact (hrK k hk).symm)
      (fun x hx t ht => by obtain rfl := Set.mem_singleton_iff.mp ht; exact (hrX x hx).symm)
  let a := q.subgroupMap f.ker
  have hqk : IsPGroup 2 a.ker := by
    rw [show a = q.subgroupMap f.ker from rfl,ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  obtain ⟨k,hk⟩ := hqk.exists_card_eq
  have hcopker : Nat.Coprime 3 (Nat.card a.ker) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hc := a.ker.card_eq_card_quotient_mul_card_subgroup
  have he : Nat.card (f.ker ⧸ a.ker) = Nat.card K :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective a (q.subgroupMap_surjective f.ker)).toEquiv
  rw [he] at hc
  change Nat.Coprime 3 (Nat.card f.ker)
  rw [hc]
  exact hcop.mul_right hcopker

end CFSG.Quasithin.Chapter15.Section01
