module

public import BenderSuzuki.ZD.Recognition.Interfaces
public import BenderSuzuki.SE.Final

/-!
# The simple strongly embedded case of Theorem ZD

In a simple Bender group the distinguished involutions generate the group,
the odd core is trivial, and the derived subgroup is the whole group. Thus
all five structural clauses of ZD hold with `u = 1`; the Borel subgroup is
transported through the actual quotient and derived-subgroup equivalences.
Theorem SE supplies the model and Borel data when strong embedding is known.

Source: GLS, Volume 4, Chapter 2, Theorem ZD and the contradiction between
Corollary 7 and Theorem 9. The reduction from product disconnection to strong
embedding is a separate obligation, not assumed as a source theorem here.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u

/-- The complete ZD structure in the simple Bender case, provided the
original subgroup is a Borel. The direct-product factor is trivial. -/
public theorem structure_of_simple_bender_borel
    {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G)
    (h : IsProductDisconnected Z M) (hmodel : IsSimpleBenderGroup G)
    (hBorel : IsBorelSubgroup M) : StructureConclusion Z M := by
  let L := Subgroup.closure Z
  have hLtop : L = ⊤ := closure_eq_top_of_simple h hmodel.isSimple
  let eL : L ≃* G := (MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv
  have hmodelL : IsSimpleBenderGroup L := hmodel.map_mulEquiv eL.symm
  obtain ⟨n, hn, hnL⟩ := hmodelL.exists_exponent
  have hperfectL : commutator L = ⊤ := hnL.isPerfect hn
  let O := pPrimeCore 2 L
  have hObot : O = ⊥ := by
    rcases hmodelL.isSimple.eq_bot_or_eq_top_of_normal O inferInstance with hbot | htop
    · exact hbot
    · obtain ⟨z, hz, _hzM⟩ := h.nonempty
      let zL : L := ⟨z, Subgroup.subset_closure hz⟩
      have hzL : IsInvolution zL := IsInvolution.subtype (h.involutions z hz) _
      let zO : O := ⟨zL, htop ▸ Subgroup.mem_top zL⟩
      have hzO : IsInvolution zO := IsInvolution.subtype hzL _
      have horder : orderOf zO = 2 := orderOf_eq_prime hzO.sq_eq_one hzO.ne_one
      have hdvd : 2 ∣ Nat.card O := horder ▸ orderOf_dvd_natCard zO
      exact ((Nat.prime_two.coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (G := L) (p := 2))) hdvd).elim
  let Q := L ⧸ O
  let q : L →* Q := QuotientGroup.mk' O
  let eCore : Q ≃* L := (QuotientGroup.quotientMulEquivOfEq hObot).trans
    (QuotientGroup.quotientBot (G := L))
  have heCore : ∀ l : L, eCore (q l) = l := by
    intro l
    change QuotientGroup.quotientBot
      ((QuotientGroup.quotientMulEquivOfEq hObot) (QuotientGroup.mk l)) = l
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hmodelQ : IsSimpleBenderGroup Q := hmodelL.map_mulEquiv eCore.symm
  obtain ⟨k, hk, hkQ⟩ := hmodelQ.exists_exponent
  have hperfectQ : commutator Q = ⊤ := hkQ.isPerfect hk
  let X := commutator Q
  let eX : X ≃* Q := (MulEquiv.subgroupCongr hperfectQ).trans Subgroup.topEquiv
  have hmodelX : IsSimpleBenderGroup X := hmodelQ.map_mulEquiv eX.symm
  let e : X ≃* G := eX.trans (eCore.trans eL)
  have hBX : IsBorelSubgroup (M.map e.symm.toMonoidHom) := hBorel.map_mulEquiv e.symm
  have hBmap : M.map e.symm.toMonoidHom =
      (((M.comap L.subtype ⊓ commutator L).map q).subgroupOf X) := by
    ext x
    constructor
    · rintro ⟨g, hg, heq⟩
      have hex : e x = g := by rw [← heq]; exact e.apply_symm_apply g
      have hval : (eCore (x : Q) : G) = g := hex
      refine ⟨eCore (x : Q), ⟨?_, ?_⟩, ?_⟩
      · change (eCore (x : Q) : G) ∈ M
        rwa [hval]
      · rw [hperfectL]; trivial
      · apply eCore.injective
        exact heCore _
    · rintro ⟨l, hl, hlx⟩
      refine ⟨(l : G), hl.1, ?_⟩
      apply e.injective
      change e (e.symm (l : G)) = e x
      rw [e.apply_symm_apply]
      change (l : G) = (eCore (x : Q) : G)
      change q l = (x : Q) at hlx
      rw [← hlx, heCore]
  change ∃ u : L, _
  refine ⟨1, M.one_mem, one_pow 2, ?_, ?_, ?_, ?_, hmodelX, ?_, ?_, ?_⟩
  · rw [hperfectL]; exact top_sup_eq _
  · change X ⊔ Subgroup.zpowers (q 1) = ⊤
    rw [map_one, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    exact hperfectQ
  · rw [map_one, Subgroup.zpowers_one_eq_bot]
    exact disjoint_bot_right
  · intro x _ v hv
    have hv1 : v = 1 := by simpa using hv
    rw [hv1]
    exact Commute.one_right x
  · change O ≤ _
    rw [hObot]; exact bot_le
  · rw [← hBmap]; exact hBX
  · intro z hz
    constructor
    · rw [hperfectQ]; trivial
    · intro heq
      have hz1 : z = 1 := by
        change q z = q 1 at heq
        simpa only [heCore] using congrArg eCore heq
      exact (h.involutions z hz).ne_one (congrArg Subtype.val hz1)

/-- Theorem SE discharges all five ZD clauses in a simple ambient group
once strong embedding has been proved. -/
public theorem structure_of_simple_stronglyEmbedded
    {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G)
    (h : IsProductDisconnected Z M) (hsimple : IsSimpleGroup G)
    (hM : IsStronglyEmbedded M) : StructureConclusion Z M := by
  have hcoretop : involutionCore G = ⊤ := hM.involutionCore_eq_top_of_isSimple hsimple
  let e : involutionCore G ≃* G :=
    (MulEquiv.subgroupCongr hcoretop).trans Subgroup.topEquiv
  have hrank := twoRankAtLeastTwo_of_mulEquiv e.symm
    (simpleStronglyEmbeddedRankTwo M hsimple hM)
  have hSE : TheoremSEBenderConclusion M :=
    (theorem_SE M hM).resolve_left (fun hfalse => hfalse hrank)
  have hBorel := (recognition_borel_of_simple_theoremSEBenderConclusion M hM hsimple hSE).2
  exact structure_of_simple_bender_borel Z M h (theorem_SE_simple M hM hsimple) hBorel
end BenderSuzuki.ZD
