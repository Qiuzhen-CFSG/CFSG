module

public import BenderSuzuki.ZD.Recognition.Interfaces
public import BenderSuzuki.SE.Borel
public import BenderSuzuki.PFAppendixII.proposition_1

/-!
# The simple model and Borel consequences of Theorem ZD

The invariant involutions generate the simple ambient group. Its odd core
is trivial because it contains an involution, and nonabelian simplicity
makes it perfect. The proved Brauer--Suzuki odd-core/centralizer theorem
excludes the rank-one alternative. The structural alternative then transports
its Bender model and Borel subgroup through the original closure, odd-core
quotient and derived-subgroup equivalences.

Source: GLS, Volume 4, Chapter 2, the model and Borel assertions of Corollary
ZD, immediately after Theorem ZD. The full ZD conclusion remains an explicit
input; this theorem does not supply product-disconnected recognition.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1

/-- The model and Borel assertions of simple Corollary ZD follow from the
full structural conclusion, with the original subgroup M unchanged. -/
public theorem simple_bender_borel_of_conclusion {G : Type*} [Group G] [Finite G] (Z : Set G) (M : Subgroup G)
    (h : IsProductDisconnected Z M) (hsimple : IsSimpleGroup G)
    (hna : ¬ IsMulCommutative G) (hc : Conclusion Z M) :
    IsSimpleBenderGroup G ∧ IsBorelSubgroup M := by
  let L := Subgroup.closure Z
  have hLtop : L = ⊤ := closure_eq_top_of_simple h hsimple
  let eL : L ≃* G := (MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv
  have hsimpleL : IsSimpleGroup L := eL.isSimpleGroup_congr.mpr hsimple
  have hnaL : ¬ IsMulCommutative L := by
    intro hcL
    apply hna
    apply IsMulCommutative.of_comm
    intro x y
    simpa only [map_mul, eL.apply_symm_apply] using
      congrArg eL (isMulCommutative_iff.mp hcL (eL.symm x) (eL.symm y))
  have hperfectL : commutator L = ⊤ :=
    (hsimpleL.eq_bot_or_eq_top_of_normal (commutator L) inferInstance).resolve_left
      (fun hb => hnaL ((commutator_eq_bot_iff L).mp hb))
  obtain ⟨z, hz, _hzM⟩ := h.nonempty
  let zL : L := ⟨z, Subgroup.subset_closure hz⟩
  have hzL : IsInvolution zL := IsInvolution.subtype (h.involutions z hz) _
  let O := pPrimeCore 2 L
  have hObot : O = ⊥ := by
    rcases hsimpleL.eq_bot_or_eq_top_of_normal O inferInstance with hbot | htop
    · exact hbot
    · let zO : O := ⟨zL, htop ▸ Subgroup.mem_top zL⟩
      have hzO : IsInvolution zO := IsInvolution.subtype hzL _
      have ho : orderOf zO = 2 := orderOf_eq_prime hzO.sq_eq_one hzO.ne_one
      have hd : 2 ∣ Nat.card O := ho ▸ orderOf_dvd_natCard zO
      exact ((Nat.prime_two.coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (G := L) (p := 2))) hd).elim
  have hstructure : StructureConclusion Z M := by
    apply hc.resolve_left
    intro hr
    have hcent := PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank hr hzL
    change O ⊔ Subgroup.centralizer ({zL} : Set L) = ⊤ at hcent
    rw [hObot, bot_sup_eq] at hcent
    have hzcent : zL ∈ Subgroup.center L := by
      apply Subgroup.mem_center_iff.mpr
      intro x
      exact Subgroup.mem_centralizer_singleton_iff.mp (hcent ▸ Subgroup.mem_top x)
    have hcenter : Subgroup.center L = ⊥ :=
      (hsimpleL.eq_bot_or_eq_top_of_normal (Subgroup.center L) inferInstance).resolve_right
        (fun ht => hnaL (Subgroup.center_eq_top_iff.mp ht))
    exact hzL.ne_one (Subgroup.mem_bot.mp (hcenter ▸ hzcent))
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
  have hperfectQ : commutator Q = ⊤ := by
    have hmap := map_commutator_eq L q
    rw [hperfectL, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective O)] at hmap
    exact hmap.symm
  let X := commutator Q
  let eX : X ≃* Q := (MulEquiv.subgroupCongr hperfectQ).trans Subgroup.topEquiv
  let e : X ≃* G := eX.trans (eCore.trans eL)
  obtain ⟨u, _huM, _hu2, _hgenL, _hgenQ, _hdis, _hcomm, hmodel, _hO, hBorel, _hZ⟩ :=
    hstructure
  let B : Subgroup X := (((M.comap L.subtype ⊓ commutator L).map q).subgroupOf X)
  have hBmap : B.map e.toMonoidHom = M := by
    ext g
    constructor
    · rintro ⟨x, hx, hxg⟩
      change ∃ l, l ∈ M.comap L.subtype ⊓ commutator L ∧ q l = (x : Q) at hx
      obtain ⟨l, hl, hlx⟩ := hx
      have hex : e x = (l : G) := by
        change (eCore (x : Q) : G) = (l : G)
        rw [← hlx, heCore]
      have hlg : (l : G) = g := hex.symm.trans hxg
      exact hlg ▸ hl.1
    · intro hg
      let l : L := ⟨g, hLtop ▸ Subgroup.mem_top g⟩
      let x : X := ⟨q l, by change q l ∈ commutator Q; rw [hperfectQ]; trivial⟩
      refine ⟨x, ?_, ?_⟩
      · exact ⟨l, ⟨hg, hperfectL ▸ Subgroup.mem_top l⟩, rfl⟩
      · change (eCore (q l) : G) = g
        rw [heCore]
  exact ⟨hmodel.map_mulEquiv e, hBmap ▸ hBorel.map_mulEquiv e⟩

end BenderSuzuki.ZD
