module
public import Theory.GroupTheory.PushingUp.BaumannBinary.Commutator
public import Stellmacher.PushingUp.SL2Two
public import Theory.GroupTheory.ResidualCentralLayerSplitting
public import Theory.GroupTheory.PResidual.CentralCore
public import Theory.GroupTheory.PResidual.SymmetricThreeProducts
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProduct

/-!
# The full binary Baumann commutator, including degree one

For the small field, Stellmacher's residual commutator bound implies
Q = V C_Q(O²(G)). The same natural quotient of V has order four, so the
Sylow image modulo C_Q(O²(G)) has order at most eight. This image cannot
be abelian: characteristic-kernel lifting would make the original Sylow
abelian, contradicting the self-centralizing core and the nontrivial
Sylow quotient. It therefore has order eight and is extraspecial. Its
class bound and elementary center lift through the residual-centralized
kernel. This completes the degree-one case and combines it with Niles's
higher-degree reduction. Normal generation by the original Sylow gives
the full [O₂(G),G] bound in the original Sylow-center closure.

Source: DGS85, *Groups and Graphs*, (6.3), printed p.120; Stellmacher,
*Pushing up*, Arch. Math. 46 (1986), Theorems 1–2 (degree one), together
with the elementary small-quotient and characteristic-kernel argument
above. The higher-degree route is documented in `Commutator`. The literal
(6.4–6.5) application, including the natural clause, is
`BaumannApplication.Commutator.source_conclusions`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace Theory.GroupTheory.BaumannBinary
variable {G : Type*} [Group G] [Finite G]

private theorem sl2Two_nested_frattini (P : Sylow 2 G)
    (q : G →* SL(2,ZMod 2)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G) :
    Stellmacher.IsSL2Two ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G)) := by
  let Q := pCore 2 G
  let e : (G ⧸ Q) ≃* SL(2,ZMod 2) := QuotientGroup.liftEquiv Q hq hk.symm
  let T := P.mapSurjective (QuotientGroup.mk'_surjective Q)
  have hT : Nat.card T = 2 := by
    change Nat.card ((P : Subgroup G).map (QuotientGroup.mk' Q)) = 2
    rw [←relIndex_ker,QuotientGroup.ker_mk']
    exact (Matrix.SpecialLinearGroup.sylow_core_relIndex q hq hk P).trans (Nat.card_zmod 2)
  have hcard : Nat.card (G ⧸ Q) = 6 :=
    Stellmacher.SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨e⟩
  have hindex : (T : Subgroup (G ⧸ Q)).index = 3 := by
    have h := (T : Subgroup (G ⧸ Q)).card_mul_index
    rw [hT,hcard] at h
    omega
  have hPhi : frattini (G ⧸ Q) = ⊥ := by
    have hl := frattini_le_coatom (isCoatom_of_index_three (T : Subgroup (G ⧸ Q)) hindex)
    have hle : frattini (G ⧸ Q) ≤ pCore 2 (G ⧸ Q) := le_sSup ⟨inferInstance,T.isPGroup'.to_le hl⟩
    exact bot_unique (hle.trans (pCore_quotient_pCore_eq_bot 2).le)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hPhi).trans QuotientGroup.quotientBot).trans e⟩

private theorem sl2Two_residual_bound (P : Sylow 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,ZMod 2)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G) :
    ⁅pCore 2 G,pResidual 2 G⁆ ≤ centerClosure (P : Subgroup G) := by
  have hh := Stellmacher.PushingUp.sl2Two_localCommutator_le_centerNormalClosureCommutator P
    (fun K hc hn hnL => hn (hP K hc hnL)) (sl2Two_nested_frattini P q hq hk)
  have hres : BenderSuzuki.External.hktPResidual 2 G = pResidual 2 G := by
    apply le_antisymm
    · exact BenderSuzuki.External.hktPResidual_le _ inferInstance (isPGroup_quotient_pResidual 2)
    · exact sInf_le ⟨BenderSuzuki.External.hktPResidual_normal,
        BenderSuzuki.External.hktPResidual_quotient_isPGroup⟩
  rw [Stellmacher.SectionThree.twoResidualAmbient_top_eq_hktPResidual,hres] at hh
  exact hh.trans (commutator_le_left _ _)

private theorem sl2Two_core_split (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,ZMod 2)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G) :
    pCore 2 G = centerClosure (P : Subgroup G) ⊔
      (pCore 2 G ⊓ centralizer (pResidual 2 G : Set G)) := by
  let Q := pCore 2 G
  let V := centerClosure (P : Subgroup G)
  let R := pResidual 2 G
  let U := Q ⊓ R
  have hred := centerClosure_reduced P hc
  have hQR := sl2Two_residual_bound P hP q hq hk
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let f : SL(2,ZMod 2) →* (Unit → Equiv.Perm (Fin 3)) := MonoidHom.pi (fun _ => e.toMonoidHom)
  have hfi : Function.Injective f := fun a b h => e.injective (congrFun h ())
  have hthree := pResidual_threeGroup_of_injective_permThree_product f hfi
  obtain ⟨m,hm⟩ := hthree.exists_card_eq
  have hodd : Odd (Nat.card (R.map q)) := by
    rw [map_pResidual_of_surjective 2 q hq,hm]
    exact (by decide : Odd (3 : ℕ)).pow
  have hUV : U ≤ V := by
    change Q ⊓ R ≤ V
    rw [inf_comm]
    exact pResidual_inf_pCore_le_of_central_mod_map V hred.le_pCore
      (by rw [commutator_comm]; exact hQR) q hk hodd
  have hi : U.relIndex R = Q.relIndex R := by
    change (Q ⊓ R).relIndex R = _
    rw [inf_relIndex_right]
  have hodd' : Odd (Nat.card (R ⧸ U.subgroupOf R)) := by
    change Odd (U.relIndex R)
    rw [hi]
    change Odd ((pCore 2 G).relIndex R)
    rw [←hk,relIndex_ker]
    exact hodd
  exact eq_sup_centralizer_of_no_two_quotient_central_layer_of_isPGroup
    R U Q V ⊥ inf_le_right (pCore_isPGroup.to_le inf_le_left) pCore_isPGroup
    hodd' (isPPerfect_pResidual 2) le_normalizer_of_normal hred.le_pCore bot_le bot_le hQR
    ((commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hUV.trans hred.le_centralizer_pCore))).le)

private theorem sl2Two_sylow_image_card_le_eight (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,ZMod 2)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G) :
    let C := pCore 2 G ⊓ centralizer (pResidual 2 G : Set G)
    Nat.card ((P : Subgroup G).map (QuotientGroup.mk' C)) ≤ 8 := by
  let Q := pCore 2 G
  let V := centerClosure (P : Subgroup G)
  let C := Q ⊓ centralizer (pResidual 2 G : Set G)
  have hQS : Q ≤ (P : Subgroup G) := pCore_isPGroup.le_sylow_of_normal P
  have hred := centerClosure_reduced P hc
  have hsplit := sl2Two_core_split P hc hP q hq hk
  have hindex : (centralizer ((⊤ : Subgroup G) : Set G)).relIndex V = 4 := by
    have h := (centerClosure_supplement_action P hc hP q hq hk (n := 1)
      (by decide) (by simp) ⊤ (top_sup_eq _)).1
    simpa only [V, Nat.card_zmod, show (2:ℕ)^2=4 from rfl] using h
  have hVC : V ⊓ center G ≤ C :=
    le_inf (inf_le_left.trans hred.le_pCore) (inf_le_right.trans (center_le_centralizer _))
  have hiC : C.relIndex V ≤ 4 := by
    have hh := relIndex_le_of_le_left (L := V) hVC index_ne_zero_of_finite
    rw [inf_relIndex_left] at hh
    simp only [coe_top,centralizer_univ] at hindex
    exact hh.trans_eq hindex
  have hiQ : C.relIndex Q ≤ 4 := by
    have he : C.relIndex Q = C.relIndex V := by
      change C.relIndex (pCore 2 G) = C.relIndex V
      rw [hsplit]
      exact relIndex_sup_of_normalizes V C le_normalizer_of_normal
    exact he.trans_le hiC
  have hiP : Q.relIndex (P : Subgroup G) = 2 :=
    (Matrix.SpecialLinearGroup.sylow_core_relIndex q hq hk P).trans (Nat.card_zmod 2)
  have hm := relIndex_mul_relIndex C Q (P : Subgroup G) inf_le_left hQS
  rw [hiP] at hm
  change Nat.card ((P : Subgroup G).map (QuotientGroup.mk' C)) ≤ 8
  rw [←relIndex_ker,QuotientGroup.ker_mk',←hm]
  omega

private theorem commutative_of_twoGroup_card_lt_eight
    {H : Type*} [Group H] [Finite H] (hp : IsPGroup 2 H) (hc : Nat.card H < 8) :
    IsMulCommutative H := by
  obtain ⟨m,hm⟩ := hp.exists_card_eq
  have hb : m ≤ 2 := by
    by_contra hh
    have hh' : 2^3 ≤ 2^m := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  interval_cases m
  · let : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hm).1
    exact ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
  · let : IsCyclic H := isCyclic_of_prime_card (p := 2) hm
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hm

private theorem sl2Two_sylow_bounds (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,ZMod 2)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G) :
    (P : Subgroup G).lowerCentralSeries 2 = ⊥ ∧
      omegaCenterIn (P : Subgroup G) = centerIn (P : Subgroup G) := by
  let C := pCore 2 G ⊓ centralizer (pResidual 2 G : Set G)
  let π := QuotientGroup.mk' C
  let T := (P : Subgroup G).map π
  have hR : pResidual 2 G ≤ centralizer (π.ker : Set G) := by
    rw [QuotientGroup.ker_mk']
    exact le_centralizer_iff.mp inf_le_right
  have hnonP : ¬ IsMulCommutative P := by
    intro hab
    have hPQ : (P : Subgroup G) ≤ pCore 2 G := by
      apply le_trans ?_ hc
      intro x hx y hy
      exact congrArg (fun z : P => (z : G))
        (hab.is_comm.comm ⟨y,pCore_isPGroup.le_sylow_of_normal P hy⟩ ⟨x,hx⟩)
    have hi := Matrix.SpecialLinearGroup.sylow_core_relIndex q hq hk P
    have he : pCore 2 G = (P : Subgroup G) :=
      le_antisymm (pCore_isPGroup.le_sylow_of_normal P) hPQ
    rw [he,relIndex_self,Nat.card_zmod] at hi
    omega
  have hnonT : ¬ IsMulCommutative T := by
    intro hab
    have hh : T.lowerCentralSeries 1 = ⊥ := by
      rw [←top_subtype_lowerCentralSeries,lowerCentralSeries_one_eq_bot_iff.mpr hab,Subgroup.map_bot]
    exact hnonP (lowerCentralSeries_one_eq_bot_iff.mp
      (lowerCentralSeries_eq_bot_of_image P hP π hR 1 hh))
  have hcard : Nat.card T = 8 := by
    have hb := sl2Two_sylow_image_card_le_eight P hc hP q hq hk
    have hh : ¬ Nat.card T < 8 := fun hh =>
      hnonT (commutative_of_twoGroup_card_lt_eight (P.isPGroup'.map π) hh)
    change Nat.card T ≤ 8 at hb
    omega
  let : IsExtraspecial 2 T := IsExtraspecial.of_noncommutative_card_eight hcard hnonT
  have hcomm : commutator T ≤ center T :=
    (IsExtraspecial.quotient_elementary_abelian 2 T).commutator_le_center_of_central_quotient
  have hclassT : T.lowerCentralSeries 2 = ⊥ := by
    rw [←top_subtype_lowerCentralSeries]
    have he : (⊤ : Subgroup T).lowerCentralSeries 2 = ⊥ := by
      change ⁅commutator T, (⊤ : Subgroup T)⁆ = ⊥
      apply commutator_eq_bot_iff_le_centralizer.mpr
      simpa only [coe_top,centralizer_univ] using hcomm
    rw [he,Subgroup.map_bot]
  have hcenterT : omegaCenterIn T = centerIn T := by
    apply le_antisymm
    · intro z hz
      exact ⟨((mem_omegaCenterIn_iff _ _).mp hz).1,((mem_omegaCenterIn_iff _ _).mp hz).2.1⟩
    · intro z hz
      apply (mem_omegaCenterIn_iff _ _).mpr
      refine ⟨hz.1,hz.2,?_⟩
      let a : center T := ⟨⟨z,hz.1⟩,mem_center_iff.mpr
        (fun t => Subtype.ext (hz.2 t t.property))⟩
      have he := pow_card_eq_one' (x := a)
      rw [IsExtraspecial.center_order_p 2 T] at he
      exact congrArg (fun x : center T => ((x : T) : G ⧸ C)) he
  have hclass := lowerCentralSeries_eq_bot_of_image P hP π hR 2 hclassT
  refine ⟨?_,omegaCenterIn_eq_centerIn_of_image P hP π hR hcenterT⟩
  rw [←top_subtype_lowerCentralSeries,hclass,Subgroup.map_bot]

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The original Sylow has class at most two and elementary center at every
positive binary degree, including the small field. -/
theorem sylow_class_two_and_elementary_center_all (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    (P : Subgroup G).lowerCentralSeries 2 = ⊥ ∧
      omegaCenterIn (P : Subgroup G) = centerIn (P : Subgroup G) := by
  by_cases hn1 : n = 1
  · have hF2 : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
    let : Fintype F := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF2)).symm
    let e : SL(2,F) ≃* SL(2,ZMod 2) :=
      { toFun := Matrix.SpecialLinearGroup.map eF.toRingHom
        invFun := Matrix.SpecialLinearGroup.map eF.symm.toRingHom
        left_inv := by intro g; ext i j; exact eF.symm_apply_apply (g i j)
        right_inv := by intro g; ext i j; exact eF.apply_symm_apply (g i j)
        map_mul' := (Matrix.SpecialLinearGroup.map eF.toRingHom).map_mul }
    let q₂ := e.toMonoidHom.comp q
    have hq₂ : Function.Surjective q₂ := e.surjective.comp hq
    have hk₂ : q₂.ker = pCore 2 G :=
      (MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective).trans hk
    exact sl2Two_sylow_bounds P hc hP q₂ hq₂ hk₂
  · exact sylow_class_two_and_elementary_center P hc hP q hq hk (by omega) hF

/-- The full commutator clause of DGS85 (6.3) at every positive binary degree:
the actor is all of G, and V is the original Sylow-center normal closure. -/
theorem core_commutator_le_centerClosure_all (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    ⁅pCore 2 G,(⊤ : Subgroup G)⁆ ≤ centerClosure (P : Subgroup G) := by
  obtain ⟨hclass,hcenter⟩ := sylow_class_two_and_elementary_center_all P hc hP q hq hk hn hF
  have hcomm : ⁅(P : Subgroup G),(P : Subgroup G)⁆ ≤ centerIn (P : Subgroup G) := by
    apply le_inf (commutator_le_self _ )
    apply commutator_eq_bot_iff_le_centralizer.mp
    simpa only [Subgroup.lowerCentralSeries_succ,Subgroup.lowerCentralSeries_zero] using hclass
  have hlocal : ⁅pCore 2 G,(P : Subgroup G)⁆ ≤ centerClosure (P : Subgroup G) :=
    ((commutator_mono (pCore_isPGroup.le_sylow_of_normal P) le_rfl).trans hcomm).trans
      (hcenter ▸ (show omegaCenterIn (P : Subgroup G) ≤ centerClosure (P : Subgroup G) from
        le_normalClosure))
  have hclosed := commutator_normalClosure_le_of_normal (pCore 2 G) (P : Subgroup G)
    (centerClosure (P : Subgroup G)) hlocal
  have htop : normalClosure ((P : Subgroup G) : Set G) = ⊤ := by
    obtain ⟨g,_,hgen,_⟩ := Matrix.SpecialLinearGroup.exists_residual_generating_sylow_pair q hq hk P
    apply top_unique
    rw [←hgen]
    apply sup_le le_normalClosure
    rintro _ ⟨x,hx,rfl⟩
    exact (inferInstance : (normalClosure ((P : Subgroup G) : Set G)).Normal).conj_mem x
      (le_normalClosure hx) g
  rwa [htop] at hclosed

end Theory.GroupTheory.BaumannBinary
