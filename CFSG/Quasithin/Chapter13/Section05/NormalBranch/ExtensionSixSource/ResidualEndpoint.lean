module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.OriginalWeakClosure
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.TransferObstruction
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.IndexNormal

/-!
# The residual endpoint of the original normal A₆ branch

Every two-subgroup of O²(H) lies in the original U_H. The original normal
pair writes H=L₁IT and I=O²(I)V. Hence O²(H) lies in L₁O²(I), whose image
in H/U_H is a three-group: the two factors have cubic residual images.

If a is fused with the original point z, conjugation carries O²(C_G(a))
into O²(H). Thus a two-subgroup X of this residual cannot have Φ(X)=V₂:
its conjugate lies in U_H, whose Frattini subgroup lies in the order-two
point. The original-source wrapper constructs all of 13.5.15 internally.
This is the actual endpoint consumed by the cubic norm construction;
it assumes no centralizer model or completed extension contradiction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition 13.5.16, printed p.922, final Frattini contradiction.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH) (b : Conclusions D M 6 g)

private theorem twoPerfect_three_of_card_dvd_six
    {A : Type*} [Group A] [Finite A] (hp : IsPPerfect 2 A)
    (hc : Nat.card A ∣ 6) : IsPGroup 3 A := by
  let P : Sylow 3 A := Sylow.nonempty.some
  have hd : P.index ∣ 6 := (P : Subgroup A).index_dvd_card.trans hc
  have hn : ¬3 ∣ P.index := P.not_dvd_index
  have hi : P.index = 1 ∨ P.index = 2 := by
    have hb : P.index ≤ 6 := Nat.le_of_dvd (by decide) hd
    interval_cases he : P.index <;> norm_num [he] at *
  have he : (P : Subgroup A) = ⊤ := by
    rcases hi with hi | hi
    · exact index_eq_one.mp hi
    · let hN : (P : Subgroup A).Normal := normal_of_index_eq_two hi
      exact hp P hN (IsPGroup.of_card (n := 1)
        (by simpa only [←index_eq_card,pow_one] using hi))
  exact P.isPGroup'.of_equiv ((MulEquiv.subgroupCongr he).trans topEquiv)

private theorem pair_core_quotient_card (I : Subgroup G) (hIH : I ≤ D.H)
    (hj : Nonempty (Section08.Source.starImage D.H I ≃* Equiv.Perm (Fin 3))) :
    Nat.card (I ⧸ pCore 2 I) = 6 := by
  obtain ⟨j⟩ := hj
  let f := pairProjection I hIH
  let j' := (MulEquiv.subgroupCongr
    (pairProjection_range I hIH)).trans j
  let η := j'.toMonoidHom.comp f.rangeRestrict
  have hη : Function.Surjective η := j'.surjective.comp f.rangeRestrict_surjective
  have hk : η.ker = f.ker := by
    ext x
    change j' (f.rangeRestrict x) = 1 ↔ f x = 1
    rw [j'.map_eq_one_iff]
    exact Subtype.ext_iff
  have htwo : IsPGroup 2 η.ker := by
    rw [hk,pairProjection_ker]
    exact (isPGroup_pCoreIn 2 D.H).comap_subtype
  rw [←ker_eq_twoCore_of_surjective_perm_three η hη htwo,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv,
    Nat.card_eq_fintype_card,Fintype.card_perm]
  decide

include d h e hseed hn hU b
/-- The original U_H contains every two-subgroup of the two-residual of H. -/
theorem two_subgroup_residual_le_core (X : Subgroup G) (hX : IsPGroup 2 X)
    (hXR : X ≤ (pResidual 2 D.H).map D.H.subtype) : X ≤ D.UH := by
  let _ := h.UH_normal
  let _ := hn
  let q := QuotientGroup.mk' (D.UH.subgroupOf D.H)
  have hLH : D.L₁ ≤ D.H := le_sup_left.trans h.local_le
  have kernel (J : Subgroup G) (hJH : J ≤ D.H) (hc : J.pCoreIn 2 = D.UH) :
      (q.comp (inclusion hJH)).ker = pCore 2 J := by
    have he : (q.comp (inclusion hJH)).ker = D.UH.subgroupOf J := by
      ext x
      exact QuotientGroup.eq_one_iff (inclusion hJH x)
    rw [he,←hc]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  let LH := D.L₁.subgroupOf D.H
  let fL := q.comp (inclusion hLH)
  have hAL : IsPGroup 3 (LH.map q) := by
    have hr : fL.range = LH.map q := by
      rw [MonoidHom.range_comp,inclusion_range]
    rw [←hr]
    apply IsPGroup.of_card (n := 1)
    rw [←index_ker,kernel D.L₁ hLH b.five.1,index_eq_card]
    exact SourceStar.original_residual_quotient_card d h e
  obtain ⟨r,hrH,_,hcore,hj,hgen,hIn,hRn,hres⟩ :=
    SourcePairResidualNormal.exists_original_normal_pair d h e hseed hn hU
  let I := D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom
  let R := (pResidual 2 I).map I.subtype
  have hIH : I ≤ D.H := SourcePairNormal.pair_le h hrH
  have hRH : R ≤ D.H := (map_subtype_le _).trans hIH
  let RH := R.subgroupOf D.H
  let fI := q.comp (inclusion hIH)
  have hrange : Nat.card fI.range = 6 := by
    rw [←index_ker,kernel I hIH hcore,index_eq_card]
    exact pair_core_quotient_card I hIH hj
  have hAR : IsPGroup 3 (RH.map q) := by
    have he : RH.map q = (pResidual 2 I).map fI := by
      have hi : (pResidual 2 I).map (inclusion hIH) = RH := by
        apply map_injective D.H.subtype_injective
        rw [map_map,map_subgroupOf_eq_of_le hRH]
        rfl
      rw [←hi,map_map]
    rw [he]
    have hr : (pResidual 2 I).map fI.rangeRestrict = pResidual 2 fI.range :=
      map_pResidual_of_surjective 2 _ fI.rangeRestrict_surjective
    have hh : IsPGroup 3 (pResidual 2 fI.range) :=
      twoPerfect_three_of_card_dvd_six (isPPerfect_pResidual 2)
        (hrange ▸ (pResidual 2 fI.range).card_subgroup_dvd_card)
    have hm := hh.map fI.range.subtype
    rw [←hr,map_map] at hm
    exact hm
  let K := LH ⊔ RH
  let TH := (D.T : Subgroup G).subgroupOf D.H
  have hKn : K.Normal := by
    let _ : LH.Normal := hn
    let _ : RH.Normal := normal_subgroupOf_of_le_normalizer hRn
    exact Subgroup.sup_normal LH RH
  let _ := hKn
  have hKT : K ⊔ TH = ⊤ := by
    apply map_injective D.H.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le hRH,map_subgroupOf_eq_of_le h.T_le_H,
      ←MonoidHom.range_eq_map,range_subtype]
    change D.L₁ ⊔ R ⊔ (D.T : Subgroup G) = D.H
    rw [hgen,hres]
    simp only [sup_assoc,sup_of_le_right h.V_le_T]
    rfl
  have hRK : pResidual 2 D.H ≤ K := sInf_le
    ⟨hKn,isPGroup_quotient_of_sup_eq_top K TH D.T.isPGroup'.comap_subtype hKT⟩
  have hA : IsPGroup 3 (K.map q) := by
    rw [Subgroup.map_sup]
    let _ : (LH.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    exact hAL.to_sup_of_normal_left hAR
  have hXH : X ≤ D.H := hXR.trans (map_subtype_le _)
  have hXRH : X.subgroupOf D.H ≤ pResidual 2 D.H := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hXR hx
    exact (show y = x from Subtype.ext he) ▸ hy
  have hle : (X.subgroupOf D.H).map q ≤ K.map q := map_mono (hXRH.trans hRK)
  have hd := (hX.comap_subtype.map q).disjoint_of_coprime hA (by decide : Nat.Coprime 2 3)
  have hz : (X.subgroupOf D.H).map q = ⊥ :=
    bot_unique ((le_inf le_rfl hle).trans (disjoint_iff_inf_le.mp hd))
  have hker := (Subgroup.map_eq_bot_iff _).mp hz
  rw [QuotientGroup.ker_mk'] at hker
  exact fun x hx => hker (show (⟨x,hXH hx⟩ : D.H) ∈ X.subgroupOf D.H from hx)

/-- A fused centralizer residual cannot contain a two-group with the original
four-plane as its Frattini subgroup. -/
theorem fused_residual_frattini_obstruction {a z : G}
    (hz : z ∈ D.V₁) (hz1 : z ≠ 1) (haz : IsConj a z)
    (X : Subgroup G) (hX : IsPGroup 2 X)
    (hXR : X ≤ (pResidual 2 (centralizer ({a} : Set G))).map
      (centralizer ({a} : Set G)).subtype)
    (hphi : (frattini X).map X.subtype = V₂) : False := by
  obtain ⟨k,hk⟩ := isConj_iff.mp haz
  let f := (MulAut.conj k).toMonoidHom
  have hCH : (centralizer ({a} : Set G)).map f ≤ D.H := by
    rw [←TypeU4.centralizer_eq h b z hz hz1]
    rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg f (mem_centralizer_singleton_iff.mp hx)
    simpa only [map_mul,show f a = z from hk] using he
  have hY : X.map f ≤ D.UH := two_subgroup_residual_le_core d h e hseed hn hU b
    (X.map f) (hX.map f) (by
      have he := map_mono (f := f) hXR
      rw [map_embedded_pResidual] at he
      exact he.trans (embedded_pResidual_mono 2 hCH))
  exact four_frattini_conjugate_obstruction h X V₂ k⁻¹ hphi d.plane_card (by
    simpa only [inv_inv] using hY)

omit b in
/-- The terminal contradiction using only the original source hypotheses
and the actual subgroup constructed by the transfer argument. -/
theorem original_fused_residual_frattini_obstruction {a z : G}
    (hz : z ∈ D.V₁) (hz1 : z ≠ 1) (haz : IsConj a z)
    (X : Subgroup G) (hX : IsPGroup 2 X)
    (hXR : X ≤ (pResidual 2 (centralizer ({a} : Set G))).map
      (centralizer ({a} : Set G)).subtype)
    (hphi : (frattini X).map X.subtype = V₂) : False := by
  obtain ⟨_,_,b⟩ := SourceConclusions.source13_5_15 d h e hseed hn hU
  exact fused_residual_frattini_obstruction d h e hseed hn hU b hz hz1 haz X hX hXR hphi

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
