module
public import CFSG.Quasithin.ChapterC.Section06.Thompson.AlternatingGeometry
/-!
# Original alternating-five Thompson stability

The source A₅ family has two invariant cores and two further elementary
subgroups. Outside elements of the index-two extension exchange the cores,
while the stabilizer of an extra member in R is Baum(R). The proved marked
four-family geometry and the source index [R:Baum(R)]=2 exclude a maximum
elementary subgroup outside R. Thus the original extension has J(M)=J(R).

Source: Aschbacher–Smith C.6.1, printed p.165, case (beta).
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] [Finite G] {H M K R L : Subgroup G}

omit [Finite G] in
private theorem count (Q A : Subgroup G) :
    Nat.card ↥(Q ⊓ A) * Q.relIndex A = Nat.card A := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ A) A bot_le inf_le_right

theorem alternating_thompson_stable_from_original
    (c : OriginalHypotheses H M K R R) (h : AlternatingPairSetup R K L)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    elementaryAbelianMaxJ M = elementaryAbelianMaxJ R := by
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hH : H = K ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have hphi := h.frattini_eq_bot_of_index_two H M R c.T_le c.R_normal hRK hH hno hi x hx hnc
  have hsrc := alternating_family_from_original c h hi x hx hnc
  have haction := alternating_action_from_original c h hi x hx hnc
  let S := ChapterB.baumann R
  let Q := (K ⊔ S).pCoreIn 2
  let W := Q.map (MulAut.conj x⁻¹).toMonoidHom
  have hJ : S = elementaryAbelianMaxJ R := h.baumann_eq_maxJ x (c.R_normal hx) hnc hphi
  have hW : (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ⊔
      (S ⊓ centralizer (K : Set G)) = W :=
    (h.family_structure hRK x (c.R_normal hx) hnc hphi).1
  obtain ⟨P,P',hf,hPi,hP'i,hg⟩ := h.four_geometry x (c.R_normal hx) hnc hphi
  change elementaryAbelianMaxSubgroups R = {Q,_,P,P'} at hf
  change FourFamilyGeometry S Q _ P P' (Q ⊓ _) at hg
  rw [hW] at hf hg
  have hQ : Q ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hP : P ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hP' : P' ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hRQ : R ≤ normalizer (Q : Set G) := by
    rw [show Q = H.pCoreIn 2 from hsrc.1]
    exact c.R_le_H.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hRW : R ≤ normalizer (W : Set G) := by
    have heR : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (c.R_normal (M.inv_mem hx))
    rw [←heR]
    exact (map_mono hRQ).trans (le_normalizer_map (MulAut.conj x⁻¹).toMonoidHom)
  have hfull : R ⊓ centralizer (sourceModule K : Set G) = Q :=
    (original_core_eq_module_centralizer c h.block.2.1).trans hsrc.1.symm
  have hRP : R ⊓ normalizer (P : Set G) ≤ S :=
    (h.extra_family_stabilizer hRK hfull x (c.R_normal hx) hnc hphi P hP hPi).le
  have hpairQ (a : G) (ha : a ∈ M) :
      Q.map (MulAut.conj a).toMonoidHom = Q ∨ Q.map (MulAut.conj a).toMonoidHom = W :=
    h.core_pair_preserved hRK x (c.R_normal hx) hnc hphi a (c.R_normal ha)
  have hWne : W ≠ Q := by
    intro he
    have hUQ : sourceModule K ≤ Q := le_sup_left.trans_eq h.product.symm
    exact hnc (((map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hUQ).trans_eq he).trans
      (h.core.le.trans inf_le_right))
  have hiQ := normalizer_relIndex_eq_two_of_pair M Q W hpairQ x⁻¹ (M.inv_mem hx) hWne
  have hN : M ⊓ normalizer (Q : Set G) = R := by
    have hr := count R M
    rw [inf_eq_left.mpr c.T_le,hi] at hr
    have hm := count (normalizer (Q : Set G)) M
    rw [hiQ,inf_comm (normalizer (Q : Set G)) M] at hm
    exact (eq_of_le_of_card_ge (le_inf c.T_le hRQ) (by omega)).symm
  have hinverse (A : Subgroup G) (a : G) :
      (A.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom = A := by
    rw [map_map]
    have he : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom = MonoidHom.id G := by
      ext z
      simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]
  have hswap (a : G) (haM : a ∈ M) (haR : a ∉ R) :
      Q.map (MulAut.conj a).toMonoidHom = W ∧ W.map (MulAut.conj a).toMonoidHom = Q := by
    have hs (b : G) (hb : b ∈ M) (hbr : b ∉ R) : Q.map (MulAut.conj b).toMonoidHom = W :=
      (hpairQ b hb).resolve_left (fun he => hbr (hN ▸
        (show b ∈ M ⊓ normalizer (Q : Set G) from ⟨hb,mem_normalizer_iff_map_conj_eq.mpr he⟩)))
    refine ⟨hs a haM haR,?_⟩
    have hai : a⁻¹ ∉ R := fun hh => haR (by simpa only [inv_inv] using R.inv_mem hh)
    rw [←hs a⁻¹ (M.inv_mem haM) hai]
    exact hinverse Q a
  have hPW : P ≠ W := by
    intro he
    have hnorm : R ≤ normalizer (P : Set G) := he.symm ▸ hRW
    have hRS : R ≤ S := fun r hr => hRP ⟨hr,hnorm hr⟩
    have hs : S = R := le_antisymm inf_le_left hRS
    have hh := haction.1
    rw [←hJ,hs,relIndex_self] at hh
    omega
  have hPQ : P ≠ Q := by
    intro he
    have hnorm : R ≤ normalizer (P : Set G) := he.symm ▸ hRQ
    have hRS : R ≤ S := fun r hr => hRP ⟨hr,hnorm hr⟩
    have hs : S = R := le_antisymm inf_le_left hRS
    have hh := haction.1
    rw [←hJ,hs,relIndex_self] at hh
    omega
  have hP'P : P' ≠ P := by
    intro he
    exact hg.cross_ne (by rw [he])
  have hP'Q : P' ≠ Q := by
    intro he
    have hh := hg.opposite_second
    rw [he,inf_comm P Q] at hh
    have hc := count Q P
    rw [hh] at hc
    have hcard : Nat.card P = Nat.card Q := le_antisymm
      (hQ.2.2 P hP.1 hP.2.1) (hP.2.2 Q hQ.1 hQ.2.1)
    have hp := Nat.card_pos (α := ↥(Q ⊓ W))
    have hiP := hg.adjacent_left
    have hlarge := hg.core_card
    nlinarith
  have hP'W : P' ≠ W := by
    intro he
    have hVS : (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ S :=
      (map_mono h.module_le).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (normalizer_le_normalizer_baumann R (c.R_normal (M.inv_mem hx))))
    have him : actionImage h.action W = ChapterB.Offenders.D 5 := by
      rw [←hW,actionImage_sup h.action (hVS.trans le_sup_right)
        (inf_le_left.trans le_sup_right)]
      have hd : actionImage h.action (S ⊓ centralizer (K : Set G)) = ⊥ := by
        unfold actionImage
        apply (Subgroup.map_eq_bot_iff _).mpr
        intro d hd
        rw [h.action_kernel]
        exact (inf_le_right.trans (centralizer_le (map_subtype_le _))) hd
      rw [hd,sup_bot_eq]
      exact h.conjugate_action_image x (c.R_normal hx) hnc
    have hc := congrArg (fun A : Subgroup FivePerm => Nat.card A)
      (hP'i.symm.trans ((congrArg (actionImage h.action) he).trans him))
    rw [Enumeration.line_card,Enumeration.actor_card] at hc
    omega
  have hextra (B : Subgroup G) (hB : B ∈ elementaryAbelianMaxSubgroups R)
      (hBQ : B ≠ Q) (hBW : B ≠ W) (a : G) (ha : a ∈ M) :
      B.map (MulAut.conj a).toMonoidHom = P ∨ B.map (MulAut.conj a).toMonoidHom = P' := by
    have heR : R.map (MulAut.conj a).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp (c.R_normal ha)
    have hm := (maxFamily_map_injective_iff (MulAut.conj a).toMonoidHom (MulAut.conj a).injective R B).mpr hB
    rw [heR,hf] at hm
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hm
    have hn (C : Subgroup G) (hC : C.map (MulAut.conj a⁻¹).toMonoidHom = Q ∨
        C.map (MulAut.conj a⁻¹).toMonoidHom = W)
        (he : B.map (MulAut.conj a).toMonoidHom = C) : False := by
      have hh : B = C.map (MulAut.conj a⁻¹).toMonoidHom := by
        rw [←he]
        simpa only [inv_inv] using (hinverse B a⁻¹).symm
      exact hC.elim (fun hq => hBQ (hh.trans hq)) (fun hw => hBW (hh.trans hw))
    rcases hm with hm | hm | hm | hm
    · exact (hn Q (hpairQ a⁻¹ (M.inv_mem ha)) hm).elim
    · have hWa : W.map (MulAut.conj a⁻¹).toMonoidHom = Q ∨ W.map (MulAut.conj a⁻¹).toMonoidHom = W := by
        by_cases har : a⁻¹ ∈ R
        · exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hRW har))
        · exact Or.inl (hswap a⁻¹ (M.inv_mem ha) har).2
      exact (hn W hWa hm).elim
    · exact Or.inl hm
    · exact Or.inr hm
  have hpair (a : G) (ha : a ∈ M) :
      (P.map (MulAut.conj a).toMonoidHom = P ∧ P'.map (MulAut.conj a).toMonoidHom = P') ∨
      (P.map (MulAut.conj a).toMonoidHom = P' ∧ P'.map (MulAut.conj a).toMonoidHom = P) := by
    have hn : P'.map (MulAut.conj a).toMonoidHom ≠ P.map (MulAut.conj a).toMonoidHom :=
      fun he => hP'P (map_injective (MulAut.conj a).injective he)
    rcases hextra P hP hPQ hPW a ha with hp | hp
    · exact Or.inl ⟨hp,(hextra P' hP' hP'Q hP'W a ha).resolve_left (fun hh => hn (hh.trans hp.symm))⟩
    · exact Or.inr ⟨hp,(hextra P' hP' hP'Q hP'W a ha).resolve_right (fun hh => hn (hh.trans hp.symm))⟩
  have hidx : S.relIndex M ≤ 4 := by
    have hh := relIndex_mul_relIndex S R M inf_le_left c.T_le
    rw [hJ,haction.1,hi] at hh
    rw [hJ]
    omega
  exact thompson_stable_of_four_family_geometry M R S Q W P P' (Q ⊓ W) hg c.T_le
    inf_le_left hQ hi hidx hRQ hRW hswap hpair hRP
end CFSG.Quasithin.ChapterC.Section06
