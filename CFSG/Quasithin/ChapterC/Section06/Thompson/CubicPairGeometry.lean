module
public import CFSG.Quasithin.ChapterC.Section06.Thompson.CubicPairAction
public import CFSG.Quasithin.ChapterC.Section06.RankOnePairSource
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingEnumeration
public import Theory.GroupTheory.ElementaryThompsonFourFamilyTransport
/-!
# Original paired-cubic four-family geometry

The two actual cubic modules combine into the marked five-letter core. Its
full pair-swap image and the central elementary factor provide the existing
fixed profile. The original opposite module then gives four maximum members,
with the common intersection, adjacent indices and distinct crossed
commutators required by the C.6.1 count. Every member is normalized by Baum(R).

Source: Aschbacher–Smith C.6.1, paired A₃ branch, printed p.165.
-/
public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
variable {G : Type*} [Group G] [Finite G] {H M K L R : Subgroup G}

theorem cubic_pair_geometry_from_original
    (c : OriginalHypotheses H M (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) = H.pCoreIn 2)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let Q := H.pCoreIn 2
    let W := Q.map (MulAut.conj x⁻¹).toMonoidHom
    ∃ P P' : Subgroup G,
      elementaryAbelianMaxSubgroups R = {Q,W,P,P'} ∧
      FourFamilyGeometry S Q W P P' (Q ⊓ W) ∧
      (∀ A ∈ elementaryAbelianMaxSubgroups R,S ≤ normalizer (A : Set G)) := by
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hH : H = (K ⊔ L) ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have hp := h.two_block_source_product h' hKL H M R c.T_le c.R_normal hRK hH hno x hx hi hpair ht hnc
  have hf := h.two_block_invariant_family h' hKL H M R c.T_le c.R_normal hRK hH hno x hx hi hpair ht hnc
  have hs := h.source_two_block_terminal_equalities h' c.R_twoGroup hKL H M R le_rfl
    c.T_le c.R_normal hRK hH hno x hx hi hpair ht hnc
  let S := ChapterB.baumann R
  let U := RankOne.U K ⊔ RankOne.U L
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let Q := S ⊓ centralizer (U : Set G)
  let W := V ⊔ D
  let σ := h.paired_cubic_action h' hK hL
  have hUS : U ≤ S := sup_le h.module_le h'.module_le
  have hVS : V ≤ S := by
    change (RankOne.U K ⊔ RankOne.U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ S
    rw [Subgroup.map_sup]
    exact sup_le (h.conjugate_le (c.R_normal hx)) (h'.conjugate_le (c.R_normal hx))
  have hDS : D ≤ S := inf_le_left
  have hQS : Q ≤ S := inf_le_left
  have hWS : W ≤ S := sup_le hVS hDS
  have hcore : Q = H.pCoreIn 2 := hs.2.1.symm.trans hfull
  have hprod : Q = U ⊔ D := hp.1
  have hWeq : W = Q.map (MulAut.conj x⁻¹).toMonoidHom := hf.2.2.1
  let : IsElementaryAbelian 2 Q := hp.2.2.2.2.2
  let : IsElementaryAbelian 2 W := hWeq ▸ IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (hprod ▸ le_sup_right)
  have hDC : D ≤ centralizer (S : Set G) := by
    have hspan : S = (U ⊔ V) ⊔ D := hp.2.2.1
    rw [hspan]
    apply le_centralizer_iff.mpr
    refine sup_le (sup_le ?_ (le_centralizer_iff.mp hp.2.1)) (le_centralizer D)
    exact le_centralizer_iff.mp ((show D ≤ Q from hprod ▸ le_sup_right).trans inf_le_right)
  have hnorm : ∀ A ∈ elementaryAbelianMaxSubgroups R,S ≤ normalizer (A : Set G) := by
    intro A hA
    have hAf := h.two_block_family h' hKL H M R c.T_le c.R_normal hRK hH hno x hx hi hpair ht hnc A
    rw [baumann_maxFamily R] at hAf
    obtain ⟨a,ha,b,hb,rfl⟩ := hAf.mp hA
    have haN : S ≤ normalizer (a : Set G) := by
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · exact h.coordinates.normalizes
      · obtain rfl := Set.mem_singleton_iff.mp ha
        exact h.conjugate_normalized (c.R_normal hx)
    have hbN : S ≤ normalizer (b : Set G) := by
      rcases Set.mem_insert_iff.mp hb with rfl | hb
      · exact h'.coordinates.normalizes
      · obtain rfl := Set.mem_singleton_iff.mp hb
        exact h'.conjugate_normalized (c.R_normal hx)
    have hDN : S ≤ normalizer (D : Set G) :=
      (le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _)
    exact (le_inf ((le_inf haN hbN).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)) hDN).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let Ui := U.subgroupOf S
  let Di := D.subgroupOf S
  let Qi := Q.subgroupOf S
  let Wi := W.subgroupOf S
  have hk : σ.ker = Qi := by
    rw [h.paired_cubic_kernel h' hK hL]
    ext s
    exact (and_iff_right s.property).symm
  have hr := h.paired_cubic_range h' hK hL hKL M R x hx (c.R_normal hx) hi hpair ht hnc
  have hWi : Wi.map σ = ChapterB.Offenders.D 5 := by
    change (W.subgroupOf S).map σ = _
    rw [show W = V ⊔ D from rfl,subgroupOf_sup hVS hDS,Subgroup.map_sup]
    have hd : (D.subgroupOf S).map σ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr
      ((subgroupOf_mono S (hprod ▸ le_sup_right)).trans hk.ge)
    rw [hd,sup_bot_eq]
    exact hr.2
  let : IsElementaryAbelian 2 Qi := IsElementaryAbelian.subgroupOf hQS
  let : IsElementaryAbelian 2 Wi := IsElementaryAbelian.subgroupOf hWS
  have hQWcard : Nat.card Wi = Nat.card Qi := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWS).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv,hWeq,
      card_map_of_injective (MulAut.conj x⁻¹).injective]
  have hprodi : Qi = Ui ⊔ Di := by
    change Q.subgroupOf S = _
    rw [hprod,subgroupOf_sup hUS hDS]
  have hDi : Di ≤ center S := by
    intro d hd
    exact mem_center_iff.mpr (fun s => Subtype.ext (hDC hd s s.property))
  obtain ⟨eU,heU⟩ := h.exists_paired_cubic_coordinates h' hK hL hKL
  let e : Ui ≃* Multiplicative Vector := (subgroupOfEquivOfLe hUS).trans eU
  have he (s : S) (u : Ui) :
      (e.symm (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (σ s) (e u).toAdd)) : S) =
        s * (u : S) * s⁻¹ := by
    apply Subtype.ext
    exact heU s ((subgroupOfEquivOfLe hUS) u)
  have hprofile : FixedProfile σ Qi := by
    rw [←hk]
    exact marked_kernel_fixedProfile σ Ui Di (hk.trans hprodi) hr.1 hDi e he
  obtain ⟨P,P',hfour,hPi,hP'i⟩ := exists_maxFamily_eq_four σ Qi Wi inferInstance inferInstance
    hk hr.1 hWi hQWcard hprofile
  have hWmax : Wi ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by rw [hfour]; simp
  have hPmax : P ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by rw [hfour]; simp
  have hP'max : P' ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by rw [hfour]; simp
  have hQmax : Qi ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by rw [hfour]; simp
  have hnormi (A : Subgroup S) (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S)) :
      (⊤ : Subgroup S) ≤ normalizer (A : Set S) := by
    have hm := (maxFamily_map_injective_iff S.subtype S.subtype_injective ⊤ A).mpr hA
    rw [←MonoidHom.range_eq_map,range_subtype,baumann_maxFamily R] at hm
    have hn := hnorm (A.map S.subtype) hm
    intro s _
    have hh : s ∈ (normalizer (A.map S.subtype : Set G)).subgroupOf S := hn s.property
    rwa [subgroupOf_normalizer_eq (map_subtype_le A),subgroupOf,
      comap_map_eq_self_of_injective S.subtype_injective] at hh
  let ι : Multiplicative Vector →* S := Ui.subtype.comp e.symm.toMonoidHom
  have hiι : Function.Injective ι := Ui.subtype_injective.comp e.symm.injective
  have hir : ι.range = Ui := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have heι (s : S) (v : Vector) :
      ι (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (σ s) v)) =
        s * ι (Multiplicative.ofAdd v) * s⁻¹ := by
    have hh := he s (e.symm (Multiplicative.ofAdd v))
    simpa only [ι,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply,toAdd_ofAdd,Subgroup.subtype_apply] using hh
  have hg := marked_four_geometry σ Qi Wi P P' Di hk hr.1 hprofile hWmax hPmax hP'max hWi hPi hP'i
    (le_top.trans (hnormi Wi hWmax)) (le_top.trans (hnormi Qi hQmax)) ι hiι (hir.symm ▸ hprodi) hDi heι
  have hga := hg.map_subtype S Qi Wi P P' (Qi ⊓ Wi)
  rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hWS,
    Subgroup.map_inf _ _ _ S.subtype_injective,map_subgroupOf_eq_of_le hQS,
    map_subgroupOf_eq_of_le hWS] at hga
  refine ⟨P.map S.subtype,P'.map S.subtype,?_,?_,hnorm⟩
  · ext B
    rw [←baumann_maxFamily R,maxFamily_equiv_iff S (MulEquiv.refl S) B,hfour]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,exists_eq_or_imp,exists_eq_left]
    change (B = Qi.map S.subtype ∨ B = Wi.map S.subtype ∨ B = P.map S.subtype ∨ B = P'.map S.subtype) ↔ _
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hWS,hWeq,hcore]
  · rw [hWeq,hcore] at hga
    exact hga
end CFSG.Quasithin.ChapterC.Section06
