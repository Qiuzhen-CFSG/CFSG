module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingSource
public import CFSG.Quasithin.ChapterC.Section06.Thompson.CubicPairGeometry
public import Theory.GroupAction.OmegaCenterFixedProduct

/-!
# Small-block centralizers in the original C.6 configuration

For a single A₅ block or a commuting pair of A₃ blocks, write
D = C_R(O²(H)) and E = Ω₁(Z(J(R))). The existing source product and
marked action give E = C_U(J(R)) × D, with the fixed module factor of
order four. Thus D ≤ E and [E : D] = 4. The original conjugator normalizes
E, while the source proves D ∩ Dˣ = 1; comparison with its conjugate then
gives |D| ≤ 4.

These are the literal center and centralizer estimates used in the small-block
branch of 14.6.9. All action, elementary-core and conjugate-intersection facts
are supplied by the preceding C.5 source proofs.
Source: Aschbacher–Smith, C.5.6, C.6.1 and 14.6.9, printed pp.156–159,
164–166 and 1025 (refs/quasithin.pdf).
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K L R : Subgroup G}

private theorem omegaCenter_index_of_fixed_factor
    (S U D : Subgroup G) (hUS : U ≤ S) (hDS : D ≤ S)
    (hUD : Disjoint U D) (hUn : S ≤ normalizer (U : Set G))
    (hDC : D ≤ centralizer (S : Set G))
    (hQ : S ⊓ centralizer (U : Set G) = U ⊔ D)
    (he : IsElementaryAbelian 2 (U ⊔ D : Subgroup G))
    (hfixed : Nat.card (U ⊓ centralizer (S : Set G) : Subgroup G) = 4) :
    D ≤ omegaOneCenterAmbient S ∧ D.relIndex (omegaOneCenterAmbient S) = 4 := by
  let F := U ⊓ centralizer (S : Set G)
  let := he
  have hDE : D ≤ omegaOneCenterAmbient S := by
    intro d hd
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hDS hd, ?_, hDC hd⟩
    exact elemPow_eq_one_of_isElementaryAbelian d (show d ∈ (U ⊔ D : Subgroup G) from mem_sup_right hd)
  have hFE : F ≤ omegaOneCenterAmbient S := by
    intro f hf
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hUS hf.1, ?_, hf.2⟩
    exact elemPow_eq_one_of_isElementaryAbelian f (show f ∈ (U ⊔ D : Subgroup G) from mem_sup_left hf.1)
  have hspan : omegaOneCenterAmbient S ≤ U ⊔ D := by
    rw [←hQ]
    intro z hz
    obtain ⟨hzS,_,hzc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    exact ⟨hzS,fun u hu => hzc u (hUS hu)⟩
  have heq : omegaOneCenterAmbient S = F ⊔ D := by
    apply le_antisymm
    · have hh := omegaOneCenterAmbient_le_fixed_factors S U D hUS hDS hUD hUn
        ((le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _))
        (le_centralizer_iff.mp (hDC.trans (centralizer_le hUS))) hspan
      simpa only [inf_eq_left.mpr hDC] using hh
    · exact sup_le hFE hDE
  have hFD : Disjoint F D := hUD.mono_left inf_le_left
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting F D hFD
    (le_centralizer_iff.mp (hDC.trans (centralizer_le (inf_le_left.trans hUS))))
  have hcard : Nat.card (omegaOneCenterAmbient S) = 4 * Nat.card D := by
    rw [heq,←Nat.card_congr e.toEquiv,Nat.card_prod,hfixed]
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) D (omegaOneCenterAmbient S) bot_le hDE
  rw [relIndex_bot_left,relIndex_bot_left,hcard] at hcount
  exact ⟨hDE,by have : 0 < Nat.card D := Nat.card_pos; nlinarith⟩

private theorem card_le_of_center_index (R D : Subgroup G) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hD : D ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ R))
    (hi : D.relIndex (omegaOneCenterAmbient (elementaryAbelianMaxJ R)) = 4)
    (hd : D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥) : Nat.card D ≤ 4 := by
  let E := omegaOneCenterAmbient (elementaryAbelianMaxJ R)
  let f := (MulAut.conj x⁻¹).toMonoidHom
  have hJ : (elementaryAbelianMaxJ R).map f = elementaryAbelianMaxJ R := by
    rw [←elementaryAbelianMaxJ_map_injective f (MulAut.conj x⁻¹).injective]
    have hR : R.map f = R := mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx)
    rw [hR]
  have hE : E.map f = E := by
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ R)).map f = _
    rw [←omegaOneCenterAmbient_map_injective f (MulAut.conj x⁻¹).injective,hJ]
  have hDx : D.map f ≤ E := (map_mono hD).trans hE.le
  have hix : D.relIndex (D.map f) = Nat.card D := by
    rw [←inf_relIndex_right,hd,relIndex_bot_left,card_map_of_injective (MulAut.conj x⁻¹).injective]
  rw [←hix,←hi]
  exact relIndex_le_of_le_right hDx index_ne_zero_of_finite

/-- The A₅ source branch supplies the literal center index and |C_R(K)| ≤ 4. -/
theorem alternating_block_center_index_from_original
    (c : OriginalHypotheses H M K R R) (h : AlternatingPairSetup R K L)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let D := R ⊓ centralizer (K : Set G)
    let E := omegaOneCenterAmbient (elementaryAbelianMaxJ R)
    D ≤ E ∧ D.relIndex E = 4 ∧ Nat.card D ≤ 4 := by
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hH : H = K ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have hfull := original_core_eq_module_centralizer c h.block.2.1
  have hp := h.source_C56_single_block_7 hRK H M R c.T_le c.R_normal hRK hH hno
    (hfull.trans (congrArg (fun A : Subgroup G => A.pCoreIn 2) hH)) x hx hi hnc
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let D := S ⊓ centralizer (K : Set G)
  have hQ : S ⊓ centralizer (U : Set G) = U ⊔ D := h.core.symm.trans h.product
  have hQe : IsElementaryAbelian 2 (U ⊔ D : Subgroup G) := by
    rw [←hp.2.2.2.2.1]
    exact hp.2.2.2.2.2.1.2.1
  have hDC : D ≤ centralizer (S : Set G) := by
    let := hQe
    have hDab : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ U ⊔ D from le_sup_right)
    let := hDab
    rw [show S = (U ⊔ V) ⊔ D from hp.2.2.2.2.2.2.1]
    apply le_centralizer_iff.mpr
    refine sup_le (sup_le ?_ ?_) (le_centralizer D)
    · exact le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (map_subtype_le _)))
    · exact le_centralizer_iff.mp (h.centralizer_centralizes_conjugate x (c.R_normal hx) hnc)
  let a := h.action.comp (inclusion (show S ≤ K ⊔ S from le_sup_right))
  have ha : a.range = ChapterB.Offenders.D 5 := by
    rw [MonoidHom.range_comp]
    have hr : (inclusion (show S ≤ K ⊔ S from le_sup_right)).range = S.subgroupOf (K ⊔ S) := by
      ext s
      constructor
      · rintro ⟨s,rfl⟩; exact s.property
      · intro hs; exact ⟨⟨s,hs⟩,rfl⟩
    rw [hr]
    exact h.baumann_image
  have hf := marked_fixed_plane_card S U a h.coordinates ha
    (fun s u => h.equivariant (inclusion le_sup_right s) u)
  have hh := omegaCenter_index_of_fixed_factor S U D h.module_le inf_le_left
    (alternatingModule_disjoint_of_commuting K D h.block inf_le_right)
    (h.normalizes.trans (normalizer_le_normalizer_characteristic_image K (blockU K))) hDC hQ hQe hf
  have hDeq : D = R ⊓ centralizer (K : Set G) := hp.2.2.2.1
  have hSeq : S = elementaryAbelianMaxJ R := hp.2.2.2.2.2.2.2.1
  rw [hDeq,hSeq] at hh
  have hd := hp.2.2.1
  rw [hp.2.2.2.1] at hd
  exact ⟨hh.1,hh.2,card_le_of_center_index R _ x (c.R_normal hx) hh.1 hh.2 hd⟩
omit [Finite G] in
private theorem paired_module_disjoint (hK : IsAlternatingBlock K 3)
    (hL : IsAlternatingBlock L 3) (hKL : L ≤ centralizer (K : Set G))
    (D : Subgroup G) (hD : D ≤ centralizer (K ⊔ L : Subgroup G)) :
    Disjoint (RankOne.U K ⊔ RankOne.U L) D := by
  have hc : RankOne.U K ≤ centralizer (RankOne.U L : Set G) :=
    le_centralizer_iff.mp ((map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _))))
  apply disjoint_def.mpr
  intro u hu hd
  have hmul : u ∈ (RankOne.U K : Set G) * (RankOne.U L : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ (hc.trans (Subgroup.centralizer_le_normalizer _))]
    exact hu
  obtain ⟨u₁,hu₁,u₂,hu₂,rfl⟩ := hmul
  have h₂K : u₂ ∈ centralizer (K : Set G) := hKL ((map_subtype_le _) hu₂)
  have h₁K : u₁ ∈ centralizer (K : Set G) := by
    have hh := (centralizer (K : Set G)).mul_mem
      ((hD.trans (centralizer_le (show K ≤ K ⊔ L from le_sup_left))) hd)
      ((centralizer (K : Set G)).inv_mem h₂K)
    simpa only [mul_inv_cancel_right] using hh
  have he₁ : u₁ = 1 := disjoint_def.mp
    (RankOne.cubic_module_disjoint hK (centralizer (K : Set G)) le_rfl) hu₁ h₁K
  have h₂L : u₂ ∈ centralizer (L : Set G) := by
    have hh := (hD.trans (centralizer_le (show L ≤ K ⊔ L from le_sup_right))) hd
    simpa only [he₁,one_mul] using hh
  have he₂ : u₂ = 1 := disjoint_def.mp
    (RankOne.cubic_module_disjoint hL (centralizer (L : Set G)) le_rfl) hu₂ h₂L
  simp only [he₁,he₂,one_mul]

/-- The paired A₃ source branch supplies the literal center index and centralizer bound. -/
theorem cubic_pair_block_center_index_from_original
    (c : OriginalHypotheses H M (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let D := R ⊓ centralizer (K ⊔ L : Subgroup G)
    let E := omegaOneCenterAmbient (elementaryAbelianMaxJ R)
    D ≤ E ∧ D.relIndex E = 4 ∧ Nat.card D ≤ 4 := by
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
  let D := S ⊓ centralizer (K ⊔ L : Subgroup G)
  let Q := S ⊓ centralizer (U : Set G)
  have hUS : U ≤ S := sup_le h.module_le h'.module_le
  have hQ : Q = U ⊔ D := hp.1
  have hQe : IsElementaryAbelian 2 (U ⊔ D : Subgroup G) := hQ ▸ hp.2.2.2.2.2
  let := hQe
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ U ⊔ D from le_sup_right)
  have hDC : D ≤ centralizer (S : Set G) := by
    rw [show S = (U ⊔ V) ⊔ D from hp.2.2.1]
    apply le_centralizer_iff.mpr
    refine sup_le (sup_le ?_ (le_centralizer_iff.mp hp.2.1)) (le_centralizer D)
    exact le_centralizer_iff.mp ((show D ≤ Q from hQ ▸ le_sup_right).trans inf_le_right)
  have hnU : S ≤ normalizer (U : Set G) :=
    (le_inf h.coordinates.normalizes h'.coordinates.normalizes).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨e,he⟩ := h.exists_paired_cubic_coordinates h' hK hL hKL
  have hr := h.paired_cubic_range h' hK hL hKL M R x hx (c.R_normal hx) hi hpair ht hnc
  have hfix := marked_fixed_plane_card S U (h.paired_cubic_action h' hK hL) e hr.1 he
  have hh := omegaCenter_index_of_fixed_factor S U D hUS inf_le_left
    (paired_module_disjoint hK hL hKL D inf_le_right) hnU hDC hp.1 hQe hfix
  have hDeq : D = R ⊓ centralizer (K ⊔ L : Subgroup G) := hs.2.2.symm
  have hSeq : S = elementaryAbelianMaxJ R := hf.2.1
  rw [hDeq,hSeq] at hh
  have hd := hp.2.2.2.2.1
  rw [←hs.2.2] at hd
  exact ⟨hh.1,hh.2,card_le_of_center_index R _ x (c.R_normal hx) hh.1 hh.2 hd⟩

end CFSG.Quasithin.ChapterC.Section06
