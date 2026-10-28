module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentElevenCubic
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Cubic movement of the original perpendicular

The literal P_K-star is normalized by the original L₁T image. Irreducibility
of V₅/V₁ and the equality C_G(V₅)=C_G(V) make its seed movement full.
Coprime action then shows [V,P_K]=[V₅,P_K], an elementary subgroup of
order16 complementing V₁ in V₅. All actors remain in the original group.

Source: Aschbacher--Smith, proof of12.6.26, printed p.833.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hz hTV hTz hbound hH hn a in
theorem SourceHypothesis.original_selectedComponent_cubic_star_normalized
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    Nonabelian.Setup.star H (E.L₁ ⊔ (T : Subgroup G)) ≤
      normalizer (Nonabelian.Setup.star H PK : Set (Nonabelian.Setup.Hstar H)) := by
  let E := D.fullSetup hZ T z
  let J := E.L₁ ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 H)
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hJL : J ≤ normalizer (E.L₁ : Set G) := sup_le E.L₁.le_normalizer
    ((le_inf h.T_le_H hTV).trans
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH))
  have hnL : Nonabelian.Setup.star H J ≤ normalizer (Nonabelian.Setup.star H E.L₁ : Set _) := by
    rintro _ ⟨x,hx,rfl⟩
    apply (E.L₁.subgroupOf H).le_normalizer_map q
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq (show E.L₁ ≤ H from le_sup_left.trans h.local_le)]
    exact hJL hx
  let := (S.original_selectedComponent_normal D hZ z hz hTV hTz hbound hH hn c a hTI hns).2
  dsimp only
  rw [(S.original_selectedComponent_sylow_intersection_star D hZ z hz hTV hTz hbound hH hn c a hTI hns P).2,
    S.original_selectedComponent_residual_sylow_star_eq D hZ z hz hTV hTz hbound hH hn c a hTI hns P]
  exact (le_inf hnL le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

include hz hTV hTz hbound hH hn a in
theorem SourceHypothesis.original_selectedComponent_cubic_seed_not_fixed
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    ¬ ⁅E.V₅,PK⁆ ≤ E.V₁ := by
  let E := D.fullSetup hZ T z
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hPL : PK ≤ E.L₁ := inf_le_left.trans (map_subtype_le _)
  have hPH : PK ≤ H := inf_le_right.trans c.le_H
  have hPN : PK ≤ normalizer (E.V₅ : Set G) := hPL.trans (le_sup_left.trans h.local_normalizes)
  have hp : IsPGroup 3 PK := (P.isPGroup'.map E.L₁.subtype).to_le inf_le_left
  have hc := IsPGroup.coprime_card_of_ne 3 2 (by decide) PK E.V₅ hp
    ((IsElementaryAbelian.isPGroup 2 V).to_le E.V₅_le)
  have hid := commutator_closure_coprime_idempotent E.V₅ (PK : Set G)
    (by simpa only [closure_eq] using hPN)
    (fun x hx => hc.of_dvd_left (PK.orderOf_dvd_natCard hx))
  simp only [closure_eq] at hid
  change ¬ ⁅E.V₅,PK⁆ ≤ E.V₁
  intro hsmall
  have hzP : ⁅E.V₁,PK⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (hPH.trans h.H_centralizes))
  have he : ⁅E.V₅,PK⁆ = ⊥ := bot_unique (hid.ge.trans
    ((commutator_mono hsmall le_rfl).trans_eq hzP))
  have hfix : PK ≤ centralizer (V : Set G) := by
    rw [←S.original_perpendicular_centralizer D hZ z hz hTV hTz hbound]
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  have hcore : PK ≤ L.pCoreIn 2 := by
    rw [←S.centralizer_eq_core]
    exact le_inf (hPL.trans ((map_subtype_le _).trans inf_le_left)) hfix
  have h2 : IsPGroup 2 PK := (isPGroup_pCoreIn 2 L).to_le hcore
  have hb : PK = ⊥ := by
    simpa only [inf_idem] using (h2.disjoint_of_coprime hp (by decide)).eq_bot
  have hcard := S.original_selectedComponent_sylow_intersection_card
    D hZ z hz hTV hTz hbound hH hn c a hTI hns P
  change Nat.card PK = 3 at hcard
  rw [hb,card_bot] at hcard
  omega

include hz hTV hTz hbound hH hn a in
theorem SourceHypothesis.original_selectedComponent_cubic_seed_image
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    subspaceCommutator σ (κ.imageSpace E.V₅) (Nonabelian.Setup.star H PK) =
      κ.imageSpace E.V₅ := by
  let E := D.fullSetup hZ T z
  let J := E.L₁ ⊔ (T : Subgroup G)
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  let q := QuotientGroup.mk' (pCore 2 H)
  let I := κ.imageSpace E.V₅
  let A := Nonabelian.Setup.star H PK
  let B := subspaceCommutator σ I A
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hSU : E.V₅ ≤ E.UH H := le_conjugateSpanBy _ _
  have hPH : PK ≤ H := inf_le_right.trans c.le_H
  have hPJ : PK ≤ J := (inf_le_left.trans (map_subtype_le _)).trans le_sup_left
  have hJI : Nonabelian.Setup.star H J ≤ subspaceStabilizer σ I := by
    apply le_subspaceStabilizer
    rintro _ ⟨x,hx,rfl⟩ v hv
    obtain ⟨u,hu,rfl⟩ := (κ.mem_imageSpace_iff E.V₅ v).mp hv
    refine (κ.mem_imageSpace_iff E.V₅ _).mpr ⟨⟨x*u*(x:G)⁻¹,
      (mem_normalizer_iff.mp (κ.normalized x.property) u).mp u.property⟩,
      (mem_normalizer_iff.mp (h.local_normalizes hx) u).mp hu,κ.equivariant x u⟩
  have hAI : A ≤ subspaceStabilizer σ I := (map_mono (comap_mono hPJ)).trans hJI
  have hBI : B ≤ I := subspaceCommutator_le_of_invariant σ hAI
  have hJB : Nonabelian.Setup.star H J ≤ subspaceStabilizer σ B :=
    subspaceCommutator_invariant_normalizer σ hJI
      (S.original_selectedComponent_cubic_star_normalized D hZ z hz hTV hTz hbound hH hn c a hTI hns P)
  have hBnorm : J ≤ normalizer (κ.subspacePreimage B : Set G) := by
    apply κ.subspacePreimage_normalized J h.local_le B
    intro x hx
    exact hJB (mem_map_of_mem q hx)
  have hBseed : κ.subspacePreimage B ≤ E.V₅ :=
    κ.subspacePreimage_le_of_imageSpace_le B E.V₅ E.V₁_le_V₅ hBI
  rcases h.irreducible (κ.subspacePreimage B) (κ.kernel_le_subspacePreimage B)
      hBseed hBnorm with hzero | hfull
  · have hzB : B = ⊥ := by
      rw [←κ.imageSpace_subspacePreimage B,hzero]
      apply bot_unique
      intro v hv
      obtain ⟨u,hu,rfl⟩ := (κ.mem_imageSpace_iff E.V₁ v).mp hv
      rw [(κ.coordinates_eq_one_iff u).mpr hu]
      exact Submodule.zero_mem _
    have hf := (subspaceCommutator_eq_bot_iff σ I A).mp hzB
    have hh : ⁅PK,E.V₅⁆ ≤ E.V₁ := κ.commutator_le_of_imageSpace_fixed PK E.V₅ hPH hSU (by
      intro v hv x
      exact hf hv ⟨q x.val,mem_map_of_mem q x.property⟩)
    exact (S.original_selectedComponent_cubic_seed_not_fixed D hZ z hz hTV hTz hbound
      hH hn c a hTI hns P ((commutator_comm E.V₅ PK).le.trans hh)).elim
  · change B = I
    rw [←κ.imageSpace_subspacePreimage B,hfull]
    rfl

include hz hTV hTz hbound hH hn a in
theorem SourceHypothesis.original_selectedComponent_cubic_seed_sup
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    ⁅E.V₅,PK⁆ ⊔ E.V₁ = E.V₅ := by
  let E := D.fullSetup hZ T z
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let _ : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
  let _ : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
  let W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))
  obtain ⟨σ,κ,_,_⟩ := h.faithful_point_quotient
  change Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W at σ
  change BinaryConjugationSection H (E.UH H) E.V₁
    (σ.comp (QuotientGroup.mk' (pCore 2 H))) at κ
  have hSU : E.V₅ ≤ E.UH H := le_conjugateSpanBy _ _
  have hPN : PK ≤ normalizer (E.V₅ : Set G) :=
    ((inf_le_left.trans (map_subtype_le _)).trans le_sup_left).trans h.local_normalizes
  have hCS : ⁅E.V₅,PK⁆ ≤ E.V₅ := le_normalizer_iff_commutator_le_left.mp hPN
  have him : κ.imageSpace ⁅E.V₅,PK⁆ = κ.imageSpace E.V₅ := by
    rw [commutator_comm,κ.imageSpace_commutator PK E.V₅ (inf_le_right.trans c.le_H) hSU,
      subspaceCommutator_comp_map]
    exact S.original_selectedComponent_cubic_seed_image
      D hZ z hz hTV hTz hbound hH hn c a hTI hns P (W := W) σ κ
  change ⁅E.V₅,PK⁆ ⊔ E.V₁ = E.V₅
  apply le_antisymm (sup_le hCS E.V₁_le_V₅)
  conv_lhs => rw [←κ.subspacePreimage_imageSpace E.V₅ hSU E.V₁_le_V₅]
  apply κ.subspacePreimage_le_of_imageSpace_le _ _ le_sup_right
  rw [κ.imageSpace_sup_kernel _ (hCS.trans hSU),him]

include hz hTV hTz hbound hH hn a in
theorem SourceHypothesis.original_selectedComponent_cubic_module_commutator
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    ⁅V,PK⁆ = ⁅E.V₅,PK⁆ ∧
      ⁅V,PK⁆ ⊔ E.V₁ = E.V₅ ∧ ⁅V,PK⁆ ⊓ E.V₁ = ⊥ ∧
      IsElementaryAbelian 2 (⁅V,PK⁆ : Subgroup G) ∧
      Nat.card (⁅V,PK⁆ : Subgroup G) = 16 := by
  let E := D.fullSetup hZ T z
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hPL : PK ≤ E.L₁ := inf_le_left.trans (map_subtype_le _)
  have hPH : PK ≤ H := inf_le_right.trans c.le_H
  have hPN : PK ≤ normalizer (E.V₅ : Set G) := hPL.trans (le_sup_left.trans h.local_normalizes)
  have hPV : PK ≤ normalizer (V : Set G) :=
    (hPL.trans ((map_subtype_le _).trans inf_le_left)).trans S.chosen.normalizes
  have hp : IsPGroup 3 PK := (P.isPGroup'.map E.L₁.subtype).to_le inf_le_left
  have hc := IsPGroup.coprime_card_of_ne 3 2 (by decide) PK V hp
    (IsElementaryAbelian.isPGroup 2 V)
  have hid := commutator_closure_coprime_idempotent V (PK : Set G)
    (by simpa only [closure_eq] using hPV)
    (fun x hx => hc.of_dvd_left (PK.orderOf_dvd_natCard hx))
  simp only [closure_eq] at hid
  have hCS : ⁅V,PK⁆ ≤ E.V₅ := commutator_le_of_normalized_index_two
    V E.V₅ PK E.V₅_le (E.perpendicular_index hz) hPV hPN
  have he : ⁅V,PK⁆ = ⁅E.V₅,PK⁆ := le_antisymm
    (hid.ge.trans (commutator_mono hCS le_rfl)) (commutator_mono E.V₅_le le_rfl)
  have hsup : ⁅V,PK⁆ ⊔ E.V₁ = E.V₅ := he ▸
    S.original_selectedComponent_cubic_seed_sup D hZ z hz hTV hTz hbound hH hn c a hTI hns P
  have hZC : E.V₁ ≤ V ⊓ centralizer (PK : Set G) :=
    le_inf (E.V₁_le_V₅.trans E.V₅_le) (le_centralizer_iff.mp (hPH.trans h.H_centralizes))
  have hinf : ⁅V,PK⁆ ⊓ E.V₁ = ⊥ := bot_unique
    ((inf_le_inf_left _ hZC).trans (commutator_disjoint_centralizer_of_coprime V PK hPV hc).eq_bot.le)
  have hnorm : E.V₁ ≤ normalizer (⁅V,PK⁆ : Subgroup G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    apply (E.V₁_le_V₅.trans E.V₅_le).trans
    apply le_centralizer_iff.mp
    exact (hCS.trans E.V₅_le).trans
      (commutator_eq_bot_iff_le_centralizer.mp
        (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative V)))
  have hcount := card_mul_eq_card_inf_mul_card_sup_of_normalizes ⁅V,PK⁆ E.V₁ hnorm
  rw [hinf,hsup,card_bot,E.point_card hz,E.perpendicular_card hz] at hcount
  change Nat.card (⁅V,PK⁆ : Subgroup G) * 2 = 1 * 2^5 at hcount
  have hCV : ⁅V,PK⁆ ≤ V := hCS.trans E.V₅_le
  have helem : IsElementaryAbelian 2 (⁅V,PK⁆ : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion hCV) (inclusion_injective hCV)
  have hcard : Nat.card (⁅V,PK⁆ : Subgroup G) = 16 := by omega
  exact ⟨he,hsup,hinf,helem,hcard⟩

end CFSG.Quasithin.Chapter12.Section06
