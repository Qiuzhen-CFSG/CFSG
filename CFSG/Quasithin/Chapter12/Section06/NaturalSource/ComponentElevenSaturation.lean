module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentElevenSeed
public import Theory.Representation.BinaryOffender.CommutingPerfectSupports
public import Theory.Representation.BinaryOffender.InvolutionSubspaceDimension
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.ShortSeedPropagation
public import Theory.GroupTheory.Commutator.NormalSpan

/-!
# The cubic fixed part and movement of the original L-core

The commuting P_K-star and V-star exchange their mixed displacement.
The seed has dimension four, while the actual cubic displacement has
dimension at most eight. Rank-nullity identifies its V-star fixed part
with the seed. Lifting through U_H/V₁ bounds the intersection of the
cubic core commutator with O₂(L) by V₅.

Coprime idempotence gives [O₂(L),P_K]=[V,P_K]. The same cubic normally
generates the original perfect L with its marked A₈ quotient, hence
[O₂(L),L]=V. The final application selects the component internally.
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
/-- The fixed part of the actual cubic displacement is exactly the original seed image. -/
theorem SourceHypothesis.original_selectedComponent_cubic_fixed_space
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (hσ : Function.Injective σ)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    subspaceCommutator σ ⊤ (Nonabelian.Setup.star H PK) ⊓
      fixedSpace σ (Nonabelian.Setup.star H V) = κ.imageSpace E.V₅ := by
  let E := D.fullSetup hZ T z
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  let A := Nonabelian.Setup.star H PK
  let B := Nonabelian.Setup.star H V
  let I := κ.imageSpace E.V₅
  let C := subspaceCommutator σ ⊤ A
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hseed : subspaceCommutator σ ⊤ B = I :=
    (S.original_selectedComponent_whole_module D hZ z hz hTV hTz hbound hH hn c a hTI hns σ hσ κ).1.symm
  have hIA : subspaceCommutator σ I A = I :=
    S.original_selectedComponent_cubic_seed_image D hZ z hz hTV hTz hbound hH hn c a hTI hns P σ κ
  have hIC : I ≤ C := hIA.ge.trans (subspaceCommutator_mono_left σ le_top A)
  have hc : ∀ x ∈ A, ∀ b ∈ B, Commute x b := by
    intro x hx b hb
    exact (S.original_point_residual_star_centralizes D hZ z hz hTV hTz hbound hH hn
      (map_mono (comap_mono (inf_le_left.trans (map_subtype_le _))) hx) b hb).symm
  have hCB : subspaceCommutator σ C B = I := by
    rw [subspaceCommutator_swap_of_commute σ ⊤ A B hc,hseed,hIA]
  have hIF : I ≤ fixedSpace σ B := by
    intro v hv b
    obtain ⟨w,hw,rfl⟩ := (κ.mem_imageSpace_iff E.V₅ v).mp hv
    obtain ⟨u,hu,he⟩ := b.property
    change σ b.val (κ.coordinates w).toAdd = (κ.coordinates w).toAdd
    rw [←he]
    have hwu : (u:G)*(w:G)=(w:G)*(u:G) :=
      congrArg Subtype.val (mul_comm (⟨u,hu⟩ : V) ⟨w,E.V₅_le hw⟩)
    have heq := κ.equivariant u w
    have hcj : (⟨(u:G)*w*(u:G)⁻¹,
        (mem_normalizer_iff.mp (κ.normalized u.property) w).mp w.property⟩ : E.UH H) = w := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr hwu
    rw [hcj] at heq
    exact heq.symm
  have hidx : E.V₁.relIndex E.V₅ = 2^4 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (E.V₁.subgroupOf E.V₅)
    rw [Nat.card_congr (subgroupOfEquivOfLe E.V₁_le_V₅).toEquiv] at hh
    change Nat.card E.V₅ = E.V₁.relIndex E.V₅ * Nat.card E.V₁ at hh
    rw [E.perpendicular_card hz,E.point_card hz] at hh
    omega
  have hdI : Module.finrank (ZMod 2) I = 4 :=
    κ.imageSpace_finrank_of_index E.V₅ (le_conjugateSpanBy _ _) 4 hidx
  have hdC : Module.finrank (ZMod 2) C ≤ 8 :=
    S.original_selectedComponent_cubic_displacement D hZ z hz hTV hTz hbound hH hn c a hTI hns P σ κ
  have hr := card_two_moved_add_fixed_finrank σ B
    (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.1 C
  rw [hCB,hdI] at hr
  have hle : I ≤ C ⊓ fixedSpace σ B := le_inf hIC hIF
  have hdim := Submodule.finrank_mono hle
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

include hz hTV hTz hbound hH hn a in
/-- The cubic commutator meets the original L-core only in the marked perpendicular. -/
theorem SourceHypothesis.original_selectedComponent_cubic_core_intersection
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    ⁅E.L₁.pCoreIn 2,PK⁆ ⊓ L.pCoreIn 2 ≤ E.V₅ := by
  let E := D.fullSetup hZ T z
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  let C := ⁅E.UH H,PK⁆
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let _ : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
  let _ : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
  let W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))
  obtain ⟨σ,κ,hσ,_⟩ := h.faithful_point_quotient
  change Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W at σ
  change BinaryConjugationSection H (E.UH H) E.V₁
    (σ.comp (QuotientGroup.mk' (pCore 2 H))) at κ
  have hPH : PK ≤ H := inf_le_right.trans c.le_H
  have hCU : C ≤ E.UH H := le_normalizer_iff_commutator_le_left.mp (hPH.trans κ.normalized)
  have him : κ.imageSpace C = subspaceCommutator σ ⊤ (Nonabelian.Setup.star H PK) := by
    rw [show C = ⁅PK,E.UH H⁆ from commutator_comm _ _,κ.imageSpace_commutator PK (E.UH H) hPH le_rfl,
      κ.imageSpace_self,subspaceCommutator_comp_map]
    rfl
  change ⁅E.L₁.pCoreIn 2,PK⁆ ⊓ L.pCoreIn 2 ≤ E.V₅
  rw [S.original_selectedComponent_cubic_core_commutator D hZ z hz hTV hTz hbound hH hn c a hTI hns P]
  intro x hx
  have hxU : x ∈ E.UH H := hCU hx.1
  apply κ.subspacePreimage_le_of_imageSpace_le _ E.V₅ E.V₁_le_V₅ le_rfl
  apply (κ.mem_subspacePreimage _ x).mpr
  refine ⟨hxU,?_⟩
  rw [←S.original_selectedComponent_cubic_fixed_space D hZ z hz hTV hTz hbound hH hn c a hTI hns P σ hσ κ]
  constructor
  · rw [←him]
    exact (κ.mem_imageSpace_iff C _).mpr ⟨⟨x,hxU⟩,hx.1,rfl⟩
  · rintro ⟨b,⟨u,hu,rfl⟩⟩
    have hcentral : x ∈ centralizer (V : Set G) := S.centralizer_eq_core.ge hx.2 |>.2
    have he : (u:G)*x=x*(u:G) := mem_centralizer_iff.mp hcentral u hu
    have hcoords := κ.equivariant u ⟨x,hxU⟩
    have hcj : (⟨(u:G)*x*(u:G)⁻¹,
        (mem_normalizer_iff.mp (κ.normalized u.property) x).mp hxU⟩ : E.UH H) = ⟨x,hxU⟩ := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr he
    rw [hcj] at hcoords
    exact hcoords.symm

include hz hTV hTz hbound hH hn a in
/-- Cubic movement of the original L-core is precisely movement of V. -/
theorem SourceHypothesis.original_selectedComponent_cubic_original_core
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    ⁅L.pCoreIn 2,PK⁆ = ⁅V,PK⁆ := by
  let E := D.fullSetup hZ T z
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  let Q₀ := L.pCoreIn 2
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hL₁L : E.L₁ ≤ L := (map_subtype_le _).trans inf_le_left
  have hPL₁ : PK ≤ E.L₁ := inf_le_left.trans (map_subtype_le _)
  have hPL : PK ≤ L := hPL₁.trans hL₁L
  have hLQ : L ≤ normalizer (Q₀ : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hQLT : Q₀ ≤ Q T L := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  have hQH : Q₀ ≤ H := (hQLT.trans (Q_le_Tv S.chosen z)).trans (inf_le_left.trans h.T_le_H)
  have hQC : Q₀ ≤ centralizer (V : Set G) := S.centralizer_eq_core.ge.trans inf_le_right
  have hQL₁ : Q₀ ≤ normalizer (E.L₁ : Set G) :=
    (le_inf hQH (hQC.trans (Subgroup.centralizer_le_normalizer _))).trans
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  have hsmall : E.L₁ ⊓ Q₀ ≤ E.L₁.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 L).to_le inf_le_right)
      inf_le_left ((le_inf E.L₁.le_normalizer (hL₁L.trans hLQ)).trans inf_normalizer_le_normalizer_inf)
  have hQR : ⁅Q₀,PK⁆ ≤ E.L₁.pCoreIn 2 := (le_inf
    ((commutator_mono le_rfl hPL₁).trans (le_normalizer_iff_commutator_le_right.mp hQL₁))
    (le_normalizer_iff_commutator_le_left.mp (hPL.trans hLQ))).trans hsmall
  have hp : IsPGroup 3 PK := (P.isPGroup'.map E.L₁.subtype).to_le inf_le_left
  have hc := IsPGroup.coprime_card_of_ne 3 2 (by decide) PK Q₀ hp (isPGroup_pCoreIn 2 L)
  have hid := commutator_closure_coprime_idempotent Q₀ (PK : Set G)
    (by simpa only [closure_eq] using hPL.trans hLQ)
    (fun x hx => hc.of_dvd_left (PK.orderOf_dvd_natCard hx))
  simp only [closure_eq] at hid
  have hQS : ⁅Q₀,PK⁆ ≤ E.V₅ := (le_inf
    (hid.ge.trans (commutator_mono hQR le_rfl))
    (le_normalizer_iff_commutator_le_left.mp (hPL.trans hLQ))).trans
    (S.original_selectedComponent_cubic_core_intersection D hZ z hz hTV hTz hbound hH hn c a hTI hns P)
  have hVQ : V ≤ Q₀ := S.chosen.le_componentCore
  exact le_antisymm (hid.ge.trans (commutator_mono (hQS.trans E.V₅_le) le_rfl))
    (commutator_mono hVQ le_rfl)

include hz hTV hTz hbound hH hn a in
/-- The actual cubic normally generates L; its core movement propagates to the whole group. -/
theorem SourceHypothesis.original_selectedComponent_original_core_commutator
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ⁅L.pCoreIn 2,L⁆ = V := by
  let E := D.fullSetup hZ T z
  let P : Sylow 3 E.L₁ := Classical.choice inferInstance
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  have hPL : PK ≤ L := (inf_le_left.trans (map_subtype_le _)).trans
    ((map_subtype_le _).trans inf_le_left)
  let A := PK.subgroupOf L
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
  let : IsQuasisimple (L ⧸ pCore 2 L) := S.source.quasisimple
  have hp : IsPPerfect 2 L := (pResidual_eq_top_iff 2 L).mp (pResidual_eq_top_of_isPerfect 2)
  have hne : ¬ A.map (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L) := by
    intro hc
    have hcenter := D.coreQuotient_center_eq_bot S.chosen S.source.quasisimple
    have hA : A ≤ pCore 2 L := by
      simpa only [hcenter,le_bot_iff,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] using hc
    have hPK : IsPGroup 2 PK := (pCore_isPGroup.to_le hA).of_equiv (subgroupOfEquivOfLe hPL)
    have hcard : Nat.card PK = 3 := S.original_selectedComponent_sylow_intersection_card
      D hZ z hz hTV hTz hbound hH hn c a hTI hns P
    obtain ⟨n,hn⟩ := hPK.exists_card_eq
    rw [hcard] at hn
    have hd : 3 ∣ 2^n := by rw [←hn]
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hg := ChapterC.RankOne.GlaubermanArgument.normal_generation_of_noncentral_core_image A hp hne
  have hgen : conjugateSpanBy PK L = L := by
    have hm := congrArg (map L.subtype) hg
    simpa only [A,map_conjugateSpanBy,map_subgroupOf_eq_of_le hPL,←MonoidHom.range_eq_map,
      range_subtype] using hm
  have hLQ : L ≤ normalizer (L.pCoreIn 2 : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hmove : ⁅L.pCoreIn 2,PK⁆ ≤ V := by
    rw [S.original_selectedComponent_cubic_original_core D hZ z hz hTV hTz hbound hH hn c a hTI hns P]
    exact le_normalizer_iff_commutator_le_left.mp (hPL.trans S.chosen.normalizes)
  apply le_antisymm
  · rw [commutator_comm]
    conv_lhs => lhs; rw [←hgen]
    rw [commutator_conjugateSpanBy_of_normalized_right PK L (L.pCoreIn 2) hPL hLQ,
      commutator_comm PK (L.pCoreIn 2)]
    exact conjugateSpanBy_le hmove S.chosen.normalizes
  · rw [S.chosen.eq_commutator]
    exact commutator_mono S.chosen.le_componentCore le_rfl

include hz hTV hTz hbound hH hn in
/-- Source application: component selection is discharged before asserting
movement of the original intrinsic L-core. -/
theorem SourceHypothesis.original_nonabelian_point_span_original_core_commutator
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ⁅L.pCoreIn 2,L⁆ = V := by
  obtain ⟨c,_,_,⟨a⟩⟩ := S.original_selectedComponent_with_action
    D hZ z hz hTV hTz hbound hns hH hn
  exact S.original_selectedComponent_original_core_commutator
    D hZ z hz hTV hTz hbound hH hn c a hTI hns

end CFSG.Quasithin.Chapter12.Section06
