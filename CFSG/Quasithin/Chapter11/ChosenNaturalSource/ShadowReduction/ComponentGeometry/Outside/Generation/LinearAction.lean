module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.LinearAction.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.HallOrder
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Attainment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core.Point

/-!
# Generation one in the original SL₃ equal-component row

The proved natural equivalence on V and an actual conjugator for the
caller's flag identify the image of L₁ with the standard point residual.
Its two-core maps into the actual root plane. Thus the odd-action theorem
applies to the full Hall actor constructed by E.2.2. Its order is coprime
to q−1 by HallOrder, so it fixes V. Hall faithfulness makes it trivial,
contradicting its cyclic subgroup of order 2ⁿ−1 when n>1.

This proves n(H)=1 for every outside H in the linear K=L₁ row, including
q=4 and the full center of SL₃, and gives the original selected-H consumer
with the literal O²(H) alternatives. The exact OddKernelNormalizer premise
is used only for faithfulness; qt-d-1222-natural-odd-kernel-normalizer must
still supply it. The earlier geometry, 11.3.2 and component equality retain
qt-d-1222-natural-local-geometry, qt-d-1222-shadow-linear-geometry,
qt-d-1222-shadow-component-triangle and
qt-d-1222-shadow-component-comparison as producers. Their final discharge
belongs to qt-d-1222-shadow-components.

The symplectic, G₂, strict-component and smaller-carrier generation steps
remain with qt-d-1222-shadow-component-witness. This module does not assert
the complete 11.4.4 or 11.5.1.
Source: Aschbacher--Smith, 11.4.4 and the selection following 11.5.1,
printed pp.778--779 of refs/quasithin.pdf.
-/

public noncomputable section

open Subgroup Matrix Representation Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
open Matrix.PSL3.LinearThree
open LocalGeometry
open LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m))

private theorem map_core_le {A B : Type*} [Group A] [Group B]
    (q : A →* B) (P : Subgroup A) : (P.pCoreIn 2).map q ≤ (P.map q).pCoreIn 2 := by
  let j := q.subgroupMap P
  have hn : ((pCore 2 P).map j).Normal := Normal.map inferInstance j (q.subgroupMap_surjective P)
  have h : (pCore 2 P).map j ≤ pCore 2 (P.map q) := le_sSup ⟨hn,pCore_isPGroup.map j⟩
  have hh := map_mono (f := (P.map q).subtype) h
  change ((pCore 2 P).map j).map (P.map q).subtype ≤ (P.map q).pCoreIn 2 at hh
  rw [Subgroup.map_map] at hh
  change (pCore 2 P).map (q.comp P.subtype) ≤ _ at hh
  change ((pCore 2 P).map P.subtype).map q ≤ _
  rw [Subgroup.map_map]
  exact hh

/-- Coprime odd actors centralizing the original SL₃ point section fix V. -/
theorem ofFlag_sl3_odd_section_centralizes
    (B : Subgroup G) (ho : Odd (Nat.card B))
    (hBV : B ≤ normalizer (V : Set G))
    (hc : ⁅B,f.Li 0⁆ ≤ (f.Li 0).pCoreIn 2)
    (hco : Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1)) :
    B ≤ centralizer (V : Set G) := by
  obtain ⟨a,ha⟩ := Matrix.PSL3.PointRadicalGeneration.exists_standardPoint_conjugator
    (f.space 0) (f.dimension 0)
  let e : V ≃* Multiplicative (Fin 3 → S.field.Carrier) :=
    (SL3.naturalEquiv D S m).trans (naturalAut a)
  let N := normalizer (V : Set G)
  let q : N →* MulAut (Multiplicative (Fin 3 → S.field.Carrier)) :=
    (MulAut.congr e).toMonoidHom.comp V.normalizerMonoidHom
  let P := (f.Li 0).subgroupOf N
  have hAL : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  have hAN : f.Li 0 ≤ N := hAL.trans D.normalizes
  have hq (l : L) : q (inclusion D.normalizes l) =
      naturalAut ((MulAut.conj a) ((Coordinates.sl3 m).quotientMap l)) := by
    apply MulEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    change e (V.normalizerMonoidHom (inclusion D.normalizes l) (e.symm (e v))) = _
    rw [e.symm_apply_apply]
    have hh := SL3.naturalEquiv_conjugation D S m l v
    apply Multiplicative.toAdd.injective
    change a.val *ᵥ (SL3.naturalEquiv D S m
      (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd =
        (a * (show SL(3,S.field.Carrier) from (Coordinates.sl3 m).quotientMap l) * a⁻¹).val *ᵥ
          (a.val *ᵥ (SL3.naturalEquiv D S m v).toAdd)
    rw [hh]
    change (naturalAut a) ((naturalAut ((Coordinates.sl3 m).quotientMap l))
      (SL3.naturalEquiv D S m v)) =
      naturalAut (a * (show SL(3,S.field.Carrier) from (Coordinates.sl3 m).quotientMap l) * a⁻¹)
        ((naturalAut a) (SL3.naturalEquiv D S m v))
    simp only [map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply_self]
    exact (congrArg (fun u : MulAut (Multiplicative (Fin 3 → S.field.Carrier)) =>
      u (SL3.naturalEquiv D S m v))
      (map_mul naturalAut a ((Coordinates.sl3 m).quotientMap l))).symm
  have hPQ : P.map q = (pointLocalSL S.field.Carrier).map naturalAut := by
    have hcomp : P.map q = ((componentImage D S m (f.Li 0)).map
        (MulAut.conj a).toMonoidHom).map naturalAut := by
      ext u
      constructor
      · rintro ⟨x,hx,rfl⟩
        refine ⟨_,⟨(Coordinates.sl3 m).quotientMap ⟨x,hAL hx⟩,⟨⟨x,hAL hx⟩,hx,rfl⟩,rfl⟩,?_⟩
        exact (hq ⟨x,hAL hx⟩).symm
      · rintro ⟨_,⟨_,⟨l,hl,rfl⟩,rfl⟩,rfl⟩
        exact ⟨inclusion D.normalizes l,hl,hq l⟩
    rw [hcomp,componentImage_residual_conjugate D S m f a ha]
    apply congrArg (Subgroup.map naturalAut)
    have he : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change a * (a⁻¹ * x * (a⁻¹)⁻¹) * a⁻¹ = x
      group
    rw [Subgroup.map_map,he,Subgroup.map_id]
  have hcore : (((f.Li 0).pCoreIn 2).subgroupOf N).map q ≤
      ((pointRadicalSL S.field.Carrier).map (pointLocalSL S.field.Carrier).subtype).map naturalAut := by
    rw [← pCoreIn_subgroupOf 2 (f.Li 0) N hAN]
    exact (map_core_le q P).trans_eq (hPQ ▸ pointLocal_additive_core)
  intro b hb
  let b' : N := ⟨b,hBV hb⟩
  have hpow : q b' ^ Nat.card B = 1 := by
    rw [←map_pow]
    have hbpow : b ^ Nat.card B = 1 :=
      congrArg (fun x : B => (x : G)) (pow_card_eq_one' (x := (⟨b,hb⟩ : B)))
    have he : b' ^ Nat.card B = 1 := Subtype.ext hbpow
    rw [he,map_one]
  have hcomm : ∀ g ∈ pointLocalSL S.field.Carrier, ⁅q b',naturalAut g⁆ ∈
      ((pointRadicalSL S.field.Carrier).map (pointLocalSL S.field.Carrier).subtype).map naturalAut := by
    intro g hg
    obtain ⟨x,hx,he⟩ := hPQ.ge (mem_map_of_mem naturalAut hg)
    rw [←he,←map_commutatorElement]
    exact hcore (mem_map_of_mem q (show ⁅b',x⁆ ∈ ((f.Li 0).pCoreIn 2).subgroupOf N from
      hc (commutator_mem_commutator hb hx)))
  have hb1 : q b' = 1 := LinearAction.odd_coprime_point_section_eq_one (q b') ho
    (S.field.card_eq.symm ▸ hco) hpow hcomm
  have hv1 : V.normalizerMonoidHom b' = 1 :=
    (MulAut.congr e).injective (hb1.trans (map_one _).symm)
  intro v hv
  have hh := congrArg (fun u : MulAut V => (u ⟨v,hv⟩ : G)) hv1
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- Source 11.4.4 for every outside H in the original linear equality row.
Only the independently owned Hall-faithfulness input remains explicit. -/
theorem ofFlag_sl3_equal_generation_eq_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H)) : ChapterE.generationParameter H = 1 := by
  apply Nat.le_antisymm ?_ (selected_generation_spec (ofFlag S f X z H) h hH hHz).1
  change ChapterE.generationParameter H ≤ 1
  by_contra! hn
  obtain ⟨hP,n,_,hb,d,_,_,hY,hfaith,hBV,hcop⟩ :=
    ofFlag_sl3_equal_faithful_hall_order S m f X z H h he hK hcontrol hH hHz hn
  have hc : ⁅d.witness.abelianGroup.map H.subtype,f.Li 0⁆ ≤ (f.Li 0).pCoreIn 2 := by
    have hc := commutator_le.mpr (fun b hb k hk =>
      Closure.coreQuotientCentralizer_commutator (hY hb).2 hk)
    simpa only [hK,ofFlag_firstResidual] using hc
  have hfix := ofFlag_sl3_odd_section_centralizes S m f _
    (d.witness.odd.of_dvd_nat (card_map_dvd _ _)) hBV hc hcop
  have hz : d.witness.abelianGroup.map H.subtype = ⊥ := by
    rwa [inf_eq_left.mpr hfix] at hfaith
  have hB : d.witness.abelianGroup = ⊥ :=
    (map_eq_bot_iff_of_injective _ H.subtype_injective).mp hz
  have hC : d.witness.cyclicGroup = ⊥ := bot_unique (d.witness.cyclic_le.trans hB.le)
  have hc1 := d.witness.card
  rw [Subgroup.card_eq_one.mpr hC] at hc1
  have hn2 : 2 ≤ n := by omega
  have hp : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn2
  omega

/-- The original selected H has generation one, with both residual alternatives
still interpreted as O²(H). The preceding geometry is retained verbatim. -/
theorem ofFlag_sl3_equal_selected_generation_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 := by
  obtain ⟨J,hJ,hJz,hs,_⟩ := ofFlag_equal_selected_radical_carrier S f X z H h he hK hNT h1132
  exact ⟨J,hJ,hJz,hs,ofFlag_sl3_equal_generation_eq_one S m f X z J
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩ he hK hcontrol hJ hJz⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
