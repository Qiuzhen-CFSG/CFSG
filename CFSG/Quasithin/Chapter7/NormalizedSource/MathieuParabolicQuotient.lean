module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrioMarking
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows.LocalActions
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# The original cocode pair in the parabolic two-core quotient

Native trio displacements fill the nine-dimensional pair factor B. This
proves B=[R,V] for the actual R=N_L(U)^∞, so the component commutator bound
places B in O₂(R). The original H normalizes R and contains its two-core,
hence B lies in O₂(H). Conjugating B by the original pair conjugator puts
all of P=O₂(I) there. Relative normality gives P=I∩O₂(H), with no assumption
that I is normal in H. The selected degree gives |V⁺|=4, and the first
isomorphism theorem marks I/P with its literal image in H/O₂(H).

NonFFSourceMathieuM24Quotient supplies these premises on the original
chosen pair. Source: Aschbacher--Smith, 8.2.8--9, printed pp.718--720,
refs/quasithin.pdf; the native calculation is H.15.6, printed p.401.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
variable {G : Type*} [Group G] [Finite G]

/-- Native trio displacements generate the entire marked pair factor. -/
theorem pair_factor_eq_commutator (W R B : Subgroup G) [IsElementaryAbelian 2 W]
    (hBW : B ≤ W) (hRW : R ≤ normalizer (W : Set G))
    (hcomm : ⁅R,W⁆ ≤ B) (hdim : rank B = 9)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (f : R →* trioStabilizer standardTrio)
    (hf : f.range = solvableResidual (trioStabilizer standardTrio))
    (hF : ∀ (r : R) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨r,hRW r.property⟩ w)) =
        cocodeRepresentation (f r).val (F (Additive.ofMul w))) :
    B = ⁅R,W⁆ := by
  have hmark := pair_space_marking W R B hBW hRW hcomm hdim F f hf hF
  have hCW : ⁅R,W⁆ ≤ W := hcomm.trans hBW
  let : IsElementaryAbelian 2 (⁅R,W⁆ : Subgroup G) := IsElementaryAbelian.of_le hCW
  let j : Additive (⁅R,W⁆ : Subgroup G) →ₗ[ZMod 2] Cocode := F.toLinearMap.comp
    ((inclusion hCW).toAdditive.toZModLinearMap 2)
  have hle : standardPairSpace ≤ j.range := by
    change (⨆ C ∈ standardTrio.parts, supportedPairSpace C) ≤ j.range
    rw [standard_pairSpace_eq_residual_commutator]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,⟨t,ht,rfl⟩,v,_,rfl⟩
    rw [←hf] at ht
    obtain ⟨r,hr⟩ := ht
    obtain ⟨w,rfl⟩ := F.surjective v
    let z : (⁅R,W⁆ : Subgroup G) := ⟨⁅r.val,w.toMul.val⁆,
      commutator_mem_commutator r.property w.toMul.property⟩
    refine ⟨Additive.ofMul z,?_⟩
    have hz : (inclusion hCW z : W) =
        W.normalizerMonoidHom ⟨r,hRW r.property⟩ w.toMul / w.toMul := by
      apply Subtype.ext
      simp only [z,commutatorElement_def,div_eq_mul_inv]
      rfl
    change F (Additive.ofMul (inclusion hCW z)) = _
    rw [hz]
    change F (Additive.ofMul (W.normalizerMonoidHom ⟨r,hRW r.property⟩ w.toMul) - w) = _
    rw [map_sub,hF,hr]
    rfl
  apply le_antisymm _ hcomm
  intro b hb
  obtain ⟨c,hc⟩ := hle ((hmark ⟨b,hBW hb⟩).mp hb)
  have he : inclusion hCW c.toMul = ⟨b,hBW hb⟩ := F.injective hc
  have he' : (c.toMul : G) = b := congrArg Subtype.val he
  exact he' ▸ c.toMul.property

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
open ChapterE Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve
variable {G : Type*} [Group G] [Finite G]

/-- The selected degree is the literal index of the pair core in V. -/
theorem selected_two_core_index
    {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 2 i S) :
    (V ⊓ I.pCoreIn 2).relIndex V = 4 := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  let := s.twoConjugate.elementary
  let : IsElementaryAbelian 2 (coreImage I V) := IsElementaryAbelian.map _
  have hc : Nat.card (coreImage I V) = 2 ^ rank (coreImage I V) := by
    obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 (coreImage I V)).exists_card_eq
    rw [rank,hd,Nat.log_pow Nat.one_lt_two]
  rw [s.rank_eq] at hc
  change Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 4 at hc
  rw [←relIndex_ker,QuotientGroup.ker_mk'] at hc
  have hm := relIndex_map_map_of_injective (pCore 2 I) (V.subgroupOf I) I.subtype_injective
  rw [map_subgroupOf_eq_of_le hVI] at hm
  rw [inf_relIndex_left]
  exact hm.trans hc

/-- The original conjugate factors give the full kernel of I in H/O₂(H). -/
theorem selected_two_pair_core_in_hstar_core
    {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 2 i S)
    (hB : V ⊓ I.pCoreIn 2 ≤ H.pCoreIn 2) :
    I.pCoreIn 2 = I ⊓ H.pCoreIn 2 := by
  have hIP : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPi : (I.pCoreIn 2).map (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hIP (I.inv_mem i.property))
  have hpair : (V ⊓ I.pCoreIn 2) ⊔ (V ⊓ I.pCoreIn 2).map
      (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2 := by
    rw [map_inf _ _ _ (MulAut.conj i.val⁻¹).injective,hPi]
    exact (selected_two_core_product s).symm
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hQi : (H.pCoreIn 2).map (MulAut.conj i.val⁻¹).toMonoidHom = H.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hHQ (H.inv_mem (s.family.le_ambient i.property)))
  have hPQ : I.pCoreIn 2 ≤ H.pCoreIn 2 := by
    rw [←hpair]
    exact sup_le hB ((map_mono hB).trans_eq hQi)
  refine le_antisymm (le_inf (pCoreIn_le 2 I) hPQ) ?_
  rw [inf_comm]
  exact pCoreIn_inf_le_of_normalizes (s.family.le_ambient.trans H.le_normalizer)

/-- Identify I/O₂(I) with its literal image in H/O₂(H), preserving every representative. -/
theorem selected_two_pair_core_quotient
    {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 2 i S)
    (hB : V ⊓ I.pCoreIn 2 ≤ H.pCoreIn 2) :
    ∃ e : (I ⧸ pCore 2 I) ≃*
        ((I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))),
      ∀ x : I, (e (QuotientGroup.mk' (pCore 2 I) x)).val =
        QuotientGroup.mk' (pCore 2 H) (inclusion s.family.le_ambient x) := by
  have hcore := selected_two_pair_core_in_hstar_core s hB
  let J := (I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  let f : I →* J := ((QuotientGroup.mk' (pCore 2 H)).comp
    (inclusion s.family.le_ambient)).codRestrict J
      (fun x => mem_map_of_mem _ x.property)
  have hf : Function.Surjective f := by
    rintro ⟨y,a,ha,rfl⟩
    exact ⟨⟨a,ha⟩,rfl⟩
  have hk : f.ker = pCore 2 I := by
    ext x
    change (⟨QuotientGroup.mk' (pCore 2 H) (inclusion s.family.le_ambient x),_⟩ : J) = 1 ↔ _
    rw [Subtype.ext_iff]
    change ((inclusion s.family.le_ambient x : H) : H ⧸ pCore 2 H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    have hI : x ∈ pCore 2 I ↔ (x : G) ∈ I.pCoreIn 2 := by
      change x ∈ pCore 2 I ↔ I.subtype x ∈ (pCore 2 I).map I.subtype
      exact (mem_map_iff_mem (f := I.subtype) I.subtype_injective).symm
    have hH : inclusion s.family.le_ambient x ∈ pCore 2 H ↔ (x : G) ∈ H.pCoreIn 2 := by
      exact (mem_map_iff_mem (f := H.subtype) H.subtype_injective).symm
    rw [hI,hH,hcore]
    exact (and_iff_right x.property).symm
  let e : (I ⧸ pCore 2 I) ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨e,fun _ => rfl⟩


/-- The source parabolic has the same kernel on V as the selected pair. -/
theorem selected_two_hstar_core_intersection
    {V H M I L U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 2 i S)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hcomm : ⁅Chapter8.Section02.Normalizer.localResidual L U,centralizer (U : Set G)⁆ ≤
      (Chapter8.Section02.Normalizer.localResidual L U).pCoreIn 2)
    (hspan : V ⊓ I.pCoreIn 2 = ⁅Chapter8.Section02.Normalizer.localResidual L U,V⁆) :
    V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2 ∧
      Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 4 ∧
      I.pCoreIn 2 = I ⊓ H.pCoreIn 2 := by
  let R := Chapter8.Section02.Normalizer.localResidual L U
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hgen := selected_generates_hstar s hH
  have hHR : H ≤ normalizer (R : Set G) :=
    normalizes_localResidual_of_generation L H I T U hgen hIC hTL hTU hcomm
  have hHQ : H ≤ normalizer (R.pCoreIn 2 : Set G) :=
    hHR.trans (normalizer_le_normalizer_characteristic_image R (pCore 2 R))
  have hQT : R.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 R).le_sylow_of_normalized T (hH.1.1.2.trans hHQ)
  have hQH : R.pCoreIn 2 ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 R) (hQT.trans hH.1.1.2) hHQ
  have hB : V ⊓ I.pCoreIn 2 ≤ H.pCoreIn 2 := by
    rw [hspan]
    exact ((commutator_mono le_rfl (hVI.trans hIC)).trans hcomm).trans hQH
  have hback : V ⊓ H.pCoreIn 2 ≤ V ⊓ I.pCoreIn 2 := by
    apply le_inf inf_le_left
    exact (le_inf inf_le_right (inf_le_left.trans hVI)).trans
      (pCoreIn_inf_le_of_normalizes (s.family.le_ambient.trans H.le_normalizer))
  have he := le_antisymm (le_inf inf_le_left hB) hback
  refine ⟨he,?_,selected_two_pair_core_in_hstar_core s hB⟩
  rw [←relIndex_ker,QuotientGroup.ker_mk']
  have hm := relIndex_map_map_of_injective (pCore 2 H) (V.subgroupOf H) H.subtype_injective
  rw [map_subgroupOf_eq_of_le (hVI.trans s.family.le_ambient)] at hm
  rw [←hm,←inf_relIndex_left]
  change (V ⊓ H.pCoreIn 2).relIndex V = 4
  rw [←he]
  exact selected_two_core_index s

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
