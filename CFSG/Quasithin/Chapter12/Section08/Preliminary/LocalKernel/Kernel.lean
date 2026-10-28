module
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.LocalKernel.Closure
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.Core
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PCoreRestriction

/-!
# The faithful local quotient in 12.8.4(4)

The kernel acts trivially on V/V₁, so preserves the binary flag. Its two-residual
therefore centralizes V. The centralizer and uniqueness inputs force its
normalizer into M, contradicting the defining escape of H_z.

Source: Aschbacher--Smith, Lemma 12.8.4(4), printed p.850.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- Kernel elements preserve every original flag member, including the zero node. -/
theorem localKernel_normalizes_flag (J : Subgroup G) (hJ : J ≤ F.H) (i : ℕ) :
    (F.localTildeAction J hJ).ker.map J.subtype ≤ normalizer (F.Vi i : Set G) := by
  apply le_normalizer_iff.mpr
  rintro k ⟨k, hk, rfl⟩ a ha
  change (k : G) * a * (k : G)⁻¹ ∈ F.Vi i
  by_cases hi : i = 0
  · have hzero : F.Vi i = ⊥ := by
      apply eq_bot_of_card_eq
      simpa [hi] using F.card 0 (Nat.zero_le n)
    simpa [hzero] using ha
  · have hc := (F.mem_localTildeAction_ker_iff J hJ k).mp hk a
      (le_conjugateSpanBy V J (F.le_seed i ha))
    have hp := F.monotone (by omega : 1 ≤ i) hc
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using
      (F.Vi i).mul_mem hp ha

/-- Two-perfectness kills the kernel's action on the entire binary flag. -/
theorem localKernel_residual_centralizes (J : Subgroup G) (hJ : J ≤ F.H) :
    let C := (F.localTildeAction J hJ).ker.map J.subtype
    (pResidual 2 C).map C.subtype ≤ centralizer (V : Set G) := by
  let C := (F.localTildeAction J hJ).ker.map J.subtype
  have hCV : C ≤ normalizer (V : Set G) := F.last ▸ F.localKernel_normalizes_flag J hJ n
  let f : C →* MulAut V := V.normalizerMonoidHom.comp (inclusion hCV)
  have hf (c : C) : f c ∈ F.binaryFullFlag := by
    intro i v
    exact (mem_normalizer_iff.mp (F.localKernel_normalizes_flag J hJ i c.property) (v : G)).symm
  let q : C →* F.binaryFullFlag := f.codRestrict F.binaryFullFlag hf
  have hz := (isPPerfect_pResidual (G := C) 2).hom_eq_one_of_isPGroup
    F.binaryFullFlag_isPGroup (q.comp (pResidual 2 C).subtype)
  change (pResidual 2 C).map C.subtype ≤ centralizer (V : Set G)
  rintro y ⟨c, hc, rfl⟩
  intro v hv
  have he := congrArg (fun a : F.binaryFullFlag => ((a : MulAut V) ⟨v, hv⟩ : G))
    (DFunLike.congr_fun hz ⟨c, hc⟩)
  change (c : G) * v * (c : G)⁻¹ = v at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

omit [Finite G] [IsElementaryAbelian 2 V] in
/-- The ambient Sylow contains O₂(L), since it normalizes L. -/
theorem localKernel_L_core_le_T (L : Subgroup G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) : L.pCoreIn 2 ≤ (T : Subgroup G) := by
  let Q := L.pCoreIn 2
  let LT := L ⊔ (T : Subgroup G)
  have hQLT : Q ≤ LT := (pCoreIn_le 2 L).trans le_sup_left
  have hn : LT ≤ normalizer (Q : Set G) :=
    (sup_le L.le_normalizer hTL).trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  let : (Q.subgroupOf LT).Normal := (normal_subgroupOf_iff_le_normalizer hQLT).mpr hn
  have hp : IsPGroup 2 (Q.subgroupOf LT) := (pCore_isPGroup.map L.subtype).comap_subtype
  have hh := map_mono (f := LT.subtype) (hp.le_sylow_of_normal (T.subtype le_sup_right))
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hQLT,
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ LT from le_sup_right)] using hh

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem localKernel_core_ne_bot (J Y : Subgroup G) (hYJ : Y ≤ J)
    (hJY : J ≤ normalizer (Y : Set G)) (hchar : HasCharacteristicTwo J) (hne : Y ≠ ⊥) :
    pCore 2 Y ≠ ⊥ := by
  intro he
  have hYcore : Y ⊓ J.pCoreIn 2 ≤ Y.pCoreIn 2 := inf_pCoreIn_le_of_le 2 hYJ
  have hinf : Y ⊓ J.pCoreIn 2 = ⊥ := by
    apply le_bot_iff.mp
    simpa only [pCoreIn, he, Subgroup.map_bot] using hYcore
  have hcomm : ⁅Y, J.pCoreIn 2⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hinf]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp ((pCoreIn_le 2 J).trans hJY))
      (le_normalizer_iff_commutator_le_right.mp
        (hYJ.trans (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))))
  have hYQ : Y ≤ J.pCoreIn 2 := by
    intro y hy
    have hyc : (⟨y, hYJ hy⟩ : J) ∈ centralizer (pCore 2 J : Set J) := by
      intro q hq
      exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hy q
        (mem_map_of_mem J.subtype hq))
    exact mem_map_of_mem J.subtype (hchar hyc)
  exact hne (le_bot_iff.mp (hinf ▸ le_inf le_rfl hYQ))

/-- Ambient uniqueness eliminates the two-residual of the actual kernel. -/
theorem localKernel_residual_eq_bot {K : GroupClass} (hG : IsSimpleQTKE K G)
    (L M J : Subgroup G) (hJ : J ∈ F.Hz L M)
    (hLV : L ≤ normalizer (V : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hM : M = normalizer (L : Set G))
    (hunique : {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} = {M})
    (hCV : centralizer (V : Set G) ≤ M)
    (hCL : L ⊓ centralizer (V : Set G) = L.pCoreIn 2) :
    let C := (F.localTildeAction J hJ.2.1).ker.map J.subtype
    (pResidual 2 C).map C.subtype = ⊥ := by
  let C := (F.localTildeAction J hJ.2.1).ker.map J.subtype
  let Y := (pResidual 2 C).map C.subtype
  let Q := L.pCoreIn 2
  have hCJ : C ≤ J := map_subtype_le _
  have hJC : J ≤ normalizer (C : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (F.localTildeAction J hJ.2.1).ker.le_normalizer_map J.subtype
  have hYJ : Y ≤ J := (map_subtype_le _).trans hCJ
  have hJY : J ≤ normalizer (Y : Set G) := hJC.trans
    (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  have hYC : Y ≤ centralizer (V : Set G) := F.localKernel_residual_centralizes J hJ.2.1
  have hYL : Y ≤ normalizer (L : Set G) := hM ▸ hYC.trans hCV
  have hcomm : ⁅Y, L⁆ ≤ Q := by
    change ⁅Y, L⁆ ≤ L.pCoreIn 2
    rw [← hCL]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp hYL)
      ((commutator_mono hYC le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (hLV.trans (normalizer_le_normalizer_centralizer V))))
  have hTJ : (T : Subgroup G) ≤ J := fun x hx => hJ.1.2 (Or.inr hx)
  have hQY : Q ≤ normalizer (Y : Set G) :=
    (localKernel_L_core_le_T (T := T) L hTL).trans (hTJ.trans hJY)
  have hres : (pResidual 2 (Y ⊔ Q : Subgroup G)).map (Y ⊔ Q).subtype = Y :=
    embedded_pResidual_join_pGroup Y Q (isPPerfect_embedded_pResidual 2 C)
      (pCore_isPGroup.map L.subtype) hQY
  have hLQ : L ≤ normalizer (Q : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hLsup : L ≤ normalizer ((Y ⊔ Q : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl x hx
    have hmap : Y ⊔ Q ≤ (Y ⊔ Q).comap (MulAut.conj l).toMonoidHom := by
      apply sup_le
      · intro y hy
        have hc : ⁅l, y⁆ ∈ Q := by
          rw [commutator_comm] at hcomm
          exact hcomm (commutator_mem_commutator hl hy)
        change l * y * l⁻¹ ∈ Y ⊔ Q
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using
          (Y ⊔ Q).mul_mem ((show Q ≤ Y ⊔ Q from le_sup_right) hc)
            ((show Y ≤ Y ⊔ Q from le_sup_left) hy)
      · exact fun q hq => (show Q ≤ Y ⊔ Q from le_sup_right)
          (le_normalizer_iff.mp hLQ l hl q hq)
    exact hmap hx
  have hLY : L ≤ normalizer (Y : Set G) := by
    rw [← hres]
    exact hLsup.trans (normalizer_le_normalizer_characteristic_image (Y ⊔ Q) (pResidual 2 (Y ⊔ Q : Subgroup G)))
  by_contra hne
  obtain ⟨N, hN, hYN⟩ := exists_twoLocal_overgroup_normalizer Y (pCore 2 Y)
    (localKernel_core_ne_bot J Y hYJ hJY (F.localKernel_characteristicTwo hG L M J hJ) hne)
    pCore_isPGroup
  obtain ⟨R, hNR, hR⟩ := Finite.exists_le_maximal hN
  have hLR : L ⊔ (T : Subgroup G) ≤ R :=
    (sup_le hLY (hTJ.trans hJY)).trans (hYN.trans hNR)
  have he : R = M := Set.mem_singleton_iff.mp (hunique ▸ (show R ∈
    {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} from ⟨hR, hLR⟩))
  exact hJ.2.2 (he ▸ hJY.trans (hYN.trans hNR))
/-- Source 12.8.4(4), for the actual quotient representation of every J∈H_z. -/
theorem localKernel_eq_pCore {K : GroupClass} (hG : IsSimpleQTKE K G)
    (L M J : Subgroup G) (hn : 2 ≤ n)
    (hVT : V ≤ (T : Subgroup G)) (hLV : L ≤ normalizer (V : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hres : pResidual 2 L = ⊤)
    (hnatural : 3 ≤ n → Nonempty (AmbientNaturalMarking L hLV n))
    (hM : M = normalizer (L : Set G))
    (hunique : {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} = {M})
    (hCV : centralizer (V : Set G) ≤ M)
    (hCL : L ⊓ centralizer (V : Set G) = L.pCoreIn 2)
    (hJ : J ∈ F.Hz L M) :
    (F.localTildeAction J hJ.2.1).ker = pCore 2 J := by
  apply le_antisymm _ (F.localKernel_core_le hG L M J hn hVT hLV hTL hres hnatural hJ)
  let C := (F.localTildeAction J hJ.2.1).ker.map J.subtype
  have he : pResidual 2 C = ⊥ :=
    ((pResidual 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp
      (F.localKernel_residual_eq_bot hG L M J hJ hLV hTL hM hunique hCV hCL)
  have hp : IsPGroup 2 C := by
    have hq := isPGroup_quotient_pResidual (G := C) 2
    exact hq.of_equiv ((QuotientGroup.quotientMulEquivOfEq he).trans
      (QuotientGroup.quotientBot))
  have hk : IsPGroup 2 (F.localTildeAction J hJ.2.1).ker :=
    hp.of_equiv ((F.localTildeAction J hJ.2.1).ker.equivMapOfInjective J.subtype J.subtype_injective).symm
  exact le_sSup ⟨inferInstance, hk⟩
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
