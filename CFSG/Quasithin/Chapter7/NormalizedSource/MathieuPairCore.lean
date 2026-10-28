module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCompatiblePair
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallCore
-- Internal continuation of the literal quotient/Sylow marking transport only.
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceLinearRanks

/-!
# The actual M24 selected pair and its two-core

The degree-two rank-one alternative is PSL2(4). Its marked Borel and Sylow
supply the native E.2 linear-core theorem, so the actual two-core is the
product of its intersections with the two original generators. The native
central quotient is the direct sum of two rank-six elementary factors.
Its order is 2^12, and adjoining the original central three-space gives
core order 2^15. The self-centralizing factor calculation identifies the
whole center, and the E.2 section-centralizer bound identifies the kernel
of I on its core modulo that same three-space.

The private import reuses the existing internal transport of the actual
quotient and Sylow markings; it introduces no public definition dependence.
NonFFSourceMathieuM24Core discharges every geometric input on the chosen
orbit, including construction of the compatible pair. Recognition of the
containing component and ambient J4 remain with qt-d-1222-nonff-mathieu.
Source: Aschbacher--Smith E.2.10(1,2,7), E.2.13(7), E.2.14(3) and 8.2.5--8,
printed pp.222--228,716--719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
open ChapterE Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {i : I} {S : Sylow 2 I}

/-- The literal quotient is PSL2(4); the Suzuki and dihedral degrees are excluded. -/
theorem selected_two_quotient (s : Selected H T M V I 2 i S) :
    Nonempty ((I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField 2)) := by
  rcases s.models with ⟨_,e,_⟩ | ⟨m,hm,hk,_,_⟩ | ⟨hk,_⟩
  · exact ⟨e⟩
  · omega
  · omega

private theorem selected_two_native_core (s : Selected H T M V I 2 i S) :
    TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹ = pCore 2 I := by
  obtain ⟨e⟩ := selected_two_quotient s
  obtain ⟨hMN,hVS,hMS⟩ := selected_linear_markings s e
  exact (s.twoConjugate.linear_pair_core_eq hMN 2 (by decide)
    (GaloisField.card 2 2 (by decide)) _ _ hVS hMS).symm

/-- The actual two-core is the join of its two original elementary factors. -/
theorem selected_two_core_product (s : Selected H T M V I 2 i S) :
    I.pCoreIn 2 = (V ⊓ I.pCoreIn 2) ⊔
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hb : (TwoConjugate.B (V.subgroupOf I) (M.subgroupOf I)).map I.subtype =
      V ⊓ I.pCoreIn 2 := by
    rw [s.twoConjugate.B_eq_twoCore_inf,map_inf _ _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hVI,inf_comm]
    rfl
  have hp := congrArg (fun D : Subgroup I => D.map I.subtype) (selected_two_native_core s)
  rw [TwoConjugate.P,Subgroup.map_sup,hb,selected_actor_image I M V hVI S i s.twoConjugate] at hp
  exact hp.symm

private theorem selected_two_native_section (s : Selected H T M V I 2 i S) :
    let := s.twoConjugate.Z_normal
    let q := QuotientGroup.mk' (TwoConjugate.Z (V.subgroupOf I) i⁻¹)
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
    IsElementaryAbelian 2 ((pCore 2 I).map q) ∧
      rank ((pCore 2 I).map q) = 2 * rank (inducedAutomizer V A) := by
  let := s.twoConjugate.Z_normal
  let q := QuotientGroup.mk' (TwoConjugate.Z (V.subgroupOf I) i⁻¹)
  have hp := selected_two_native_core s
  have he := s.twoConjugate.quotient_direct_sum.1
  rw [hp] at he
  let := he
  have hd : rank ((TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹).map q) =
      2 * Nat.log 2 ((TwoConjugate.Z (V.subgroupOf I) i⁻¹).relIndex
        (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹)) := by
    let := s.twoConjugate.quotient_direct_sum.1
    rw [rank,show Nat.card ((TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹).map q) =
      Nat.card (Additive ((TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹).map q)) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,Nat.log_pow Nat.one_lt_two]
    exact s.twoConjugate.quotient_core_finrank_eq_twice_actor
  rw [hp] at hd
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hi := relIndex_map_map_of_injective (f := I.subtype)
    (TwoConjugate.Z (V.subgroupOf I) i⁻¹)
    (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹) I.subtype_injective
  rw [selected_intersection_image I V hVI i,
    selected_actor_image I M V hVI S i s.twoConjugate] at hi
  have hcoreM : (pCore 2 I).map I.subtype ≤ M := by
    rintro _ ⟨a,ha,rfl⟩
    apply (M.subgroupOf I).normalCore_le
    change a ∈ localCore M I
    rwa [s.core_eq]
  have hAN : V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ≤
      normalizer (V : Set G) := inf_le_right.trans
    ((le_inf hcoreM (map_subtype_le _)).trans (s.normalizer_eq ▸ inf_le_right))
  have hr := rank_inducedAutomizer V
    (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype) hAN
  rw [selected_actor_kernel I M V hVI S i s.twoConjugate] at hr
  refine ⟨he,?_⟩
  change rank ((pCore 2 I).map q) = 2 * rank (inducedAutomizer V
    (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype))
  rw [hr,subgroupCorank,hi]
  exact hd

/-- The original central quotient has order 2^12 and its full core order 2^15. -/
theorem selected_two_core_section (s : Selected H T M V I 2 i S)
    {U : Subgroup G} (hUZ : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hIC : I ≤ centralizer (U : Set G)) (hu : rank U = 3)
    (ha : rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)) = 6) :
    ∃ _hU : (U.subgroupOf (I.pCoreIn 2)).Normal,
      IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ∧
      Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2^12 ∧
      Nat.card (I.pCoreIn 2) = 2^15 := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let P := I.pCoreIn 2
  have hPI : P ≤ I := pCoreIn_le 2 I
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  let Zi := TwoConjugate.Z (V.subgroupOf I) i⁻¹
  let := s.twoConjugate.Z_normal
  let q := QuotientGroup.mk' Zi
  let Q := (pCore 2 I).map q
  obtain ⟨helem,hrank⟩ := selected_two_native_section s
  let : IsElementaryAbelian 2 Q := helem
  change rank Q = 2 * rank (inducedAutomizer V A) at hrank
  change rank (inducedAutomizer V A) = 6 at ha
  have hqcard : Nat.card Q = 2^12 := by
    obtain ⟨a,heq⟩ := (IsElementaryAbelian.isPGroup 2 Q).exists_card_eq
    have hr : rank Q = a := by rw [rank,heq,Nat.log_pow Nat.one_lt_two]
    have ha12 : a = 12 := by omega
    simpa only [ha12] using heq
  have hZi : Zi.map I.subtype = U :=
    (selected_intersection_image I V hVI i).trans hUZ.symm
  have hUP : U ≤ P := by
    rw [←hZi]
    exact map_mono ((s.twoConjugate.core_geometry.2.2.trans inf_le_left).trans
      s.twoConjugate.P_le_twoCore)
  have hUN : (U.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    ((hPI.trans hIC).trans (Subgroup.centralizer_le_normalizer _))
  let := hUN
  let f : P →* Q := ((q.comp (inclusion hPI)).codRestrict Q (fun x => by
    apply mem_map_of_mem
    obtain ⟨y,hy,hxy⟩ := x.property
    have hyx : y = inclusion hPI x := Subtype.ext hxy
    exact hyx ▸ hy))
  have hf : Function.Surjective f := by
    rintro ⟨y,a,ha,rfl⟩
    exact ⟨⟨a,mem_map_of_mem I.subtype ha⟩,rfl⟩
  have hk : f.ker = U.subgroupOf P := by
    ext x
    change (⟨q (inclusion hPI x),_⟩ : Q) = 1 ↔ (x : G) ∈ U
    rw [Subtype.ext_iff]
    change ((inclusion hPI x : I) : I ⧸ Zi) = 1 ↔ (x : G) ∈ U
    rw [QuotientGroup.eq_one_iff,←hZi]
    constructor
    · intro hx
      exact mem_map_of_mem I.subtype hx
    · rintro ⟨a,ha,hax⟩
      exact (show a = inclusion hPI x from Subtype.ext hax) ▸ ha
  let ep : (P ⧸ U.subgroupOf P) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hel : IsElementaryAbelian 2 (P ⧸ U.subgroupOf P) :=
    IsElementaryAbelian.of_injective ep.toMonoidHom ep.injective
  have hc : Nat.card (P ⧸ U.subgroupOf P) = 2^12 :=
    (Nat.card_congr ep.toEquiv).trans hqcard
  have hUcard : Nat.card U = 2^3 := by
    obtain ⟨a,hea⟩ := ((IsElementaryAbelian.isPGroup 2 V).to_le
      (show U ≤ V from hUZ ▸ inf_le_left)).exists_card_eq
    rw [rank,hea,Nat.log_pow Nat.one_lt_two] at hu
    simpa only [hu] using hea
  have hPcard := (U.subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv,hUcard,
    index_eq_card,hc] at hPcard
  exact ⟨hUN,hel,hc,by norm_num at hPcard ⊢; exact hPcard.symm⟩

/-- The whole center of the actual two-core is the original fixed three-space. -/
theorem selected_two_core_center (s : Selected H T M V I 2 i S)
    {U : Subgroup G} (hUZ : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hUfix : U = V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Subgroup G)) :
    (center (pCore 2 I)).map (I.subtype.comp (pCore 2 I).subtype) = U := by
  let An := TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹
  let Zn := TwoConjugate.Z (V.subgroupOf I) i⁻¹
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hAi := selected_actor_image I M V hVI S i s.twoConjugate
  change An.map I.subtype = V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 at hAi
  have hZi := selected_intersection_image I V hVI i
  have hfix : V.subgroupOf I ⊓ centralizer (An : Set I) = Zn := by
    apply Subgroup.map_injective I.subtype_injective
    rw [hZi,←hUZ,hUfix]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨hx.1,?_⟩
      intro a ha
      rw [←hAi] at ha
      obtain ⟨b,hb,rfl⟩ := ha
      exact congrArg Subtype.val (hx.2 b hb)
    · intro x hx
      refine ⟨⟨x,hVI hx.1⟩,⟨hx.1,?_⟩,rfl⟩
      intro a ha
      exact Subtype.ext (hx.2 a.val (hAi ▸ mem_map_of_mem I.subtype ha))
  have hc := s.twoConjugate.center_P_eq_Z_of_V_fixed hfix
  have hp := selected_two_native_core s
  have hc' : (center (pCore 2 I)).map (pCore 2 I).subtype = Zn := by
    exact (congrArg (fun P : Subgroup I => (center P).map P.subtype) hp).symm.trans hc
  rw [←map_map,hc',hZi]
  exact hUZ.symm

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
open ChapterE Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V] {i : I} {S : Sylow 2 I}

/-- The section action of I has exactly its original two-core as kernel. -/
theorem selected_two_section_kernel (s : Selected H T M V I 2 i S)
    {U : Subgroup G} (hUZ : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    ∃ _hU : (U.subgroupOf I).Normal,
      centralizerModulo ⊤ (pCore 2 I) (U.subgroupOf I) = pCore 2 I := by
  let Zi := TwoConjugate.Z (V.subgroupOf I) i⁻¹
  let := s.twoConjugate.Z_normal
  let q := QuotientGroup.mk' Zi
  have hp := selected_two_native_core s
  have hc := s.twoConjugate.quotient_core_centralizer_le s.characteristic_two
  rw [hp] at hc
  have he := s.twoConjugate.quotient_direct_sum.1
  rw [hp] at he
  let := he
  have hkernel : centralizerModulo ⊤ (pCore 2 I) Zi = pCore 2 I := by
    apply le_antisymm
    · simpa only [centralizerModulo,top_inf_eq] using hc
    · intro x hx
      apply mem_centralizerModulo_iff.mpr
      refine ⟨mem_top x,?_⟩
      intro a ha
      apply (QuotientGroup.eq_one_iff _).mp
      change q ⁅a,x⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (congrArg Subtype.val (mul_comm
          (⟨q a,mem_map_of_mem q ha⟩ : (pCore 2 I).map q)
          (⟨q x,mem_map_of_mem q hx⟩ : (pCore 2 I).map q)))
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hUI : U ≤ I := (hUZ ▸ inf_le_left).trans hVI
  have hZi : U.subgroupOf I = Zi := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hUI,selected_intersection_image I V hVI i]
    exact hUZ
  let hUi : (U.subgroupOf I).Normal := hZi.symm ▸ s.twoConjugate.Z_normal
  exact ⟨hUi,by simpa only [hZi] using hkernel⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
