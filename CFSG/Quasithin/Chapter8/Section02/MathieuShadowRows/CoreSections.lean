module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore

/-!
# Literal sections of a selected degree-one pair

The generic E.2 two-conjugate geometry gives an elementary central
quotient of twice the actor rank. Transport it from the intrinsic subgroup
of I to the original ambient two-core, retaining the actual denominator U.
The fixed-space identity identifies Z(O₂(I)) with U and gives the exact
kernel O₂(I) of the action on the central quotient.

This is an intentional internal extension of HermitianSourceFieldFourCore:
its private degree-one native geometry is independent of its Hermitian
marking. Only that generic geometry is reused; no Hermitian model premise
or private name appears in these public interfaces. The M24-code application
instantiates the actor rank to six and the fixed-space rank to four.
Source: Aschbacher--Smith E.2.10, E.2.13--14 and 8.2.8, printed
pp.222--226,718--719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {i : I} {S : Sylow 2 I}

/-- The actual ambient core quotient has twice the actor rank, with its
literal quotient denominator and the full original core order. -/
theorem selected_core_section_of_ranks
    (s : Selected H T M V I 1 i S)
    (U : Subgroup G) (hU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hIC : I ≤ centralizer (U : Set G)) (r u : ℕ)
    (hr : rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)) = r)
    (hu : rank U = u) :
    ∃ _hU : (U.subgroupOf (I.pCoreIn 2)).Normal,
      IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ∧
      Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2^(2*r) ∧
      Nat.card (I.pCoreIn 2) = 2^(u+2*r) := by
  let P := I.pCoreIn 2
  have hPI : P ≤ I := pCoreIn_le 2 I
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  let Zi := TwoConjugate.Z (V.subgroupOf I) i⁻¹
  let := s.twoConjugate.Z_normal
  let q := QuotientGroup.mk' Zi
  let Q := (pCore 2 I).map q
  obtain ⟨helem,hrank⟩ := selected_one_native_section s
  let : IsElementaryAbelian 2 Q := helem
  change rank Q = 2 * rank (inducedAutomizer V
    (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)) at hrank
  rw [hr] at hrank
  have hqcard : Nat.card Q = 2^(2*r) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 Q).exists_card_eq
    have he : n = 2*r := by
      rw [rank,hn,Nat.log_pow Nat.one_lt_two] at hrank
      exact hrank
    simpa only [he] using hn
  have hZi : Zi.map I.subtype = U :=
    (selected_intersection_image I V hVI i).trans hU.symm
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
  have hc : Nat.card (P ⧸ U.subgroupOf P) = 2^(2*r) :=
    (Nat.card_congr ep.toEquiv).trans hqcard
  have hUcard : Nat.card U = 2^u := by
    obtain ⟨n,hn⟩ := ((IsElementaryAbelian.isPGroup 2 V).to_le
      (hU ▸ inf_le_left)).exists_card_eq
    rw [rank,hn,Nat.log_pow Nat.one_lt_two] at hu
    simpa only [hu] using hn
  have hPcard := (U.subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv,hUcard,index_eq_card,hc,
    ←pow_add] at hPcard
  exact ⟨hUN,hel,hc,hPcard.symm⟩

/-- With the literal fixed-space identity, the original core centre is U. -/
theorem selected_core_center_of_fixed
    (s : Selected H T M V I 1 i S) (U : Subgroup G)
    (hU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hfix : V ⊓ centralizer
      ((V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Subgroup G) : Set G) = U) :
    (center (pCore 2 I)).map (I.subtype.comp (pCore 2 I).subtype) = U := by
  let An := TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹
  let Zn := TwoConjugate.Z (V.subgroupOf I) i⁻¹
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hAi := selected_actor_image I M V hVI S i s.twoConjugate
  change An.map I.subtype = V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 at hAi
  have hZi := selected_intersection_image I V hVI i
  have hfixed : V.subgroupOf I ⊓ centralizer (An : Set I) = Zn := by
    apply Subgroup.map_injective I.subtype_injective
    rw [hZi,←hU,←hfix]
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
  have hc := s.twoConjugate.center_P_eq_Z_of_V_fixed hfixed
  have hp := selected_one_native_core s
  have hc' : (center (pCore 2 I)).map (pCore 2 I).subtype = Zn :=
    (congrArg (fun P : Subgroup I => (center P).map P.subtype) hp).symm.trans hc
  rw [←map_map,hc',hZi]
  exact hU.symm

/-- The kernel on the actual core section is the full two-core of I. -/
theorem selected_core_action_kernel
    (s : Selected H T M V I 1 i S) (U : Subgroup G)
    (hU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    ∃ _hU : (U.subgroupOf I).Normal,
      centralizerModulo ⊤ (pCore 2 I) (U.subgroupOf I) = pCore 2 I := by
  let Z := TwoConjugate.Z (V.subgroupOf I) i⁻¹
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hZi : Z.map I.subtype = U :=
    (selected_intersection_image I V hVI i).trans hU.symm
  have hz : U.subgroupOf I = Z := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le ((hU ▸ inf_le_left).trans hVI),hZi]
  have hUN : (U.subgroupOf I).Normal := hz ▸ s.twoConjugate.Z_normal
  refine ⟨hUN,?_⟩
  let := s.twoConjugate.Z_normal
  let := hUN
  have hk := selected_one_native_section_kernel s
  apply le_antisymm
  · intro x hx
    apply hk.le
    apply mem_centralizerModulo_iff.mpr
    exact ⟨mem_top x,fun a ha => hz.le ((mem_centralizerModulo_iff.mp hx).2 a ha)⟩
  · intro x hx
    apply mem_centralizerModulo_iff.mpr
    exact ⟨mem_top x,fun a ha => hz.ge
      ((mem_centralizerModulo_iff.mp (hk.ge hx)).2 a ha)⟩

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
