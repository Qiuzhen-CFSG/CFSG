module

public import CFSG.Quasithin.Chapter8.Section01
public import CFSG.Quasithin.Chapter7.Section01To05.FixedSpaceSpan
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.FixedGeneration
public import Theory.ElementaryAbelian.FixedOrderGeneration

/-!
# Full-kernel lifts in the original corank-five offender family

Every subgroup of an induced automizer lifts to its full inverse image in the
original acting subgroup. This preserves the whole centralizer kernel and the
relative index. For a w-offender, the corank formula places the lift in the
literal family used to define `offenderCentralizerSpan` in original 8.1.3.

At image rank five and 1 ≤ w ≤ 2, every elementary four-subgroup fixed space
is contained in that span. At image rank four and w = 2, the span equals the
sum of the fixed spaces of all nonidentity elements of the induced automizer.
Thus native module calculations apply to the original ambient subgroup with
its original covering kernel, rather than to a replacement action.

Source: Aschbacher--Smith 7.5.3 and 8.1.3, printed pp.700 and 713--714,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterE Chapter7 MathieuCode.M22Quintet
variable {G : Type*} [Group G]

/-- Lift an action subgroup with its whole original centralizer kernel. -/
theorem lift_with_kernel {V A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (D : Subgroup (Automizer V)) (hD : D ≤ inducedAutomizer V A) :
    ∃ B ≤ A, A ⊓ centralizer (V : Set G) ≤ B ∧ inducedAutomizer V B = D ∧
      subgroupCorank A B = subgroupCorank (inducedAutomizer V A) D := by
  let N := normalizer (V : Set G)
  let f := V.normalizerMonoidHom.rangeRestrict
  let C := A.subgroupOf N
  let J := C ⊓ D.comap f
  let B := J.map N.subtype
  have hBA : B ≤ A := by
    rintro _ ⟨x,hx,rfl⟩
    exact hx.1
  have hBN : B.subgroupOf N = J :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective J
  have hmap : J.map f = D := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro d hd
      obtain ⟨x,hx,he⟩ := hD hd
      exact ⟨x,⟨hx,(show f x ∈ D from he.symm ▸ hd)⟩,he⟩
  refine ⟨B,hBA,?_,?_,?_⟩
  · intro x hx
    have hz : f ⟨x,hA hx.1⟩ = 1 := by
      apply Subtype.ext
      change ⟨x,hA hx.1⟩ ∈ V.normalizerMonoidHom.ker
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hx.2
    exact ⟨⟨x,hA hx.1⟩,⟨hx.1,(show f ⟨x,hA hx.1⟩ ∈ D from hz ▸ D.one_mem)⟩,rfl⟩
  · change (B.subgroupOf N).map f = D
    rw [hBN,hmap]
  · unfold subgroupCorank
    congr 1
    rw [←Subgroup.relIndex_subgroupOf (H := B) hA,hBN]
    exact (Subgroup.inf_relIndex_left C (D.comap f)).trans
      (Subgroup.relIndex_comap D f C)

variable [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Every image of the required rank has a literal corank-five preimage. -/
theorem offender_family_lift {T : Subgroup G} {g : G} (h : IsWOffenderAt V T g)
    (D : Subgroup (Automizer V)) (hD : D ≤ inducedAutomizer V (offenderNormalizer V g))
    (hdim : 5 + rank D = (globalW V T).toNat +
      rank (inducedAutomizer V (offenderNormalizer V g))) :
    ∃ B ∈ offenderCorankFamily V g 5, inducedAutomizer V B = D := by
  let I := inducedAutomizer V (offenderNormalizer V g)
  let := offender_inducedAutomizer_elementary V g
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  obtain ⟨B,hBA,hker,hmap,hcor⟩ := lift_with_kernel inf_le_right D hD
  refine ⟨B,⟨hBA,hker,?_⟩,hmap⟩
  have he : rank I = subgroupCorank I D + rank D := by
    have hh := offender_corank_add (B := (⊥ : Subgroup (Automizer V))) bot_le hD
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hh
  have hw : (globalW V T).toNat =
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) := by
    rw [h.2,ENat.toNat_natCast]
  rw [offender_corank_add hBA (show offenderNormalizer V g ≤
    V.map (MulAut.conj g).toMonoidHom from inf_le_left),hcor]
  change 5 + rank D = (globalW V T).toNat + rank I at hdim
  change subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
    (offenderNormalizer V g) + subgroupCorank I D = 5
  omega

/-- The native four-subgroup span maps into the exact ambient span in 8.1.3. -/
theorem fourFixedSpan_le_offenderCentralizerSpan
    {T : Subgroup G} {g : G} (h : IsWOffenderAt V T g)
    (hfive : rank (inducedAutomizer V (offenderNormalizer V g)) = 5)
    (hwpos : 1 ≤ (globalW V T).toNat) (hw : (globalW V T).toNat ≤ 2) :
    ambientSubmodule V (fourFixedSpan (automizerRepresentation V)
      (inducedAutomizer V (offenderNormalizer V g))) ≤ offenderCentralizerSpan V g 5 := by
  simp only [fourFixedSpan,ambientSubmodule_iSup]
  refine iSup_le fun D => iSup_le fun hD => iSup_le fun he => iSup_le fun hc => ?_
  let := he
  obtain ⟨J,hJD,hJ,hJcard,_⟩ := IsElementaryAbelian.exists_two_power_subgroup_mem
    D (n := (globalW V T).toNat) (by omega)
    (by rw [hc]; exact Nat.pow_le_pow_right (n := 2) (i := (globalW V T).toNat) (by decide) hw) 1 D.one_mem
  have hr : rank J = (globalW V T).toNat := by
    rw [rank,hJcard,Nat.log_pow Nat.one_lt_two]
  obtain ⟨B,hB,hBI⟩ := offender_family_lift h J (hJD.trans hD) (by rw [hr,hfive]; omega)
  have hfix : fixedSpace (automizerRepresentation V) D ≤
      fixedSpace (automizerRepresentation V) (inducedAutomizer V B) := by
    rw [hBI]
    exact ChapterE.fixedSpace_antitone _ hJD
  have hle : ambientSubmodule V (fixedSpace (automizerRepresentation V) D) ≤
      ambientSubmodule V (fixedSpace (automizerRepresentation V) (inducedAutomizer V B)) :=
    Subgroup.map_mono ((moduleSubgroup V).monotone hfix)
  rw [ambientSubmodule_fixedSpace V B (hB.1.trans inf_le_right)] at hle
  exact hle.trans (le_iSup_of_le B (le_iSup_of_le hB le_rfl))

end CFSG.Quasithin.Chapter8.MathieuShadowRows

namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterE Chapter7
open MathieuCode.M22Quintet
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- At image rank four and w=2, the literal corank-five span is exactly
H.10.1's sum of nonidentity element fixed spaces. -/
theorem rank_four_offenderCentralizerSpan_eq
    {T : Subgroup G} {g : G} (h : IsWOffenderAt V T g)
    (hfour : rank (inducedAutomizer V (offenderNormalizer V g)) = 4)
    (hw : (globalW V T).toNat = 2) :
    offenderCentralizerSpan V g 5 = offenderFixedSpan V g := by
  let I := inducedAutomizer V (offenderNormalizer V g)
  let := offender_inducedAutomizer_elementary V g
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => ?_
    let J := inducedAutomizer V B
    have hJI : J ≤ I := Subgroup.map_mono (Subgroup.comap_mono hB.1)
    let := offender_elementary_of_le hJI
    have hr : rank J = 1 := by
      have he := offenderCorankFamily_image_rank h hB
      rw [hfour,hw] at he
      change 5 + rank J = 2 + 4 at he
      omega
    have hc : Nat.card J = 2 := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 J).exists_card_eq
      have he : rank J = n := by rw [rank,hn,Nat.log_pow Nat.one_lt_two]
      have hn1 : n = 1 := he.symm.trans hr
      rw [hn,hn1,pow_one]
    let : IsCyclic J := isCyclic_of_prime_card hc
    obtain ⟨a,he⟩ := J.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
    have ha : a ∈ J := he ▸ mem_zpowers a
    have ha1 : a ≠ 1 := by
      intro hz
      rw [hz,zpowers_one_eq_bot] at he
      have : rank J = 0 := by rw [←he,rank]; simp
      omega
    have hfix : fixedSpace (automizerRepresentation V) J ≤
        fixedSpaceSpan (automizerRepresentation V) I := by
      rw [←he]
      exact fixedSpace_le_fixedSpaceSpan _ (hJI ha) ha1
    rw [←ambientSubmodule_fixedSpace V B (hB.1.trans inf_le_right)]
    exact Subgroup.map_mono ((moduleSubgroup V).monotone hfix)
  · change ambientSubmodule V (fixedSpaceSpan (automizerRepresentation V) I) ≤ _
    simp only [fixedSpaceSpan,ambientSubmodule_iSup]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    have hao : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
    have hr : rank (zpowers a) = 1 := by
      rw [rank,Nat.card_zpowers,hao]
      decide
    obtain ⟨B,hB,hBI⟩ := offender_family_lift h (zpowers a) (zpowers_le.mpr ha)
      (by rw [hr,hw,hfour])
    rw [←hBI,ambientSubmodule_fixedSpace V B (hB.1.trans inf_le_right)]
    exact le_iSup_of_le B (le_iSup_of_le hB le_rfl)
end CFSG.Quasithin.Chapter8.MathieuShadowRows
