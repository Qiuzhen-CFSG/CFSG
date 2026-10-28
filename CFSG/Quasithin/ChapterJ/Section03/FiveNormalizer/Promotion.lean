module
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.LocalTwo
public import Theory.GroupTheory.UniqueCentralInvolutionSylow
/-!
# Source Sylow promotion and the extraspecial five-group

Inside N_G(P), the centralizer of the original z is exactly N_H(B₅), of
order160. The already constructed order32 subgroup has z as its unique
central involution, so its relative index five in that centralizer promotes
it to Sylow in N_G(P). Thus64 cannot divide this normalizer order.
The elementary-branch exclusion now gives the source extraspecial P,
retaining only the earlier ambient order from J.3.1.

All local choices and subgroup maps are the original TypeRu objects.
Source: Aschbacher--Smith J.3.6, printed p.439.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

private theorem local_normalizer_intersection (c : Choices d)
    (B5 : Sylow 5 d.toTypeRuSetup.H) :
    d.toTypeRuSetup.H ⊓ normalizer (fiveOddPart B5 : Set G) =
      d.toTypeRuSetup.H ⊓ normalizer (B5Image B5 : Set G) := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  have hB : fiveOddPart B5 ⊓ d.toTypeRuSetup.H=B5Image B5 := by
    rw [c.H_eq_centralizer_z]
    exact c.fiveOddPart_inf_centralizer_z d.card_Z B5 q
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    have hp := mem_normalizer_iff_map_conj_eq.mp hx.2
    have hh := mem_normalizer_iff_map_conj_eq.mp (d.toTypeRuSetup.H.le_normalizer hx.1)
    rw [← hB,map_inf _ _ _ (MulAut.conj x).injective,hp,hh]
  · exact inf_le_inf_left _ (normalizer_B5Image_le_normalizer_fiveOddPart B5)

/-- The source local order32 group is Sylow in the original normalizer of P. -/
theorem five_normalizer_not_sixtyfour (c : Choices d)
    (B5 : Sylow 5 d.toTypeRuSetup.H) :
    ¬64∣Nat.card (normalizer (fiveOddPart B5 : Set G)) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  obtain ⟨R,hR,hRc,hQR,hu⟩ := exists_five_local_two c B5
  let M := normalizer (fiveOddPart B5 : Set G)
  have hzM : c.z∈M := G5_normalizes_fiveOddPart B5 (c.z_mem_G5 B5)
  let z : M := ⟨c.z,hzM⟩
  let C := centralizer ({z} : Set M)
  have hCm : C.map M.subtype = d.toTypeRuSetup.H ⊓ normalizer (B5Image B5 : Set G) := by
    rw [← local_normalizer_intersection c B5]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨?_,y.property⟩
      rw [c.H_eq_centralizer_z]
      change (y:G)∈centralizer ({c.z} : Set G)
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)
    · intro hx
      refine ⟨⟨x,hx.2⟩,?_,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hx.1)
  have hCc : Nat.card C=160 := by
    rw [← card_map_of_injective (K:=C) M.subtype_injective,hCm,local_five_normalizer_card c B5]
  have hRM : R≤M := (hR.trans inf_le_right).trans
    (normalizer_B5Image_le_normalizer_fiveOddPart B5)
  let A := R.subgroupOf M
  have hAc : Nat.card A=32 := (Nat.card_congr (subgroupOfEquivOfLe hRM).toEquiv).trans hRc
  have hAp : IsPGroup 2 A := IsPGroup.of_card (n:=5) hAc
  have hAC : A≤C := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ (hR ha).1)
  have hzQ : c.z∈CQ B5 := (q.inf_U.symm ▸ c.z_mem_Z).1
  let zA : A := ⟨z,hQR hzQ⟩
  have hzA2 : orderOf zA=2 := by
    rw [← orderOf_coe,← orderOf_coe]
    exact SourceCompletion.z_order c
  have hzAc : zA∈center A := by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hAC a.property)
  have huA (a:A) (ha:a∈center A) (ho:orderOf a=2) : a=zA := by
    let e := subgroupOfEquivOfLe hRM
    have hec : e a∈center R := by
      apply mem_center_iff.mpr
      intro r
      obtain ⟨b,rfl⟩ := e.surjective r
      simpa only [map_mul] using congrArg e (mem_center_iff.mp ha b)
    have hh := hu (e a) hec ((e.orderOf_eq a).trans ho)
    exact Subtype.ext (Subtype.ext hh)
  have hindex : A.relIndex C=5 := by
    have he := relIndex_mul_relIndex (⊥ : Subgroup M) A C bot_le hAC
    rw [relIndex_bot_left,relIndex_bot_left,hAc,hCc] at he
    omega
  obtain ⟨S,hS⟩ := exists_sylow_of_unique_central_involution A hAp zA hzA2 hzAc huA
    (by change ¬2∣A.relIndex C; rw [hindex]; decide)
  have hSc : Nat.card S=32 := hS ▸ hAc
  intro hd
  have he := (S : Subgroup M).card_mul_index
  rw [hSc] at he
  have hi : 2∣(S : Subgroup M).index := by
    rw [← he] at hd
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0<32)).mp hd
  exact S.not_dvd_index hi

/-- The original five-core is extraspecial, with only the earlier J.3.1 order retained. -/
theorem five_oddPart_extraspecial (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    IsExtraspecial 5 (fiveOddPart B5) :=
  five_oddPart_extraspecial_of_two_part c B5 hG (five_normalizer_not_sixtyfour c B5)

/-- The same extraspecial conclusion for the literal five-core used downstream. -/
theorem five_core_extraspecial (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    IsExtraspecial 5 (pCoreIn 5 (G5 B5)) := by
  rw [← SourceCompletion.five_oddPart_eq_core c B5]
  exact five_oddPart_extraspecial c B5 hG

end CFSG.Quasithin.ChapterJ.Section03
