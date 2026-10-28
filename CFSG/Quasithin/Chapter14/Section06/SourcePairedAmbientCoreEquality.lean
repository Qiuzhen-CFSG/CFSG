module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedCoreEquality
public import Theory.GroupTheory.IrreducibleSectionRestriction

/-!
# Ambient subgroup inputs for the actual omega-core quotient

The paired block geometry is stated in the original ambient group, while
the quotient by Ω₁Z(O₂(H)) is formed inside H. This theorem restricts both
irreducible sections, the literal conjugation map, the quotient-center
bound, and both centralizer conditions through H.subtype. It then maps
the proved core equality back to the ambient group.

Source: the carrier transition in Aschbacher--Smith, 14.6.9(k)--(n),
printed p.1027. This is used with H = Mc and B = I ∩ Mc.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
attribute [local instance] omegaCore_normal

/-- The paired irreducible sections and their ordinary and modulo centralizers
identify the actual local two-core. -/
theorem source_omegaCore_eq_of_ambient_paired_sections
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {H : Subgroup G} (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G))
    (S B A C K E N Z₀ : Subgroup G)
    (hBH : B ≤ H) (hKH : K ≤ H)
    (hST : S ≤ (T : Subgroup G))
    (hSnormal : (S.subgroupOf (T : Subgroup G)).Normal)
    (hCS : C ≤ S) (hQC : H.pCoreIn 2 ≤ C) (hEA : E ≤ A)
    (hZ₀Z : Z₀ ≤ omegaOneCenterAmbient (H.pCoreIn 2))
    [(Z₀.subgroupOf S).Normal]
    (hBE : B ≤ normalizer (E : Set G))
    (hirrE : IsIrreducibleSection B Z₀ E)
    (hcenter : ((center (S ⧸ Z₀.subgroupOf S)).comap
      (QuotientGroup.mk' (Z₀.subgroupOf S))).map S.subtype ≤ E)
    (hBA : B ≤ normalizer (A : Set G))
    (hBC : B ≤ normalizer (C : Set G))
    (hirrC : IsIrreducibleSection B A C)
    (hsmall : ⁅A,K⁆ ≤ E) (hcomm : ⁅C,K⁆ = N)
    (a : G) (haH : a ∈ H)
    (hcard : Nat.card (A ⊓ A.map (MulAut.conj a).toMonoidHom : Subgroup G) < Nat.card E)
    (hcent : C ⊓ centralizer (N : Set G) ≤ Z₀)
    (hmod : ∀ c ∈ C, (∀ n ∈ N, ⁅n,c⁆ ∈ Z₀) → c ∈ N) :
    H.pCoreIn 2 = N := by
  let S₀ := S.subgroupOf H
  let B₀ := B.subgroupOf H
  let A₀ := A.subgroupOf H
  let C₀ := C.subgroupOf H
  let K₀ := K.subgroupOf H
  let E₀ := E.subgroupOf H
  let N₀ := N.subgroupOf H
  let Z₀' := Z₀.subgroupOf H
  have hSH : S ≤ H := hST.trans hH.2
  have hCH : C ≤ H := hCS.trans hSH
  have hAH : A ≤ H := hirrC.1.trans hCH
  have hEH : E ≤ H := hEA.trans hAH
  have hZS : Z₀ ≤ S := hirrE.1.trans (hEA.trans (hirrC.1.trans hCS))
  have hNH : N ≤ H := by
    rw [←hcomm]
    exact (Subgroup.commutator_le_sup C K).trans (sup_le hCH hKH)
  have hST₀ : S₀ ≤ (T.subtype hH.2 : Subgroup H) := comap_mono hST
  have hTnS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp hSnormal
  have hSn₀ : (S₀.subgroupOf (T.subtype hH.2 : Subgroup H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hST₀).mpr
      (normalizes_subgroupOf_of_normalizes H (T : Subgroup G) S hTnS)
  let : (Z₀'.subgroupOf S₀).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show Z₀' ≤ S₀ from comap_mono hZS)).mpr
      (normalizes_subgroupOf_of_normalizes H S Z₀
        ((normal_subgroupOf_iff_le_normalizer hZS).mp inferInstance))
  have hQC₀ : pCore 2 H ≤ C₀ := by
    intro x hx
    exact hQC (mem_map_of_mem H.subtype hx)
  have hZ₀Z' : Z₀' ≤ omegaOneCenterAmbient (pCore 2 H) := by
    intro x hx
    have hm := hZ₀Z hx
    change x.val ∈ omegaOneCenterAmbient ((pCore 2 H).map H.subtype) at hm
    rw [omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective] at hm
    exact (mem_map_iff_mem H.subtype_injective).mp hm
  have hcenter₀ : ((center (S₀ ⧸ Z₀'.subgroupOf S₀)).comap
      (QuotientGroup.mk' (Z₀'.subgroupOf S₀))).map S₀.subtype ≤ E₀ := by
    apply (quotient_center_preimage_le_iff S₀ Z₀' E₀).mpr
    intro s hs hc
    apply (quotient_center_preimage_le_iff S Z₀ E).mp hcenter s hs
    intro t ht
    exact hc ⟨t,hSH ht⟩ ht
  have hcomm₀ : ⁅C₀,K₀⁆ = N₀ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hCH,
      map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hNH,hcomm]
  have hsmall₀ : ⁅A₀,K₀⁆ ≤ E₀ := by
    intro x hx
    have hm := mem_map_of_mem H.subtype hx
    rw [map_commutator,map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hKH] at hm
    exact hsmall hm
  let a₀ : H := ⟨a,haH⟩
  have hmapConj : (A₀.map (MulAut.conj a₀).toMonoidHom).map H.subtype =
      A.map (MulAut.conj a).toMonoidHom := by
    rw [map_map]
    change A₀.map ((MulAut.conj a).toMonoidHom.comp H.subtype) = _
    rw [←map_map,map_subgroupOf_eq_of_le hAH]
  have hcard₀ : Nat.card (A₀ ⊓ A₀.map (MulAut.conj a₀).toMonoidHom : Subgroup H) < Nat.card E₀ := by
    rw [←card_map_of_injective H.subtype_injective (K := A₀ ⊓ A₀.map (MulAut.conj a₀).toMonoidHom),
      ←card_map_of_injective H.subtype_injective (K := E₀)]
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,map_subgroupOf_eq_of_le hAH,
      hmapConj,map_subgroupOf_eq_of_le hEH]
    exact hcard
  have hcent₀ : C₀ ⊓ centralizer (N₀ : Set H) ≤ Z₀' := by
    intro x hx
    apply hcent
    refine ⟨hx.1,?_⟩
    intro n hn
    exact congrArg Subtype.val (hx.2 ⟨n,hNH hn⟩ hn)
  have hmod₀ : ∀ c ∈ C₀, (∀ n ∈ N₀, ⁅n,c⁆ ∈ Z₀') → c ∈ N₀ := by
    intro c hc hm
    exact hmod c hc (fun n hn => hm ⟨n,hNH hn⟩ hn)
  have hEq : pCore 2 H = N₀ := source_omegaCore_eq_of_paired_sections
    hG T hempty hH hHZ S₀ B₀ A₀ C₀ K₀ E₀ N₀ Z₀' hST₀ hSn₀
    (comap_mono hCS) hQC₀ (comap_mono hEA) hZ₀Z'
    (normalizes_subgroupOf_of_normalizes H B E hBE)
    (irreducible_section_subgroupOf H B Z₀ E hBH hEH hirrE) hcenter₀
    (normalizes_subgroupOf_of_normalizes H B A hBA)
    (normalizes_subgroupOf_of_normalizes H B C hBC)
    (irreducible_section_subgroupOf H B A C hBH hCH hirrC)
    hsmall₀ hcomm₀ a₀ hcard₀ hcent₀ hmod₀
  change (pCore 2 H).map H.subtype = N
  rw [hEq]
  exact map_subgroupOf_eq_of_le hNH
end CFSG.Quasithin.Chapter14.Section06
