module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldFourNormalizerStructureSplit
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction

/-! The split quotient is the full literal conjugation action on the
original central four-group, with the original component as kernel. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_component_normalizer_four_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    let N := normalizer (B : Set G)
    let V := tripleSixPoint D a t
    ∃ hNV : N ≤ normalizer (V : Set G),
      let f := V.normalizerMonoidHom.comp (inclusion hNV)
      Function.Surjective f ∧ f.ker = B.subgroupOf N ∧
        ∃ L : Subgroup N, (B.subgroupOf N).IsComplement' L ∧
          Function.Bijective (f.comp L.subtype) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let N := normalizer (B : Set G)
  let V := tripleSixPoint D a t
  obtain ⟨hC,L,hLN,⟨eL⟩,hcomp,_⟩ :=
    original_tripleSix_escaping_component_normalizer_split h structural D a t ht heven hout
  obtain ⟨_,hNV,_⟩ := original_tripleSix_escaping_projective_geometry h structural D a t ht heven hout
  have hN : N ≤ normalizer (V:Set G) := hNV.le
  let f := V.normalizerMonoidHom.comp (inclusion hN)
  have hk : f.ker = B.subgroupOf N := by
    change V.normalizerMonoidHom.ker.comap (inclusion hN) = _
    rw [normalizerMonoidHom_ker,hC]
    rfl
  have hV := tripleSixPoint_properties D a t ht
  let := hV.2.2.2.1
  let : Nontrivial V := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hV.2.2.1]; decide)
  let : IsKleinFour V := ⟨hV.2.2.1,IsElementaryAbelian.exponent_eq_prime⟩
  have hBc := (original_tripleSix_escaping_component_normalizer_index_six
    h structural D a t ht heven hout).1
  have hNc := (original_tripleSix_escaping_four_normalizer_index_two
    h structural D a t ht heven hout).2
  have hrc : Nat.card f.range=6 := by
    have hm := f.ker.card_mul_index
    rw [index_ker,hk,Nat.card_congr (subgroupOfEquivOfLe B.le_normalizer).toEquiv,hBc,hNc] at hm
    omega
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp
    (f.range.eq_top_of_card_eq (hrc.trans (IsKleinFour.card_mulAut V).symm))
  let L' := L.subgroupOf N
  have hi : Function.Injective (f.comp L'.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro l hl
    have hb : l.val∈B.subgroupOf N := hk ▸ (show l.val∈f.ker from hl)
    apply Subtype.ext
    exact (disjoint_iff.mp hcomp.disjoint).le ⟨hb,l.property⟩
  have hc : Nat.card L'=Nat.card (MulAut V) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hLN).toEquiv,
      Nat.card_congr eL.toEquiv,IsKleinFour.card_mulAut]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  exact ⟨hN,hf,hk,L',hcomp,(Nat.bijective_iff_injective_and_card _).mpr ⟨hi,hc⟩⟩

end CFSG.Quasithin.Chapter12.Section07
