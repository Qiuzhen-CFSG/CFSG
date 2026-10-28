module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldStructureFieldTypeActor
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldComponentCover
public import Theory.SpecificGroups.PSL3Four.CentralCover.FieldType

/-! The actual original S₃ complement preserves the original elementary
sixty-four U. Its projective involutions are field involutions, and its
cubic elements are noninner diagonal automorphisms of the same quotient. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_component_normalizer_field_type
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
    ∃ c : Matrix.PSL3Four.FourCover B, ∃ L : Subgroup G, ∃ hLN : L≤N,
      L≤normalizer (U : Set G) ∧ Nonempty (L≃*Equiv.Perm (Fin 3)) ∧
      (B.subgroupOf N).IsComplement' (L.subgroupOf N) ∧
      centerIn B=V ∧ U≤B ∧
      let ρ := B.normalizerMonoidHom.comp (inclusion hLN)
      let β := (c.toCover.autMap c.ker_eq_center).comp ρ
      (∀ x : L, x≠1 → β x∉MulAut.innerSubgroup Matrix.PSL3Four.PSL) ∧
      (∀ x : L, orderOf x=2 → IsConj (β x) Matrix.PSL3Four.pslFrobenius) ∧
      (∀ x : L, orderOf x=3 → β x∈Matrix.PSL3.OuterSolvable.innerDiagonal Matrix.PSL3Four.F) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let N := normalizer (B : Set G)
  let V := tripleSixPoint D a t
  obtain ⟨hcenter,⟨c⟩⟩ := original_tripleSix_escaping_component_cover
    h structural D a t ht heven hout
  obtain ⟨L,hLV,hLU,⟨eL⟩,hdis⟩ := original_tripleSix_escaping_four_actor_preserves_module
    h structural D a t ht heven hout
  obtain ⟨_,hNV,_⟩ := original_tripleSix_escaping_projective_geometry
    h structural D a t ht heven hout
  have hLN : L≤N := hLV.trans_eq hNV.symm
  have hUB : U≤B := (tripleSixPointCentralizerResidual_commutator D a t ht heven).2.trans
    (le_conjugateSpanBy Lt H)
  have hZB : B≤centralizer (V : Set G) := by
    intro b hb v hv
    change v∈tripleSixPoint D a t at hv
    rw [←hcenter] at hv
    exact (hv.2 b hb).symm
  have hLc : Nat.card L=6 := by
    rw [Nat.card_congr eL.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hBc := (original_tripleSix_escaping_component_normalizer_index_six
    h structural D a t ht heven hout).1
  have hNc := (original_tripleSix_escaping_four_normalizer_index_two
    h structural D a t ht heven hout).2
  have hcomp : (B.subgroupOf N).IsComplement' (L.subgroupOf N) := by
    apply isComplement'_of_card_mul_and_disjoint
    · rw [Nat.card_congr (subgroupOfEquivOfLe B.le_normalizer).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hLN).toEquiv,hLc,hBc,hNc]
    · apply disjoint_iff.mpr
      apply bot_unique
      intro x hx
      apply Subtype.ext
      have hh : (x:G)∈L⊓centralizer (V:Set G) := ⟨hx.2,hZB hx.1⟩
      rw [hdis] at hh
      exact hh
  let ρ : L→*MulAut B := B.normalizerMonoidHom.comp (inclusion hLN)
  let β := (c.toCover.autMap c.ker_eq_center).comp ρ
  have hmoves (x : L) (hx : x≠1) : ∃ z : center B, ρ x z≠z := by
    by_contra! hfix
    have hxC : (x:G)∈centralizer (V:Set G) := by
      intro v hv
      change v∈tripleSixPoint D a t at hv
      rw [←hcenter,centerIn_eq_map_center] at hv
      obtain ⟨z,hz,rfl⟩ := hv
      have he := congrArg (fun y : B => (y:G)) (hfix ⟨z,hz⟩)
      change (x:G)*(z:G)*(x:G)⁻¹=(z:G) at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hh : (x:G)∈L⊓centralizer (V:Set G) := ⟨x.property,hxC⟩
    rw [hdis] at hh
    exact hx (Subtype.ext hh)
  have hout' (x : L) (hx : x≠1) : β x∉MulAut.innerSubgroup Matrix.PSL3Four.PSL := by
    rintro ⟨y,hy⟩
    obtain ⟨b,hb⟩ := (c.toCover.autMap_inner_iff c.ker_eq_center (ρ x)).mp ⟨y,hy.symm⟩
    obtain ⟨z,hz⟩ := hmoves x hx
    apply hz
    rw [hb]
    change b*(z:B)*b⁻¹=(z:B)
    rw [mem_center_iff.mp z.property b,mul_inv_cancel_right]
  let Q := U.subgroupOf B
  let := D.elementary
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.subgroupOf hUB
  have hQc : Nat.card Q=64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv).trans
      ((Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans hexacode_card)
  have hZQ : center B≤Q := by
    intro z hz
    apply (tripleSixPoint_properties D a t ht).2.1
    rw [←hcenter,centerIn_eq_map_center]
    exact mem_map_of_mem B.subtype hz
  have hQfix (x : L) : Q.map (ρ x).toMonoidHom=Q := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      change (x:G)*(u:G)*(x:G)⁻¹∈U
      exact (mem_normalizer_iff.mp (hLU x.property) (u:G)).mp hu
    · rw [card_map_of_injective (f := (ρ x).toMonoidHom) (ρ x).injective]
  refine ⟨c,L,hLN,hLU,⟨eL⟩,hcomp,hcenter,hUB,hout',?_,?_⟩
  · intro x hx
    apply c.involution_stabilizes_sixtyfour_is_field Q hZQ hQc (ρ x)
    · have hx2 : x^2=1 := hx ▸ pow_orderOf_eq_one x
      rw [←map_pow,hx2,map_one]
    · exact hQfix x
    · exact hmoves x (fun he => by rw [he,orderOf_one] at hx; omega)
  · intro x hx
    exact Matrix.PSL3Four.cube_one_mem_innerDiagonal (β x)
      (by
        have hx3 : x^3=1 := hx ▸ pow_orderOf_eq_one x
        rw [←map_pow,hx3,map_one])

end CFSG.Quasithin.Chapter12.Section07
