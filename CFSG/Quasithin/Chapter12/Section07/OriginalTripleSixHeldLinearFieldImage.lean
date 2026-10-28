module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldStructureFieldType
public import Theory.SpecificGroups.PSL3Four.CentralCover.LinearFieldImage

/-! The full original component normalizer induces exactly the linear-field
subgroup of Aut(PSL₃(4)), through the actual four-cover. Its kernel remains
the original point four-group. Thus the projective actor image is determined
as an embedded subgroup, beyond the types of individual complement actors. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal full component-normalizer action has the original four-group
as kernel and the whole projective linear-field group as image. -/
theorem original_tripleSix_escaping_linearField_image
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
    ∃ c : Matrix.PSL3Four.FourCover B,
      let β := (c.toCover.autMap c.ker_eq_center).comp B.normalizerMonoidHom
      β.ker = V.subgroupOf N ∧
      β.range = Matrix.PSL3.ExtensionBorel.linearField Matrix.PSL3Four.F := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let N := normalizer (B : Set G)
  let V := tripleSixPoint D a t
  obtain ⟨c,L,hLN,hLU,_,hcomp,hcenter,hUB,_⟩ :=
    original_tripleSix_escaping_component_normalizer_field_type h structural D a t ht heven hout
  let β := (c.toCover.autMap c.ker_eq_center).comp B.normalizerMonoidHom
  have hCV : centralizer (B : Set G) = V :=
    (original_tripleSix_escaping_projective_geometry h structural D a t ht heven hout).1
  have hk : β.ker = V.subgroupOf N := by
    rw [MonoidHom.ker_comp_of_injective _ _ (c.toCover.autMap_injective c.ker_eq_center),
      normalizerMonoidHom_ker, hCV]
  let Q := U.subgroupOf B
  let := D.elementary
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.subgroupOf hUB
  have hQc : Nat.card Q = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv).trans
      ((Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card)
  have hZQ : center B ≤ Q := by
    intro z hz
    apply (tripleSixPoint_properties D a t ht).2.1
    rw [←hcenter,centerIn_eq_map_center]
    exact mem_map_of_mem B.subtype hz
  let A := Matrix.PSL3.ExtensionBorel.linearField Matrix.PSL3Four.F
  have htop : (⊤ : Subgroup N) ≤ A.comap β := by
    rw [←hcomp.sup_eq_top]
    apply sup_le
    · intro b hb
      have hi : β b ∈ MulAut.innerSubgroup Matrix.PSL3Four.PSL := by
        have hbconj : B.normalizerMonoidHom b = MulAut.conj (⟨b,hb⟩ : B) := by
          ext y
          rfl
        obtain ⟨x,hx⟩ := (c.toCover.autMap_inner_iff c.ker_eq_center
          (B.normalizerMonoidHom b)).mpr ⟨⟨b,hb⟩, hbconj⟩
        exact ⟨x,hx.symm⟩
      exact (show Matrix.PSL3.OuterSolvable.innerDiagonal Matrix.PSL3Four.F ≤ A from
        le_sup_left) (Matrix.PSL3.OuterSolvable.inner_le_innerDiagonal _ hi)
    · intro x hx
      apply c.stabilizes_sixtyfour_linearField Q hZQ hQc (B.normalizerMonoidHom x)
      apply eq_of_le_of_card_ge
      · rintro _ ⟨u,hu,rfl⟩
        change (x:G) * (u:G) * (x:G)⁻¹ ∈ U
        exact (mem_normalizer_iff.mp (hLU hx) (u:G)).mp hu
      · rw [card_map_of_injective (f := (B.normalizerMonoidHom x).toMonoidHom)
          (B.normalizerMonoidHom x).injective]
  have hle : β.range ≤ A := by
    rintro _ ⟨x,rfl⟩
    exact htop (mem_top x)
  have hVle : V ≤ N := hCV ▸ centralizer_le_normalizer (B : Set G)
  have hkc : Nat.card β.ker = 4 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hVle).toEquiv]
    exact (tripleSixPoint_properties D a t ht).2.2.1
  have hNc : Nat.card N = 483840 :=
    (original_tripleSix_escaping_four_normalizer_index_two h structural D a t ht heven hout).2
  have hrc : Nat.card β.range = 120960 := by
    have hh := β.ker.card_mul_index
    rw [index_ker,hkc,hNc] at hh
    omega
  refine ⟨c,hk,eq_of_le_of_card_ge hle ?_⟩
  rw [hrc]
  exact Matrix.PSL3Four.linearField_card_le

end CFSG.Quasithin.Chapter12.Section07
