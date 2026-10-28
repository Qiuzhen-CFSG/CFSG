module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalAutomizerSource
public import GorensteinWalter.CardSupOfDisjointNormalizer
/-!
# The actual component index modulo the source two-core

The component intersects its centralizer kernel trivially, so the order
of H/O₂(H) is |K| times the actual index of K O₂(H) in H. The proved
nonfull A₆, binary linear, and odd PGL models therefore give index two,
without assuming that an abstract quotient isomorphism marks K.

Source: Aschbacher--Smith 2.5.16 and the abelian-core step of 2.5.21,
printed pp.560,565--566.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.normal_component_core_index_card
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) :
    Nat.card K * (K ⊔ twoCore H).relIndex H = Nat.card (H ⧸ pCore 2 H) := by
  let D := K.subgroupOf H
  let C := pCore 2 H
  have hC : centralizer (D : Set H) = C := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact MathieuSourceSetup.normal_component_conjugation_ker c hG hempty hgen
  have hd : Disjoint D C := by
    apply disjoint_def.mpr
    intro d hdD hdC
    have hz : (⟨d, hdD⟩ : D) ∈ center D := by
      apply mem_center_iff.mpr
      intro a
      rw [← hC] at hdC
      exact Subtype.ext (hdC a a.property)
    let e : D ≃* K := subgroupOfEquivOfLe c.component_le
    have he := (centerCongr e ⟨⟨d, hdD⟩, hz⟩).property
    change e ⟨d, hdD⟩ ∈ center K at he
    rw [MathieuSourceSetup.component_center_eq_bot c hG hempty hgen, mem_bot] at he
    exact congrArg Subtype.val (e.map_eq_one_iff.mp he)
  have hcard := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer D C
    (by rw [D.normalizer_eq_top]; exact le_top) hd
  have htotal := (D ⊔ C).card_mul_index
  rw [hcard] at htotal
  have hquot := card_eq_card_quotient_mul_card_subgroup C
  have hindex : Nat.card D * (D ⊔ C).index = Nat.card (H ⧸ C) := by
    have hpos := Nat.card_pos (α := C)
    nlinarith
  have hmap : (D ⊔ C).map H.subtype = K ⊔ twoCore H := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le c.component_le]
    rfl
  have hi : (K ⊔ twoCore H).relIndex H = (D ⊔ C).index := by
    have ht : (⊤ : Subgroup H).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    calc
      _ = ((D ⊔ C).map H.subtype).relIndex
          ((⊤ : Subgroup H).map H.subtype) := by rw [hmap, ht]
      _ = (D ⊔ C).relIndex (⊤ : Subgroup H) :=
        relIndex_map_map_of_injective _ _ H.subtype_injective
      _ = _ := relIndex_top_right _
  rw [hi, ← Nat.card_congr (subgroupOfEquivOfLe c.component_le).toEquiv]
  exact hindex

theorem MathieuSourceSetup.normal_component_core_index_le_two_of_card
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hc : Nat.card (H ⧸ pCore 2 H) ≤ 2 * Nat.card K) :
    (K ⊔ twoCore H).relIndex H ≤ 2 := by
  have hi := MathieuSourceSetup.normal_component_core_index_card c hG hempty hgen
  have hp := Nat.card_pos (α := K)
  nlinarith

theorem MathieuSourceSetup.alternating_six_nonfull_core_index
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hQ : Nonempty ((H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)) :
    (K ⊔ twoCore H).relIndex H = 2 := by
  have hi := MathieuSourceSetup.normal_component_core_index_card c hG hempty hgen
  rw [Nat.card_congr eK.toEquiv, AlternatingSix.ShadowLocal.card_A6] at hi
  have hcard : Nat.card (H ⧸ pCore 2 H) = 720 := by
    rcases hQ with hQ | hQ
    · obtain ⟨e⟩ := hQ
      rw [Nat.card_congr e.toEquiv, AlternatingSix.M10.Action.card_extension]
    · obtain ⟨e⟩ := hQ
      rw [Nat.card_congr e.toEquiv, GorensteinWalter.pgl2_card_formula,
        Atlas.Comparisons.Exceptional.Nine.card]
      norm_num
  rw [hcard] at hi
  omega

open scoped MatrixGroups
/-- The prime linear branch, using its actual quotient model. -/
theorem MathieuSourceSetup.linear_pgl_core_index
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (F : Type*) [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (eK : K ≃* PSL(2, F)) (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 F) :
    (K ⊔ twoCore H).relIndex H = 2 := by
  have hi := MathieuSourceSetup.normal_component_core_index_card c hG hempty hgen
  rw [Nat.card_congr eK.toEquiv, Nat.card_congr eQ.toEquiv,
    GorensteinWalter.pgl2_card_formula] at hi
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) hodd
  have hp := Nat.card_pos (α := PSL(2, F))
  nlinarith

/-- The binary linear source automizer gives inner index exactly two. -/
theorem MathieuSourceSetup.linear_binary_core_index
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (eK : K ≃* Matrix.PSL3Two.PSL) :
    (K ⊔ twoCore H).relIndex H = 2 := by
  obtain ⟨eQ⟩ := MathieuSourceSetup.normal_linear_binary_core_quotient c hG hempty hgen eK
  have hi := MathieuSourceSetup.normal_component_core_index_card c hG hempty hgen
  rw [Nat.card_congr eK.toEquiv, Nat.card_congr eQ.toEquiv,
    Matrix.PSL3Two.Automorphisms.card_aut] at hi
  have hc : Nat.card Matrix.PSL3Two.PSL = 168 := by
    rw [← Nat.card_congr Matrix.PSL3Two.equiv.toEquiv]
    exact Matrix.PSL3Two.card_SL
  rw [hc] at hi
  omega
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
