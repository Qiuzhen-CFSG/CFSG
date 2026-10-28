module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# Seven-component exclusions from the M₂₂, M₂₄ and J₂ involution tables

The actual extension and central-product descriptions give involution fixed
subgroup orders 384, 1344 or 320 for M₂₂; 21504 or 7680 for M₂₄; and 1920,
240 or 336 for J₂. None is divisible by 2520. Hence no common fixed subgroup
of a nontrivial two-subgroup can contain either seven model, independently
of whether it is a component.

The table statements are explicit premises. This module derives their
consequences and does not prove or assume their concrete model calculations
as axioms. In the central products the intersections, commutation and
generation determine the orders; no splitting of an extension is inferred.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the inspection
in E.6.18, printed p.252; the earlier tables 16.1.5(5),(7),(8), pp.1171–1172.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
namespace Tables
open Chapter16.OtherPreliminaries

private theorem extension_card {N E Q : Type*} [Group N] [Group E] [Group Q]
    (s : GroupExtension N E Q) : Nat.card E = Nat.card N * Nat.card Q := by
  have hn : Nat.card N = Nat.card s.rightHom.ker := by
    rw [← s.range_inl_eq_ker_rightHom]
    exact Nat.card_congr (MonoidHom.ofInjective s.inl_injective).toEquiv
  rw [← s.rightHom.ker.card_mul_index, ← hn, index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      s.rightHom s.rightHom_surjective).toEquiv]

private theorem elementary_card (n : ℕ) : Nat.card (Mathieu.Elementary n) = 2 ^ n := by
  simp [Mathieu.Elementary, Mathieu.C2]

/-- The full M₂₂ table suffices for every two-subgroup, not just involutions. -/
theorem m22 (rows : ∀ r : MulAut Sporadic.Mathieu.M22, orderOf r = 2 →
    Mathieu.M22InvolutionAlternative r) : SevenActionInspection Sporadic.Mathieu.M22 := by
  apply of_involution_fixed_card
  intro r hr
  rcases rows r hr with ⟨_, ⟨s⟩⟩ | ⟨_, h⟩
  · rw [extension_card s, elementary_card]
    change ¬ 2520 ∣ 2 ^ 4 * Nat.card (Equiv.Perm (Fin 4))
    rw [Nat.card_perm]
    norm_num
  · rcases h with hs | hs
    · obtain ⟨s⟩ := hs
      rw [extension_card s, elementary_card, Matrix.PSL3Two.card_PSL]
      norm_num
    · obtain ⟨s⟩ := hs
      rw [extension_card s, elementary_card, BenderSuzuki.MatrixGroups.suzukiZero_card]
      norm_num

private theorem commuting_product_card {C : Type*} [Group C] [Finite C]
    {B D : Subgroup C} (hcomm : ∀ b ∈ B, ∀ d ∈ D, b * d = d * b)
    (hsup : B ⊔ D = ⊤) :
    Nat.card B * Nat.card D = Nat.card (B ⊓ D : Subgroup C) * Nat.card C := by
  have hn : D ≤ normalizer (B : Set C) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro d hd b hb
    exact hcomm b hb d hd
  simpa only [hsup, card_top] using
    card_mul_eq_card_inf_mul_card_sup_of_normalizes B D hn

private theorem dihedral_square_card {C : Type*} [Group C] [Finite C]
    (h : Mathieu.IsDihedralSquareProduct C) : Nat.card C = 32 := by
  obtain ⟨B, D, ⟨eB⟩, ⟨eD⟩, hi, hcomm, hsup⟩ := h
  have hc := commuting_product_card hcomm hsup
  rw [Nat.card_congr eB.toEquiv, Nat.card_congr eD.toEquiv,
    DihedralGroup.nat_card, hi] at hc
  norm_num at hc
  omega

private theorem dihedral_cube_card {C : Type*} [Group C] [Finite C]
    (h : Mathieu.IsDihedralCubeProduct C) : Nat.card C = 128 := by
  obtain ⟨B, D, hB, ⟨eD⟩, hi, hcomm, hsup⟩ := h
  have hc := commuting_product_card hcomm hsup
  rw [dihedral_square_card hB, Nat.card_congr eD.toEquiv,
    DihedralGroup.nat_card, hi] at hc
  norm_num at hc
  omega

/-- The full M₂₄ table suffices for every two-subgroup, not just involutions. -/
theorem m24 (rows : ∀ r : MulAut Sporadic.Mathieu.M24, orderOf r = 2 →
    Mathieu.M24InvolutionAlternative r) : SevenActionInspection Sporadic.Mathieu.M24 := by
  apply of_involution_fixed_card
  intro r hr
  rcases (rows r hr).2 with h | hs
  · obtain ⟨Q, hQ, hshape, ⟨e⟩⟩ := h
    let := hQ
    rw [card_eq_card_quotient_mul_card_subgroup Q, Nat.card_congr e.toEquiv,
      dihedral_cube_card hshape, Matrix.PSL3Two.card_PSL]
    norm_num
  · obtain ⟨s⟩ := hs
    rw [extension_card s, elementary_card]
    change ¬ 2520 ∣ 2 ^ 6 * Nat.card (Equiv.Perm (Fin 5))
    rw [Nat.card_perm]
    norm_num

private theorem quaternion_dihedral_card {C : Type*} [Group C] [Finite C]
    (h : JankoTwoHigmanSims.IsQuaternionDihedralProduct C) : Nat.card C = 32 := by
  obtain ⟨B, D, ⟨eB⟩, ⟨eD⟩, hi, hcomm, hsup⟩ := h
  have hc := commuting_product_card hcomm hsup
  rw [Nat.card_congr eB.toEquiv, Nat.card_congr eD.toEquiv,
    DihedralGroup.nat_card, hi, Nat.card_eq_fintype_card, QuaternionGroup.card] at hc
  norm_num at hc
  omega

/-- Both inner rows and the outer J₂ row exclude embedded seven subgroups. -/
theorem j2 (rows : ∀ r : MulAut Sporadic.LeechRelated.J2.Carrier, orderOf r = 2 →
    JankoTwoHigmanSims.J2InvolutionAlternative r) :
    SevenActionInspection Sporadic.LeechRelated.J2.Carrier := by
  apply of_involution_fixed_card
  intro r hr
  rcases rows r hr with ⟨_, h⟩ | ⟨_, ⟨e⟩⟩
  · rcases h with h | he
    · obtain ⟨Q, hQ, hshape, ⟨e⟩⟩ := h
      let := hQ
      rw [card_eq_card_quotient_mul_card_subgroup Q, Nat.card_congr e.toEquiv,
        quaternion_dihedral_card hshape]
      change ¬ 2520 ∣ Nat.card (alternatingGroup (Fin 5)) * 32
      rw [nat_card_alternatingGroup]
      norm_num
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, Nat.card_prod]
      change ¬ 2520 ∣ Nat.card (Fin 2 → Multiplicative (ZMod 2)) *
        Nat.card (alternatingGroup (Fin 5))
      rw [nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card]
  · rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.Automorphisms.card_aut]
    norm_num
end Tables
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
