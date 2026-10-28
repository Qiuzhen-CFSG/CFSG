module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource

/-!
# Whole-module inputs to seven-letter block selection

These models describe the actual conjugation action on a normal elementary
subgroup of the original ambient group. C.1.24 constructs shortness, and
the normal-layer comparison identifies the full block module with this
subgroup. The resulting ordinary or exceptional type is therefore a fact
about the original component, rather than its action image.

Source: Aschbacher--Smith, C.1.24(a), pp.130--131, and14.6.10(5), p.1029.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
open ChapterC ChapterC.RankOne.SevenSource
variable {G : Type*} [Group G] [Finite G]

/-- Coordinates on the entire moved subgroup, with its literal ambient action. -/
def WholeModule (K U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] : Prop :=
  (∃ (q : G →* Equiv.Perm (Fin 7)) (hq : Function.Surjective q)
      (hk : q.ker = centralizer (U : Set G)),
    K.map q = alternatingGroup (Fin 7) ∧
    ∃ E : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7),
      ∀ a v, E (NormalElementaryQuotient.representation U q hq hk a v) =
        BinaryPermutation.naturalRepresentation (Fin 7) a (E v)) ∨
  (∃ (q : G →* alternatingGroup (Fin 7)), Function.Surjective q ∧
    q.ker = centralizer (U : Set G) ∧ K.map q = ⊤ ∧
    Module.finrank (ZMod 2) (Additive U) = 4)

/-- Selection and typing, after constructing the full original module action. -/
theorem block_types_of_wholeModule
    (K U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hK : K.IsCComponent) (hf : generalizedFitting G = pCore 2 G)
    (hfK : generalizedFitting K = pCore 2 K) (P : Sylow 2 G)
    (hprod : ∀ g : G, ∃ k ∈ K, ∃ t ∈ (P : Subgroup G), k*t=g)
    (hno : ∀ D : Subgroup (ChapterB.baumann (P : Subgroup G)),
      D.Characteristic → D ≠ ⊥ → ¬ (D.map (ChapterB.baumann (P : Subgroup G)).subtype).Normal)
    (hm : ⁅U,K⁆ = U) (hfix : U ⊓ centralizer (K : Set G) = ⊥)
    (hmodel : WholeModule K U) :
    IsAlternatingBlock K 7 ∨ IsExceptionalA7Block K := by
  have hfalse : (∃ D : Subgroup (ChapterB.baumann (P : Subgroup G)),
      D.Characteristic ∧ D ≠ ⊥ ∧ (D.map (ChapterB.baumann (P : Subgroup G)).subtype).Normal) → False := by
    rintro ⟨D,hD,hne,hn⟩
    exact hno D hD hne hn
  rcases hmodel with ⟨q,hq,hk,hKq,E,he⟩ | ⟨q,hq,hk,hKq,hd⟩
  · have hc : Nat.card U = 2 ^ 6 := by
      rw [←Nat.card_congr Additive.toMul, Nat.card_congr E.toEquiv,
        Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        BinaryPermutation.finrank_natural_odd (Fin 7) (by decide), Fintype.card_fin]
    have hne : U ≠ ⊥ := by intro hh; rw [hh,card_bot] at hc; norm_num at hc
    have hcod : ∀ A, fixedCodim (NormalElementaryQuotient.representation U q hq hk) A =
        fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) A := by
      intro A
      simpa only [Subgroup.map_id] using fixedCodim_map_equivariant
        (NormalElementaryQuotient.representation U q hq hk)
        (BinaryPermutation.naturalRepresentation (Fin 7)) (MonoidHom.id _) E he A
    have hlift : ∀ a v, E.symm (BinaryPermutation.naturalRepresentation (Fin 7) a v) =
        NormalElementaryQuotient.representation U q hq hk a (E.symm v) := by
      intro a v
      apply E.injective
      rw [E.apply_symm_apply,he,E.apply_symm_apply]
    have hb := (Natural.normal_characteristic_or_block_of_natural_seven_linear
      K U hK hf hfK P hprod q hq hk hKq hcod E.symm.toLinearMap E.symm.injective
      hlift (hm.symm ▸ hne)).resolve_left hfalse
    exact Or.inl (ordinary_block_of_full_six K U hb hm hfix hc q hk
      (MulEquiv.subgroupCongr hKq))
  · have hc : Nat.card U = 2 ^ 4 := by
      rw [←Nat.card_congr Additive.toMul,
        Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,hd]
    have hne : U ≠ ⊥ := by intro hh; rw [hh,card_bot] at hc; norm_num at hc
    have hb := (normal_characteristic_or_block_of_exceptional_seven
      K U hK hf hfK P hprod q hq hk hKq hd (hm.symm ▸ hne)).resolve_left hfalse
    exact Or.inr (exceptional_block_of_full_four K U hb hm hfix hc q hk
      ((MulEquiv.subgroupCongr hKq).trans (Subgroup.topEquiv)))

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
