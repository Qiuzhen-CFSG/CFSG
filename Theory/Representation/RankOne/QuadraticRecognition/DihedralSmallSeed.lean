module
public import Theory.Representation.RankOne.QuadraticRecognition.SmallFixedSeed
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.BinaryOffender.DihedralDisplacement
import all Theory.Representation.BinaryOffender.DihedralDisplacement

/-!
# A small fixed seed for an order-ten dihedral action

Let a nontrivial elementary binary subgroup B fix a seed C of order at most
two, contain all its displacements in C, and have the conjugates of C span
the module. Two conjugates of B generate D10, so the seed-pair bound limits
the module to two binary dimensions. An order-five image would move at
least four dimensions, hence the rotation acts trivially. Every actor now
fixes C, and generation makes the entire action trivial.

No faithfulness of the original action is assumed. The faithful action
image is used only for the prime-order displacement bound. The existing
finite dihedral generation calculation is reused privately; no private
declaration enters the public statement.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
the small-module step of (12.3), printed p.180. The literal graph consumer
is CommutingThreeProfile.DihedralExclusion.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.RankOne.QuadraticRecognition
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

/-- A fixed generating seed of order at most two cannot support a nontrivial D10 action with these displacement bounds. -/
theorem dihedral_small_seed_trivial
    (ρ : Representation (ZMod 2) (DihedralGroup 5) W)
    (B : Subgroup (DihedralGroup 5)) [IsElementaryAbelian 2 B] (hne : B ≠ ⊥)
    (C : Submodule (ZMod 2) W)
    (hfix : C ≤ fixedSpace ρ B)
    (hseed : (⨆ a : DihedralGroup 5, C.map (ρ a)) = ⊤)
    (hmove : subspaceCommutator ρ ⊤ B ≤ C)
    (hcard : Nat.card C ≤ 2) : ρ = 1 := by
  obtain ⟨t,ht,ht1⟩ := B.bot_or_exists_ne_one.resolve_left hne
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hpair : B ⊔ B.map (MulAut.conj (DihedralGroup.r 1)).toMonoidHom = ⊤ := by
    apply top_unique
    rw [← DihedralGroup.two_conjugates_generate_small (Or.inr rfl) t ht1 ht2]
    apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    fin_cases j
    · simpa using (show t ∈ B ⊔ B.map (MulAut.conj (DihedralGroup.r 1)).toMonoidHom from
        (show B ≤ B ⊔ B.map (MulAut.conj (DihedralGroup.r 1)).toMonoidHom from le_sup_left) ht)
    · exact (show B.map (MulAut.conj (DihedralGroup.r 1)).toMonoidHom ≤
        B ⊔ B.map (MulAut.conj (DihedralGroup.r 1)).toMonoidHom from le_sup_right)
        (mem_map_of_mem _ ht)
  have hd := seed_pair_degree_bound ρ B (DihedralGroup.r 1) C hpair hseed hmove
  have hdimC : Module.finrank (ZMod 2) C ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp
      (show 2 ^ Module.finrank (ZMod 2) C ≤ 2^1 from hcard)
  have hdim : Module.finrank (ZMod 2) W ≤ 2 := by omega
  have hr : actionHom ρ (DihedralGroup.r 1) = 1 := by
    have hp : (actionHom ρ (DihedralGroup.r 1))^5 = 1 := by
      rw [←map_pow,show (DihedralGroup.r 1 : DihedralGroup 5)^5 = 1 from by decide,map_one]
    have ho := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one hp)
    rcases ho with ho | ho
    · exact orderOf_eq_one_iff.mp ho
    · have hl := prime_order_le_fixedCodim (imageRepresentation ρ)
        (imageRepresentation_injective ρ) (by decide : Nat.Prime 5) (by decide)
        (actionHom ρ (DihedralGroup.r 1)) ho
      rw [BinaryPrimeDegree.orderOf_two_mod_five] at hl
      have hu := fixedCodim_add_finrank (imageRepresentation ρ)
        (zpowers (actionHom ρ (DihedralGroup.r 1)))
      omega
  have hr' : ρ (DihedralGroup.r 1) = 1 := by
    exact LinearMap.ext ((actionHom_eq_one_iff ρ _).mp hr)
  have hwords : ∀ a : DihedralGroup 5, ∃ j : Fin 5,
      a = (DihedralGroup.r 1)^ (j:ℕ) ∨ a = (DihedralGroup.r 1)^(j:ℕ) * t := by
    have hh : ∀ t : DihedralGroup 5, t ≠ 1 → t^2=1 → ∀ a : DihedralGroup 5,
        ∃ j : Fin 5, a = (DihedralGroup.r 1)^(j:ℕ) ∨ a = (DihedralGroup.r 1)^(j:ℕ)*t := by decide
    exact hh t ht1 ht2
  have hCfix (a : DihedralGroup 5) (v : W) (hv : v ∈ C) : ρ a v = v := by
    obtain ⟨j,rfl | rfl⟩ := hwords a
    · rw [map_pow,hr',one_pow]; rfl
    · rw [map_mul,map_pow,hr',one_pow,one_mul]
      exact hfix hv ⟨t,ht⟩
  have hC : C = ⊤ := by
    apply top_unique
    rw [←hseed]
    apply iSup_le
    intro a
    rintro _ ⟨v,hv,rfl⟩
    rw [hCfix a v hv]
    exact hv
  apply MonoidHom.ext
  intro a
  exact LinearMap.ext (fun v => hCfix a v (hC.symm ▸ Submodule.mem_top))
end Representation.RankOne.QuadraticRecognition
