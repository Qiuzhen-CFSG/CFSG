module

public import Theory.Representation.SL2NaturalOffenders.Ratios
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The fixed and commutator line of a natural SL₂ Sylow subgroup

Quadraticity puts every displacement in the common fixed space. A nonidentity
matrix fixes at most one field line, so its displacement already has the
common fixed space's binary dimension. Thus [V,P]=C_V(P), with dimension equal
to the binary degree of the defining field. The equality is for the literal
ambient image of the specified Sylow subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.1.1,
printed p.454.
-/

public section
namespace Representation.SL2NaturalOffenders.Ratios
open Representation.BinaryOffender
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group H] [Finite H]
  (L : Subgroup H) (e : L ≃* NoStrong.Actor F)
  (ρ : Representation (ZMod 2) H (Fin 2 → F))
  (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
include e hnat

/-- Both common subspaces are the same line over the defining field. -/
theorem sylowImage_commutator_eq_fixedSpace (P : Sylow 2 L) :
    subspaceCommutator ρ ⊤ ((P : Subgroup L).map L.subtype) =
      fixedSpace ρ ((P : Subgroup L).map L.subtype) := by
  let A := (P : Subgroup L).map L.subtype
  have hA := sylowImage_offender L e ρ hnat P
  have hq := sylowImage_quadratic L e ρ hnat P
  have hle : subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩ b
    exact hq b b.property a ha v
  apply Submodule.eq_of_le_of_finrank_le hle
  have hdim : Module.finrank (ZMod 2) (Fin 2 → F) =
      2 * Module.finrank (ZMod 2) F := by simp [Module.finrank_pi_fintype, two_mul]
  have hcod := sylowImage_fixedCodim L e ρ hnat P
  have hfix := fixedCodim_add_finrank ρ A
  rw [hdim] at hfix
  obtain ⟨⟨a, ha⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
  have ha1 : a ≠ 1 := fun h => hne (Subtype.ext h)
  have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
  have hc := fixedSpace_card_le_of_le L e ρ hnat
    (Subgroup.zpowers_ne_bot.mpr ha1) (hzA.trans (Subgroup.map_subtype_le _))
  have hpow : 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers a)) ≤
      2 ^ Module.finrank (ZMod 2) F := by
    have hC : Nat.card (fixedSpace ρ (Subgroup.zpowers a)) =
        2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers a)) := by
      simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := fixedSpace ρ (Subgroup.zpowers a)))
    have hF : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
      simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F))
    rwa [← hC, ← hF]
  have hfixa := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  have haDim := fixedCodim_add_finrank ρ (Subgroup.zpowers a)
  rw [hdim, fixedCodim_zpowers_eq_displacement_rank] at haDim
  have hra : LinearMap.range (ρ a - LinearMap.id) ≤ subspaceCommutator ρ ⊤ A := by
    rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨a, ha, v, Submodule.mem_top, rfl⟩
  have hdle := Submodule.finrank_mono hra
  change fixedCodim ρ A = Module.finrank (ZMod 2) F at hcod
  omega

end Representation.SL2NaturalOffenders.Ratios
