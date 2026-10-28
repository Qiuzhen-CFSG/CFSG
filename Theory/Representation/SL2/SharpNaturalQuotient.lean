module
public import Theory.Representation.SL2.SharpSylowCovering
/-!
# Natural coordinates from sharp Sylow fixed indices

Two generating Sylows of SL₂(2ⁿ) with fixed codimension n recognize the
quotient by all ambient fixed vectors as exactly one natural module.
Sharp fixed-space generation gives natural copies; its already proved
order q² forces multiplicity one. The matrix actors and the full fixed
kernel are preserved without selecting a complement.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 2.9, p.33;
Aschbacher--Smith G.1.6--7, pp.329--330. The original Niles core-center
application is in `Glauberman.PushingUpSL2DegreeNaturalCenter`.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender Representation.SL2SylowFixedRecognition
open scoped MatrixGroups
namespace Representation.SL2
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V] [Finite V]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

theorem sharp_sylow_natural_quotient (ρ : Representation (ZMod 2) SL(2,F) V)
    (hnt : ∃ g, ρ g ≠ 1) {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (R T : Sylow 2 SL(2,F)) (hgen : (R : Subgroup SL(2,F)) ⊔ T = ⊤)
    (hR : fixedCodim ρ R = n) (hT : fixedCodim ρ T = n) :
    ∃ E : (V ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ g v, E (centralQuotient ρ g v) = Matrix.mulVec g.val (E v) := by
  obtain ⟨_,htotal,hyp⟩ := sharp_sylow_fixed_spaces ρ hnt hn hF R T hgen hR hT
  obtain ⟨m,e,he⟩ := natural_centralQuotient ρ R hyp n (by omega) hF
  have hc : Nat.card (V ⧸ fixedSpace ρ ⊤) = Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),show Nat.card (ZMod 2) = 2 by simp [Nat.card_eq_fintype_card],
      show Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ ⊤) = 2*n from htotal,hF,←pow_mul]
    rw [Nat.mul_comm]
  have hm : m = 1 := by
    have hh := Nat.card_congr e.toEquiv
    rw [hc,Nat.card_fun,Nat.card_fun,Nat.card_fin,Nat.card_fin,←pow_mul] at hh
    have hlarge : 1 < Nat.card F := by rw [hF]; exact one_lt_pow₀ (by decide) (by omega)
    have hh' := Nat.pow_right_injective hlarge hh
    omega
  subst m
  refine ⟨e.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 2 → F)),?_⟩
  intro g v
  exact he g v 0
end Representation.SL2
