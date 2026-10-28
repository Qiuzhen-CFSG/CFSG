module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import Theory.Representation.BinaryPermutation.CoreFixedLine

/-!
# The original five-dimensional marking in13.4

The marking uses the actual chosen Irr⁺ subgroup and the literal projection
L → L/O₂,Z(L). Its equivariance identifies C_V(L) with the constant line
inside the six-point augmentation core. Thus |V|=32 and |C_V(L)|=2 are
conclusions, not additional geometric assumptions.

The preceding13.3.2 module classification must construct this marking from
C_V(L)≠1. The four-dimensional natural section is not the module used here.
Source: Aschbacher–Smith13.4.1–2, printed pp.896–897.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual equivariant augmentation-core marking supplied by13.3.2(3). -/
structure CoreMarking (D : ChosenModule T L V) where
  quotient : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6)
  coordinate : V ≃* Multiplicative (BinaryPermutation.core (Fin 6))
  equivariant : ∀ (l : L) (v : V),
    (coordinate (V.normalizerMonoidHom ⟨l.val, D.normalizes l.property⟩ v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6)
        (quotient (QuotientGroup.mk' (centralCore L) l)).val (coordinate v).toAdd

namespace CoreMarking
variable {D : ChosenModule T L V} (m : CoreMarking D)
include m

/-- Membership in the actual fixed subgroup is precisely the constant-vector test. -/
theorem mem_fixed_iff (v : V) :
    v.val ∈ centralizer (L : Set G) ↔
      (m.coordinate v).toAdd.val ∈ BinaryPermutation.constants (Fin 6) := by
  rw [← BinaryPermutation.core_fixed_iff_constant (by simp) (m.coordinate v).toAdd]
  constructor
  · intro hv a
    obtain ⟨q, rfl⟩ := m.quotient.surjective a
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) q
    rw [← m.equivariant]
    congr 2
    apply Subtype.ext
    change l.val * v.val * l.val⁻¹ = v.val
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hv l.val l.property)
  · intro hv
    apply mem_centralizer_iff.mpr
    intro l hl
    have he := (m.equivariant ⟨l, hl⟩ v).trans
      (hv (m.quotient (QuotientGroup.mk' (centralCore L) ⟨l, hl⟩)))
    have hx := m.coordinate.injective (Multiplicative.toAdd.injective he)
    have hh := congrArg Subtype.val hx
    exact mul_inv_eq_iff_eq_mul.mp hh

/-- The equivalence uses the same V and coordinate map as the source marking. -/
def fixedEquiv : (V ⊓ centralizer (L : Set G) : Subgroup G) ≃
    BinaryPermutation.coreConstants (Ω := Fin 6) where
  toFun v := ⟨(m.coordinate ⟨v.val, v.property.1⟩).toAdd,
    (m.mem_fixed_iff ⟨v.val, v.property.1⟩).mp v.property.2⟩
  invFun w := ⟨(m.coordinate.symm (Multiplicative.ofAdd w.val)).val,
    (m.coordinate.symm (Multiplicative.ofAdd w.val)).property,
    (m.mem_fixed_iff _).mpr (by
      rw [m.coordinate.apply_symm_apply]
      exact w.property)⟩
  left_inv v := by simp
  right_inv w := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (m.coordinate.apply_symm_apply _)

theorem card_fixed : Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) = 2 := by
  rw [Nat.card_congr m.fixedEquiv]
  exact BinaryPermutation.card_coreConstants (by decide)

theorem fixed_ne_bot : V ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro he
  have hc := m.card_fixed
  rw [he, card_bot] at hc
  omega

theorem card_module : Nat.card V = 32 := by
  rw [Nat.card_congr m.coordinate.toEquiv]
  change Nat.card (BinaryPermutation.core (Fin 6)) = 32
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    BinaryPermutation.finrank_core]
  rfl

end CoreMarking
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
