module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# The fixed-space action in the M₁₂ elementary-sixteen calculation

An element commuting with an involution and fixing its fixed space has square
one in a faithful binary representation. Consequently an order-five element
of the centralizer acts nontrivially on that space. Its displacement is divisible
by four. If it is a commutator [z,g], the commutator rank inequality forces z to
move at least two dimensions. On the five-dimensional outer fixed space this
gives the common fixed-space bound three.

This proves the action calculation used in Aschbacher–Smith H.11.1(4), printed
pp.392–393, combined manuscript of 1 March 2004. The subgroup placement and the
order-five commutator are separate group-theoretic inputs, not module bounds.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.FixedPairs
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private theorem add_self (v : V) : v + v = 0 := by
  simpa only [add_smul, one_smul, zero_smul] using
    congrArg (fun c : ZMod 2 => c • v) (by decide : (1 : ZMod 2) + 1 = 0)

private theorem commute_apply (ρ : Representation (ZMod 2) G V) {t x : G}
    (hc : Commute t x) (v : V) : ρ t (ρ x v) = ρ x (ρ t v) := by
  simpa only [map_mul, Module.End.mul_apply] using congrArg (fun g => ρ g v) hc.eq

/-- The pointwise kernel of the centralizer on an involution fixed space has exponent two. -/
private theorem square_eq_one_of_fixes (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {t x : G} (ht : t ^ 2 = 1) (hc : Commute t x)
    (hf : ∀ v ∈ fixedSpace ρ (zpowers t), ρ x v = v) : x ^ 2 = 1 := by
  have ht2 (v : V) : ρ t (ρ t v) = v := by
    simpa only [pow_two, map_mul, map_one, Module.End.mul_apply, Module.End.one_apply]
      using congrArg (fun g => ρ g v) ht
  have hw (v : V) : ρ t v + v ∈ fixedSpace ρ (zpowers t) := by
    rw [mem_fixedSpace_zpowers_iff, map_add, ht2, add_comm]
  have hv (v : V) : ρ x v + v ∈ fixedSpace ρ (zpowers t) := by
    rw [mem_fixedSpace_zpowers_iff, map_add, commute_apply ρ hc]
    have hh := hf _ (hw v)
    rw [map_add] at hh
    have he : ρ x (ρ t v) = (ρ t v + v) + ρ x v := by
      calc
        _ = (ρ x (ρ t v) + ρ x v) + ρ x v := by
          rw [add_assoc, add_self, add_zero]
        _ = _ := congrArg (· + ρ x v) hh
    rw [he]
    calc
      _ = (ρ t v + ρ t v) + (ρ x v + v) := by abel
      _ = _ := by rw [add_self, zero_add]
  apply hρ
  ext v
  have hh := hf _ (hv v)
  rw [map_add] at hh
  change ρ (x ^ 2) v = ρ 1 v
  simp only [pow_two, map_mul, map_one, Module.End.mul_apply, Module.End.one_apply]
  exact add_right_cancel (hh.trans (add_comm _ _))

private theorem centralizer_stabilizes (ρ : Representation (ZMod 2) G V) (t : G) :
    centralizer ({t} : Set G) ≤ subspaceStabilizer ρ (fixedSpace ρ (zpowers t)) := by
  apply le_subspaceStabilizer
  intro x hx v hv
  rw [mem_fixedSpace_zpowers_iff] at hv ⊢
  rw [commute_apply ρ (mem_centralizer_singleton_iff.mp hx).symm, hv]

private noncomputable def centralizerRepresentation (ρ : Representation (ZMod 2) G V) (t : G) :
    Representation (ZMod 2) (centralizer ({t} : Set G)) (fixedSpace ρ (zpowers t)) :=
  (stabilizerRepresentation ρ _).comp (Subgroup.inclusion (centralizer_stabilizes ρ t))

private noncomputable def centralizer_fixed_equiv (ρ : Representation (ZMod 2) G V) (t : G)
    (z : centralizer ({t} : Set G)) :
    fixedSpace (centralizerRepresentation ρ t) (zpowers z) ≃ₗ[ZMod 2]
      (fixedSpace ρ (zpowers t) ⊓ fixedSpace ρ (zpowers (z : G)) : Submodule (ZMod 2) V) where
  toFun v := ⟨v.val.val, v.val.property, by
    have hv := (mem_fixedSpace_zpowers_iff _ _ _).mp v.property
    exact (mem_fixedSpace_zpowers_iff _ _ _).mpr (congrArg Subtype.val hv)⟩
  invFun v := ⟨⟨v.val, v.property.1⟩, by
    rw [mem_fixedSpace_zpowers_iff]
    apply Subtype.ext
    exact (mem_fixedSpace_zpowers_iff _ _ _).mp v.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [FiniteDimensional (ZMod 2) V]
private theorem four_le_restricted_five (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {t : G} (ht : t ^ 2 = 1)
    (x : centralizer ({t} : Set G)) (hx : orderOf x = 5) :
    4 ≤ fixedCodim (centralizerRepresentation ρ t) (zpowers x) := by
  have hd := four_dvd_fixedCodim_of_order_five (centralizerRepresentation ρ t) x hx
  have hn : fixedCodim (centralizerRepresentation ρ t) (zpowers x) ≠ 0 := by
    intro hz
    have hf := (fixedCodim_eq_zero_iff _ _).mp hz
    have hs : (x : G) ^ 2 = 1 := square_eq_one_of_fixes ρ hρ ht
      (mem_centralizer_singleton_iff.mp x.property).symm (by
        intro v hv
        have hmem : (⟨v, hv⟩ : fixedSpace ρ (zpowers t)) ∈
            fixedSpace (centralizerRepresentation ρ t) (zpowers x) := by rw [hf]; trivial
        exact congrArg Subtype.val ((mem_fixedSpace_zpowers_iff _ _ _).mp hmem))
    have ho : orderOf (x : G) ∣ 2 := orderOf_dvd_of_pow_eq_one hs
    rw [Subgroup.orderOf_coe, hx] at ho
    norm_num at ho
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd

theorem common_fixed_finrank_le_three (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {t : G} (ht : t ^ 2 = 1)
    (z g : centralizer ({t} : Set G)) (hc : orderOf (z * g * z⁻¹ * g⁻¹) = 5)
    (hdim : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) = 5) :
    Module.finrank (ZMod 2)
      (fixedSpace ρ (zpowers t) ⊓ fixedSpace ρ (zpowers (z : G)) : Submodule (ZMod 2) V) ≤ 3 := by
  have hlo := four_le_restricted_five ρ hρ ht _ hc
  have hhi := fixedCodim_commutator_le_twice (centralizerRepresentation ρ t) z g
  have hd := fixedCodim_add_finrank (centralizerRepresentation ρ t) (zpowers z)
  rw [hdim, (centralizer_fixed_equiv ρ t z).finrank_eq] at hd
  omega
end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.FixedPairs
