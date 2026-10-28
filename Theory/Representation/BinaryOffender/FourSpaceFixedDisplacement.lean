module
public import Theory.Representation.BinaryOffender.SmallFixedCodimension
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.ElementaryAbelian.Injective

/-!
# Displacement on a proper fixed space in binary dimension four

If an elementary actor fixes exactly a line in a faithful four-space, its
action on the fixed space of any nontrivial subgroup is quadratic: that
proper space has dimension at most three and still has the same fixed line.
Consequently every restricted displacement lies in the original fixed line.

Source application: MS93 (3.6), printed p.871, the maximal critical plane.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The larger elementary actor sends a proper fixed space into its fixed line
by displacement. -/
theorem displacement_fixed_of_proper_fixedSpace
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 4)
    {A B : Subgroup G} [IsElementaryAbelian 2 B]
    (hAB : A ≤ B) (hA : A ≠ ⊥)
    (hB : Module.finrank (ZMod 2) (fixedSpace ρ B) = 1) :
    ∀ b ∈ B, ∀ v ∈ fixedSpace ρ A, ρ b v-v ∈ fixedSpace ρ B := by
  let D := fixedSpace ρ A
  have hstable (b : B) {v : V} (hv : v ∈ D) : ρ b v ∈ D := by
    intro a
    have hc : (a : G)*(b : G) = (b : G)*(a : G) :=
      congrArg Subtype.val (mul_comm' (⟨a,hAB a.property⟩ : B) b)
    change ρ a (ρ b v) = ρ b v
    have hfix : ρ (a : G) v = v := hv a
    rw [←Module.End.mul_apply,←map_mul,hc,map_mul,Module.End.mul_apply,hfix]
  let P : Subrepresentation (ρ.comp B.subtype) := ⟨D,hstable⟩
  have hDne : D ≠ ⊤ := by
    intro he
    apply hA
    apply eq_bot_iff.mpr
    intro a ha
    apply hρ
    ext v
    have hv : v ∈ D := he ▸ Submodule.mem_top
    exact (hv ⟨a,ha⟩).trans (LinearMap.congr_fun (map_one ρ).symm v)
  have hDdim : Module.finrank (ZMod 2) P.toSubmodule ≤ 3 := by
    have hh := Submodule.finrank_lt hDne
    rw [hdim] at hh
    exact Nat.le_of_lt_succ hh
  let e : fixedSpace P.toRepresentation (⊤ : Subgroup B) ≃ₗ[ZMod 2]
      fixedSpace ρ B := {
    toFun x := ⟨x.val.val,fun b => congrArg Subtype.val (x.property ⟨b,mem_top b⟩)⟩
    invFun x := ⟨⟨x.val,fun a => x.property ⟨a,hAB a.property⟩⟩,fun b => Subtype.ext (x.property b.val)⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hfixed : Module.finrank (ZMod 2) (fixedSpace P.toRepresentation (⊤ : Subgroup B)) = 1 :=
    e.finrank_eq.trans hB
  have hcodim : fixedCodim P.toRepresentation (⊤ : Subgroup B) ≤ 2 := by
    have hh := fixedCodim_add_finrank P.toRepresentation (⊤ : Subgroup B)
    rw [hfixed] at hh
    omega
  let : IsElementaryAbelian 2 (⊤ : Subgroup B) := IsElementaryAbelian.of_injective
    (⊤ : Subgroup B).subtype (⊤ : Subgroup B).subtype_injective
  have hquad := isQuadratic_of_fixedCodim_le_two P.toRepresentation hcodim
  intro b hb v hv a
  exact congrArg Subtype.val (hquad a (mem_top a) ⟨b,hb⟩ (mem_top _) ⟨v,hv⟩)
end Representation.BinaryOffender
