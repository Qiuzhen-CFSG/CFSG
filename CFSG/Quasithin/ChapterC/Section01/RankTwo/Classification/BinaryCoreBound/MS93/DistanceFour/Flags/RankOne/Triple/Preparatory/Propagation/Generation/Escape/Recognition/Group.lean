module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.Recognition.Linear

/-!
# The split natural section on the elementary quotient group

The subgroup/vector-space correspondence identifies the actual displacement
subgroup and common fixed subgroup with the linear commutator and fixed spaces.
The cyclic displacement order gives rank one. The linear recognition theorem
then transfers to a multiplicative equivalence on the literal moving subgroup,
with its actual action equation and complementary fixed subgroup.

Source: Meierfrankenfeld--Stellmacher (1993), c(U)=1 on p.881 and the
natural-section inference in (4.6.8)(2), printed p.906.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation.Recognition
open ModuleAlternatives.CentralAttachments
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

/-- The subgroup/vector-space correspondence on the elementary quotient. -/
abbrev subspace : Subgroup E ≃o Submodule (ZMod 2) (Additive E) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

/-- The literal displacement subgroup of the whole action image. -/
abbrev moved (a : SL →* MulAut E) : Subgroup E := commutatorAction a.range E
/-- The common fixed subgroup of the whole action image. -/
abbrev fixed (a : SL →* MulAut E) : Subgroup E := FixedPoints.subgroup a.range E

omit [Finite E] in
/-- Linearization identifies the full displacement subgroup with the moving space. -/
theorem subspace_moved (a : SL →* MulAut E) :
    subspace (moved a) = (moving (Offenders.linearize a)).toSubmodule := by
  let ρ := Offenders.linearize a
  let D := (moving ρ).toSubmodule
  apply le_antisymm
  · have hle : moved a ≤ subspace.symm D := by
      rw [moved, commutatorAction_eq_closure, closure_le]
      rintro _ ⟨g, v, rfl⟩
      obtain ⟨s, hs⟩ := g.property
      change Additive.ofMul (v⁻¹ * g.val v) ∈ D
      rw [← hs]
      have hm := Coinvariants.sub_mem_ker (ρ := ρ) s (Additive.ofMul v)
      change -Additive.ofMul v + ρ s (Additive.ofMul v) ∈ Coinvariants.ker ρ
      simpa only [sub_eq_add_neg, add_comm] using hm
    exact (subspace.monotone hle).trans_eq (subspace.apply_symm_apply D)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change a g v.toMul / v.toMul ∈ moved a
    rw [div_eq_mul_inv, mul_comm]
    rw [moved, commutatorAction_eq_closure]
    exact subset_closure ⟨⟨a g, g, rfl⟩, v.toMul, rfl⟩

omit [Finite E] in
/-- Linearization preserves the literal common fixed subgroup. -/
theorem subspace_fixed (a : SL →* MulAut E) :
    subspace (fixed a) = fixedSpace (Offenders.linearize a) ⊤ := by
  ext v
  constructor
  · intro h g
    exact h ⟨a g, g, rfl⟩
  · intro h g
    obtain ⟨s, hs⟩ := g.property
    change g.val v.toMul = v.toMul
    rw [← hs]
    exact h ⟨s, mem_top s⟩

/-- Two displacement values bound the binary displacement rank by one. -/
theorem fixedCodim_le_one (a : SL →* MulAut E) (t : SL)
    (ht : Nat.card (commutatorAction (zpowers (a t)) E) = 2) :
    fixedCodim (Offenders.linearize a) (zpowers t) ≤ 1 := by
  let B := commutatorAction (zpowers (a t)) E
  have hcard : 2 ^ Module.finrank (ZMod 2) (subspace B) = 2 ^ 1 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subspace B)
    change Nat.card B = _ at hc
    rw [Nat.card_zmod, ht] at hc
    exact hc.symm
  have hdim : Module.finrank (ZMod 2) (subspace B) = 1 :=
    Nat.pow_right_injective (by decide : 1 < 2) hcard
  rw [fixedCodim_zpowers_eq_displacement_rank]
  have hle : LinearMap.range (Offenders.linearize a t - LinearMap.id) ≤ subspace B := by
    rintro v ⟨w, rfl⟩
    change a t w.toMul / w.toMul ∈ B
    rw [div_eq_mul_inv, mul_comm]
    dsimp only [B]
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨⟨a t, mem_zpowers _⟩, w.toMul, rfl⟩
  exact (Submodule.finrank_mono hle).trans_eq hdim

/-- A small involution in a faithful elementary action supplies actual natural
coordinates on the moving subgroup and a complementary fixed subgroup. -/
theorem group_split (a : SL →* MulAut E) (hf : Function.Injective a)
    (t : SL) (ht : t ^ 2 = 1) (hne : t ≠ 1)
    (hsmall : Nat.card (commutatorAction (zpowers (a t)) E) = 2) :
    ∃ (e : moved a ≃* Multiplicative (Fin 3 → ZMod 2)) (marking : SL ≃* SL),
      (∀ (g : SL) (x y : moved a), (y : E) = a g x →
        (e y).toAdd = (marking g).val.mulVec (e x).toAdd) ∧
      IsCompl (moved a) (fixed a) := by
  let ρ := Offenders.linearize a
  obtain ⟨e, marking, he, hc⟩ := linear_split ρ
    (Offenders.linearize_injective a hf) t ht hne (fixedCodim_le_one a t hsmall)
  let eD : moved a ≃* Multiplicative (moving ρ).toSubmodule := {
    toFun x := Multiplicative.ofAdd ⟨Additive.ofMul x.val, by
      rw [← subspace_moved a]
      exact x.property⟩
    invFun v := ⟨v.toAdd.val.toMul, by
      change v.toAdd.val ∈ subspace (moved a)
      rw [subspace_moved]
      exact v.toAdd.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  refine ⟨eD.trans e, marking, ?_, ?_⟩
  · intro g x y hy
    have heq : eD y = Multiplicative.ofAdd ((moving ρ).toRepresentation g (eD x).toAdd) := by
      apply congrArg Multiplicative.ofAdd
      apply Subtype.ext
      exact congrArg Additive.ofMul hy
    change (e (eD y)).toAdd = _
    rw [heq]
    exact he g (eD x).toAdd
  · apply subspace.isCompl_iff.mpr
    rw [subspace_moved, subspace_fixed]
    exact hc
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation.Recognition
