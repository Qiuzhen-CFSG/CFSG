module
public import Theory.Representation.PSL3Two.DoubledPointOffenders
public import Theory.Representation.SL3DoubledNaturalOffenders
public import Theory.Representation.BinaryOffender.EndFieldTransfer
public import Theory.GroupTheory.PCoreImage

/-!
# Offenders on a point radical in the full doubled-natural normalizer

Let D contain the diagonal SL₃(2) component in its full linear normalizer.
A point whose component stabilizer is a natural point parabolic has no
nontrivial offender in O₂(D_v). Full-normalizer localization first places
an offender in the component. Pulling the radical back to SL₃(2) puts it
in the natural point radical, where the strict doubled fixed-space bound
contradicts the offender inequality.

This retains arbitrary multiplicity actions in D. The source application
is the larger radical O₂(L₁T) in Aschbacher–Smith 13.4.10(4), printed p.909,
using B.5.10(2), pp.107–109. No equality of D with its component is assumed.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.SL3DoubledNaturalOffenders
local notation "F" => ZMod 2
local notation "μ" => Representation.asGroupHom (representation (ZMod 2))

private theorem mu_injective : Function.Injective μ := by
  intro a b hab
  exact representation_injective F (congrArg Units.val hab)

@[expose] def binaryPoint (v : Space F) : Subgroup (Ambient F) where
  carrier := {g | action F g v = v}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change action F a (action F b v) = v; rw [hb,ha]
  inv_mem' := by
    intro a ha
    change action F a⁻¹ v = v
    have hh := congrArg (action F a⁻¹) ha
    simpa only [Representation.inv_self_apply] using hh.symm

private theorem fixed_card_pair (A : Subgroup (SL F)) :
    Nat.card (fixedSpace (action F) (A.map μ)) =
      Nat.card (fixedSpace (BinaryLinearThree.W.prod BinaryLinearThree.W) A) := by
  apply Nat.card_congr
  exact {
    toFun := fun v => ⟨(v.val 0,v.val 1),fun a => by
      have hh := v.property ⟨μ a.val,mem_map_of_mem μ a.property⟩
      exact Prod.ext (congrFun hh 0) (congrFun hh 1)⟩
    invFun := fun v => ⟨![v.val.1,v.val.2],fun a => by
      obtain ⟨g,hg,hga⟩ := a.property
      change action F a.val ![v.val.1,v.val.2] = _
      rw [←hga]
      have hh := v.property ⟨g,hg⟩
      funext i
      fin_cases i
      · exact congrArg Prod.fst hh
      · exact congrArg Prod.snd hh⟩
    left_inv := fun v => by apply Subtype.ext; funext i; fin_cases i <;> rfl
    right_inv := fun v => rfl }

/-- Even in an overgroup of the doubled component, the point radical has
no nontrivial offender. The point marking uses the literal component map. -/
theorem binary_point_radical_offender_eq_bot
    (D : Subgroup (Ambient F)) (hDN : D ≤ normalizer F)
    (hCD : component F ≤ D) (v : Space F)
    (w : BinaryLinearThree.Vector) (hw : w ≠ 0)
    (hpoint : (binaryPoint v).comap μ = BinaryLinearThree.naturalPoint w)
    (A : Subgroup (Ambient F))
    (hAR : A ≤ (D ⊓ binaryPoint v : Subgroup (Ambient F)).pCoreIn 2)
    (hA : IsOffender (action F) A) : A = ⊥ := by
  let : Finite (Module.End F (Space F)) := Finite.of_injective
    (fun a : Module.End F (Space F) => (a : Space F → Space F)) DFunLike.coe_injective
  let P := D ⊓ binaryPoint v
  let R := P.pCoreIn 2
  have hAC : A ≤ component F := offender_le_component_of_le_normalizer
    (by simp : Nat.card F = 2 ^ 1) (by decide) (by decide) hA
    (hAR.trans ((pCoreIn_le 2 P).trans (inf_le_left.trans hDN)))
  let B := A.comap μ
  have hmap : B.map μ = A := map_comap_eq_self hAC
  have hRP : R.comap μ ≤ BinaryLinearThree.naturalPoint w := by
    rw [←hpoint]
    exact comap_mono ((pCoreIn_le 2 P).trans inf_le_right)
  have hp : IsPGroup 2 (R.comap μ) := (isPGroup_pCoreIn 2 P).of_injective
    ((μ).subgroupComap R) (by intro a b hh; exact Subtype.ext (mu_injective (congrArg Subtype.val hh)))
  have hn : BinaryLinearThree.naturalPoint w ≤ Subgroup.normalizer (R.comap μ : Set (SL F)) := by
    rw [←hpoint]
    intro g hg
    apply mem_normalizer_iff.mpr
    intro x
    have hgP : μ g ∈ P := ⟨hCD ⟨g,rfl⟩,hg⟩
    have hgR := (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))) hgP
    change μ x ∈ R ↔ μ (g*x*g⁻¹) ∈ R
    simpa only [map_mul,map_inv] using (show μ x ∈ R ↔ μ g * μ x * (μ g)⁻¹ ∈ R from
      mem_normalizer_iff.mp hgR (μ x))
  have hBR : B ≤ (BinaryLinearThree.naturalPoint w).pCoreIn 2 :=
    (comap_mono hAR).trans (le_pCoreIn_of_normalizes hp hRP hn)
  by_contra hne
  have hBne : B ≠ ⊥ := fun hh => hne (hmap.symm.trans (hh ▸ map_bot μ))
  have hlo := (EndFieldTransfer.offender_iff_card (action F) A hA.1).mp hA
  have hcard : Nat.card (Space F) = 64 := by simp [Space,Natural]
  rw [hcard,←hmap,card_map_of_injective mu_injective,fixed_card_pair,mul_comm] at hlo
  exact (not_lt_of_ge hlo) (BinaryLinearThree.doubled_point_radical_fixed_card_lt w hw B hBR hBne)
end Representation.SL3DoubledNaturalOffenders
