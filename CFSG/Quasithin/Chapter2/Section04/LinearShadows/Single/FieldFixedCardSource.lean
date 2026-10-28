module
public import Theory.GroupTheory.ElementaryFixedCardinality
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionRootSource

/-!
# The order of the original field-fixed Thompson subgroup

The elementary two-core and the root quotient have square-root fixed groups.
Fixed quotient lifting makes their counts multiply, giving the exact order of
C_R(s) without choosing a descended block model. The final equivalence retains
the literal ambient centralizer and the original conjugation action.
Source: Aschbacher–Smith, Lemma 2.4.12(2), printed p.532.
-/
public section
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_field_thompson_centralizer_card_square
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    Nat.card (R ⊓ centralizer ({s}:Set G) : Subgroup G)^2=Nat.card R := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let N := (twoCore d.H).subgroupOf R
  let : N.Normal := source_field_core_normal d
  let α := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
  let hN : ∀ x ∈ N, α x ∈ N := source_field_actor_preserves_core d s hs.1
  let : IsElementaryAbelian 2 N := (source_field_elementary_layers d hG T hST hsingle hL hM hTM hu c).1
  have hs1 : s^2=1 := by simpa only [hs2] using pow_orderOf_eq_one s
  have hα : Function.Involutive α := by
    intro r
    apply Subtype.ext
    change s*(s*(r:G)*s⁻¹)*s⁻¹=(r:G)
    calc _ = (s*s)*(r:G)*(s*s)⁻¹ := by group
         _ = (r:G) := by rw [show s*s=1 from by simpa only [pow_two] using hs1]; simp
  have hc := Theory.GroupTheory.fixed_card_square_of_elementary_kernel N α hα hN
    (source_field_involution_core_fixed_card d hG T hST hsingle hL hM hTM hu c s hs hs2)
    (source_field_involution_sylow_quotient_fixed_card d hG T hST hsingle hL hM hTM hu c s hs hs2)
  let e : α.eqLocus (MonoidHom.id R) ≃ (R ⊓ centralizer ({s}:Set G) : Subgroup G) :=
    { toFun := fun a=>⟨a.val,a.val.property,by
        apply mem_centralizer_singleton_iff.mpr
        have hh := congrArg Subtype.val a.property
        change s*(a.val:G)*s⁻¹=(a.val:G) at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm⟩
      invFun := fun a=>⟨⟨a,a.property.1⟩,Subtype.ext
        (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp a.property.2).symm)⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  rwa [Nat.card_congr e] at hc
end CFSG.Quasithin.Chapter2.LinearShadows.Single
