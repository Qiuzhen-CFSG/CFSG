module
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.ElementaryAbelian.Injective

/-!
# Recovering an omega pair from an embedded linear block

In a finite group where an involution determines its Sylow two-subgroup,
an embedded SL₂(k) containing a full omega root and an involution of another
Sylow contains that second full omega root, when its order is |k|. A Sylow
of the block through the involution embeds into the unique ambient Sylow;
its elementary exponent and field order force equality with the omega root.

This is the group-theoretic bridge from the unitary Sylow–involution model
to the two-center actor in DGS85, Groups and Graphs (1985), (11.3),
printed pp.169–171. The concrete application retains both unitary carriers.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Subgroup
variable {G k : Type*} [Group G] [Finite G] [Field k] [Finite k] [CharP k 2]

private theorem linear_sylow_card (e : G ≃* SL(2,k)) (S : Sylow 2 G) :
    Nat.card S = Nat.card k := by
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  exact (Nat.card_congr ((S : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).trans
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T).symm.toEquiv)

private theorem linear_sylow_square (e : G ≃* SL(2,k)) (S : Sylow 2 G) (s : S) : s^2=1 := by
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let f := ((S : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T).symm
  apply f.injective
  rw [map_pow,map_one]
  change (2 : ℕ) • (f s).toAdd = 0
  rw [two_nsmul]
  exact CharTwo.add_self_eq_zero _

/-- An embedded binary linear group has no smaller Sylow containing a
p-subgroup of field order. -/
theorem sylow_of_linear_card (e : G ≃* SL(2,k)) (A : Subgroup G)
    (hp : IsPGroup 2 A) (hc : Nat.card A = Nat.card k) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = A := by
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  exact ⟨S,(eq_of_le_of_card_ge hS (by rw [linear_sylow_card e S,hc])).symm⟩

/-- A full root and an outside involution generating a binary linear block
already contain the entire second omega group, provided involutions have
unique ambient Sylows and the omega groups have the linear field order. -/
theorem omega_pair_eq_of_linear_block (R T : Sylow 2 G)
    (htwo : ∀ S U : Sylow 2 G, ∀ t : G, t ∈ S → t ∈ U → t ≠ 1 → t^2=1 → S=U)
    (t : G) (ht : t ∈ T) (ht1 : t ≠ 1) (ht2 : t^2=1)
    (hcard : Nat.card (omegaOneAmbient (T : Subgroup G)) = Nat.card k)
    (e : (omegaOneAmbient (R : Subgroup G) ⊔ zpowers t : Subgroup G) ≃* SL(2,k)) :
    omegaOneAmbient (R : Subgroup G) ⊔ omegaOneAmbient (T : Subgroup G) =
      omegaOneAmbient (R : Subgroup G) ⊔ zpowers t := by
  let H := omegaOneAmbient (R : Subgroup G) ⊔ zpowers t
  let t₀ : H := ⟨t,mem_sup_right (mem_zpowers t)⟩
  have ht₀ : t₀^2=1 := Subtype.ext ht2
  have hp : IsPGroup 2 (zpowers t₀) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one ht₀).isPGroup
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hsT : (S : Subgroup H).map H.subtype ≤ T := by
    obtain ⟨U,hU⟩ := (S.isPGroup'.map H.subtype).exists_le_sylow
    have htU : t ∈ U := hU (mem_map_of_mem H.subtype (hS (mem_zpowers t₀)))
    exact htwo U T t htU ht ht1 ht2 ▸ hU
  have hsΩ : (S : Subgroup H).map H.subtype ≤ omegaOneAmbient (T : Subgroup G) := by
    rintro x ⟨s,hs,rfl⟩
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl s.val
      (hsT (mem_map_of_mem H.subtype hs))
    exact congrArg (fun z : S => ((z : H) : G)) (linear_sylow_square e S ⟨s,hs⟩)
  have heq : (S : Subgroup H).map H.subtype = omegaOneAmbient (T : Subgroup G) :=
    eq_of_le_of_card_ge hsΩ (by rw [card_map_of_injective H.subtype_injective,
      linear_sylow_card e S,hcard])
  exact le_antisymm (sup_le le_sup_left (heq ▸ map_subtype_le _))
    (sup_le le_sup_left ((zpowers_le.mpr
      ((omegaOneAmbient_le_iff _ _).mp le_rfl t ht ht2)).trans le_sup_right))
end Subgroup
