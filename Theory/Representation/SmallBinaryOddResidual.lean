module
public import Theory.Representation.BinarySymmetricThreeNormalizer
public import Theory.Representation.SmallBinaryPrimeNormalizer
public import Theory.GroupTheory.PResidual.SymmetricThreeProducts
public import Theory.GroupTheory.PResidual.Quotient
/-!
# Odd two-residuals of small faithful binary actions

A binary plane has symmetric-three automorphism group. A fully moved normal
symmetric-three actor in dimension four embeds its ambient group in a product
of two symmetric-three groups. A normal five-group in dimension four has odd
centralizer and a two-group conjugation image. Each case has odd two-residual.

These bounds supply the literal image deductions in Aschbacher–Smith 15.1.6.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace Representation.SmallBinaryOddResidual
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem odd_of_permThree_product {ι : Type*}
    (f : G →* (ι → Equiv.Perm (Fin 3))) (hf : Function.Injective f) :
    Odd (Nat.card (pResidual 2 G)) := by
  obtain ⟨n,hn⟩ := (pResidual_threeGroup_of_injective_permThree_product f hf).exists_card_eq
  rw [hn]
  exact (by decide : Odd 3).pow

theorem odd_twoResidual_of_dimension_two
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 2) : Odd (Nat.card (pResidual 2 G)) := by
  let b : V ≃ₗ[ZMod 2] BinaryFourPlus.Plane :=
    (Module.finBasisOfFinrankEq (ZMod 2) V hdim).equivFun
  let a := LinearMap.GeneralLinearGroup.congrLinearEquiv b
  let l := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryFourPlus.Plane
  let f : G →* Equiv.Perm (Fin 3) := BinaryFourPlus.planeAutEquiv.toMonoidHom.comp
    (l.toMonoidHom.comp (a.toMonoidHom.comp ρ.asGroupHom))
  have hfi : Function.Injective f := by
    apply BinaryFourPlus.planeAutEquiv.injective.comp
    apply l.injective.comp
    apply a.injective.comp
    intro x y he
    exact hf (congrArg Units.val he)
  exact odd_of_permThree_product (MonoidHom.pi fun _ : Unit => f)
    (fun x y h => hfi (congrFun h ()))

theorem odd_twoResidual_of_normal_symmetricThree
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 2 ∨ Module.finrank (ZMod 2) V = 4)
    (H : Subgroup G) [H.Normal] (j : H ≃* Equiv.Perm (Fin 3))
    (hfull : subspaceCommutator (ρ.comp H.subtype) ⊤ ⊤ = ⊤) :
    Odd (Nat.card (pResidual 2 G)) := by
  rcases hdim with hdim | hdim
  · exact odd_twoResidual_of_dimension_two ρ hf hdim
  let σ := ρ.comp (H.subtype.comp j.symm.toMonoidHom)
  have hσ : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    change subspaceCommutator ((ρ.comp H.subtype).comp j.symm.toMonoidHom) ⊤ ⊤ = ⊤
    rw [subspaceCommutator_comp_map,map_top_of_surjective _ j.symm.surjective]
    exact hfull
  obtain ⟨f,hfi,_⟩ := BinarySymmetricThreeNormalizer.exists_pair_embedding ρ hf hdim H j
    (BinarySymmetricThreeNormalizer.fixedFree_of_full σ hσ)
  let q : G →* (Bool → Equiv.Perm (Fin 3)) :=
    MonoidHom.pi fun b => if b then (MonoidHom.fst _ _).comp f else (MonoidHom.snd _ _).comp f
  apply odd_of_permThree_product q
  intro x y he
  apply hfi
  exact Prod.ext (congrFun he true) (congrFun he false)

theorem odd_twoResidual_of_normal_five
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (P : Subgroup G) [P.Normal] (hP : Nat.card P = 5) :
    Odd (Nat.card (pResidual 2 G)) := by
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.elementary (V := V)
  let := BinaryGroupAction.faithful ρ hf
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hV : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
    rfl
  have hodd : Odd (Nat.card (centralizer (P : Set G))) :=
    (by decide : Odd 15).of_dvd_nat (card_centralizer_five_dvd_fifteen (V := Multiplicative V) P hP hV)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hAut : IsPGroup 2 (MulAut P) := IsPGroup.of_card (n := 2) (by
    rw [IsCyclic.card_mulAut,hP]
    decide)
  have hle : pResidual 2 G ≤ centralizer (P : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer P]
    exact pResidual_le_ker_of_isPGroup 2 (MulAut.conjNormal : G →* MulAut P) hAut
  exact hodd.of_dvd_nat (card_dvd_of_le hle)
end Representation.SmallBinaryOddResidual
