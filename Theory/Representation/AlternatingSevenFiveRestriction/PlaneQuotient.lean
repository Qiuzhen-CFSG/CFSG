module
public import Theory.Representation.AlternatingSevenFiveRestriction.CoreEmbedding
/-!
# A natural SL₂ quotient cannot occur above the five-point core

An invariant subspace of dimension at least four in a six-space contains
its simple four-dimensional A₅ core. A natural plane quotient over F₄ has
kernel of dimension at most two, so this core injects into the quotient.
The cubic fixed-vector obstruction distinguishes the two modules.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Module Matrix
open scoped MatrixGroups
namespace BinaryPermutation.SevenPointChiefFactor
variable {V U F : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
theorem no_natural_plane_quotient (hF : Nat.card F = 4)
    (ρ : Representation (ZMod 2) Five V) (σ : Representation (ZMod 2) Five U)
    (j : core (Fin 5) →ₗ[ZMod 2] V) (hj : Function.Injective j)
    (hjact : ∀ a v, j (coreRepresentation (Fin 5) a.val v) = ρ a (j v))
    (hdim : finrank (ZMod 2) V = 6)
    (i : U →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (hiact : ∀ a v, i (σ a v) = ρ a (i v))
    (f : Five →* SL(2,F)) (hf : Function.Injective f)
    (k : U →ₗ[ZMod 2] (Fin 2 → F)) (hk : Function.Surjective k)
    (hkact : ∀ a v, k (σ a v) = (f a).val *ᵥ k v) : False := by
  have hdF : finrank (ZMod 2) (Fin 2 → F) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ finrank (ZMod 2) (Fin 2 → F) = Nat.card (Fin 2 → F) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      _ = 2 ^ 4 := by rw [Nat.card_fun, hF, Nat.card_fin]; decide
  have hdU : 4 ≤ finrank (ZMod 2) U := by
    rw [← hdF]
    exact LinearMap.finrank_le_finrank_of_surjective hk
  have hdU' : finrank (ZMod 2) U ≤ 6 := by
    rw [← hdim]
    exact LinearMap.finrank_le_finrank_of_injective hi
  have hdker : finrank (ZMod 2) k.ker ≤ 2 := by
    have he := k.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hk, finrank_top, hdF] at he
    omega
  have hrange : LinearMap.range j ≤ LinearMap.range i :=
    fiveCore_range_le ρ j hj hjact hdim (LinearMap.range i)
      (by rw [LinearMap.finrank_range_of_inj hi]; exact hdU)
      (by rintro a _ ⟨v,rfl⟩; exact ⟨σ a v,hiact a v⟩)
  let ei := LinearEquiv.ofInjective i hi
  let j' := ei.symm.toLinearMap.comp (j.codRestrict (LinearMap.range i) (fun v => hrange ⟨v,rfl⟩))
  have hij (v) : i (j' v) = j v := congrArg Subtype.val (ei.apply_symm_apply _)
  have hj' : Function.Injective j' := by
    intro v w h
    apply hj
    rw [← hij v,← hij w,h]
  have hj'act (a : Five) (v) : j' (coreRepresentation (Fin 5) a.val v) = σ a (j' v) := by
    apply hi
    rw [hij,hiact,hij,hjact]
  have hkinv : ∀ (a : Five) v, v ∈ LinearMap.ker (k.comp j') →
      coreRepresentation (Fin 5) a.val v ∈ LinearMap.ker (k.comp j') := by
    intro a v hv
    change k (j' (coreRepresentation (Fin 5) a.val v)) = 0
    rw [hj'act,hkact,show k (j' v) = 0 from hv,Matrix.mulVec_zero]
  have hki : Function.Injective (k.comp j') := by
    rcases fiveCore_simple (k.comp j').ker hkinv with hz | ht
    · exact LinearMap.ker_eq_bot.mp hz
    · have hh : LinearMap.range j' ≤ k.ker := by
        rintro _ ⟨v,rfl⟩
        have hv : v ∈ (k.comp j').ker := by rw [ht]; trivial
        exact hv
      have hh' := Submodule.finrank_mono hh
      rw [LinearMap.finrank_range_of_inj hj',fiveCore_finrank] at hh'
      omega
  apply AlternatingFiveLinearTwo.no_equivariant_core_injection f hf (k.comp j').toAddMonoidHom hki
  intro a v
  change k (j' (coreRepresentation (Fin 5) a.val v)) = _
  exact (congrArg k (hj'act a v)).trans (hkact a (j' v))
end BinaryPermutation.SevenPointChiefFactor
