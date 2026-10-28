module

public import Theory.Representation.Suzuki.SteinbergRegularActors
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Bounds
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.Quotient

/-!
# The original quadratic actor with a J₄ projection kernel

An elementary subgroup of Aut(J₄) has order at most 2¹¹. Thus a quadratic
twisted regular actor whose actual root-projection kernel embeds into Aut(J₄)
has order at most 2¹²: quadraticity bounds its root image by two. A ratio bound
of two permits at most 24 moved dimensions. Every nonidentity Suzuki root
shift moves at least 32 dimensions, and pure multiplicity movement moves at
least 64. Consequently the entire Steinberg isotypic part is fixed.

The actor is retained throughout; no faithful action on a selected constituent
is assumed. This is the J₄ variant of the Suzuki isolation calculation for
Aschbacher–Smith §13.6, printed pp.934–935. It replaces the kernel bound 256
used for M₂₃ and L₃(4) by the proved automorphism two-rank bound eleven.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Module Representation
open Representation.BinaryOffender.NaturalTensor

namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural

/-- An elementary actor embedded in the automorphism group of a simple,
perfect copy of the actual J₄ model has at most 2048 elements. -/
theorem elementary_jankoFour_automorphism_card_le
    {A X : Type*} [Group A] [Group X]
    [IsElementaryAbelian 2 A] [IsSimpleGroup X] [Group.IsPerfect X]
    (e : X ≃* Janko4.Model) (j : A →* MulAut X) (hj : Function.Injective j) :
    Nat.card A ≤ 2048 := by
  let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Janko4.Model :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let f := (MulAut.congr e).toMonoidHom.comp j
  have hf : Function.Injective f := (MulAut.congr e).injective.comp hj
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (MulAut Janko4.Model)).mp
    Janko4.TwoRank.automorphism_twoRank_le_eleven f.range he
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).le.trans hc

/-- The full original quadratic actor has rank at most twelve when its
literal root-projection kernel embeds into Aut(J₄). -/
theorem quadratic_actor_rank_le_twelve_of_jankoFour_kernel
    {K A P M X : Type*} [Field K] [Group A] [Group P] [Group X]
    [IsElementaryAbelian 2 A] [IsSimpleGroup X] [Group.IsPerfect X]
    [AddCommGroup M] [Module K M] [Nontrivial M]
    (e : X ≃* Janko4.Model)
    (φ : A →* P) (τ : Representation K A M)
    (σ : Representation K A (P → M))
    (hσ : ∀ a f x, σ a f x = τ a (f ((φ a)⁻¹ * x)))
    (hquad : ∀ a b v, σ a (σ b v - v) = σ b v - v)
    (j : φ.ker →* MulAut X) (hj : Function.Injective j) :
    Nat.log 2 (Nat.card A) ≤ 12 := by
  let : IsElementaryAbelian 2 φ.ker :=
    IsElementaryAbelian.of_injective φ.ker.subtype φ.ker.subtype_injective
  have hk := elementary_jankoFour_automorphism_card_le e j hj
  have hr := TwistedRegular.quadratic_projection_card_le_two φ τ σ hσ hquad
  have hc : Nat.card A ≤ 4096 := by
    rw [← φ.ker.card_mul_index, Subgroup.index_ker]
    nlinarith
  exact (Nat.log_mono_right (b := 2) hc).trans (by decide)

/-- The literal twisted-root action on a Suzuki Steinberg isotypic part is
trivial under the source ratio bound when its full projection kernel embeds
into the automorphism group of the normal J₄ component quotient. -/
theorem twisted_root_action_trivial_of_jankoFour_kernel
    (m : ℕ) (hm : 1 ≤ m) {K A M X : Type*} [Field K] [Group A] [Group X]
    [IsElementaryAbelian 2 A] [IsSimpleGroup X] [Group.IsPerfect X]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] [Nontrivial M]
    (e : X ≃* Janko4.Model)
    (φ : A →* SuzukiRootSubgroup m) (τ : Representation K A M)
    (σ : Representation K A (SuzukiRootSubgroup m → M))
    (hσ : ∀ a f x, σ a f x = τ a (f ((φ a)⁻¹ * x)))
    (hquad : ∀ a b v, σ a (σ b v - v) = σ b v - v)
    (j : φ.ker →* MulAut X) (hj : Function.Injective j)
    (hsmall : ∀ a, operatorFixedCodim (σ a) ≤ 2 * Nat.log 2 (Nat.card A)) :
    ∀ a, σ a = 1 := by
  classical
  let : Fintype (SuzukiRootSubgroup m) := Fintype.ofFinite _
  have hr := quadratic_actor_rank_le_twelve_of_jankoFour_kernel e φ τ σ hσ hquad j hj
  have hsize : 64 ≤ Fintype.card (SuzukiRootSubgroup m) := by
    rw [Fintype.card_eq_nat_card, suzukiRootSubgroup_card m (by omega)]
    rw [← pow_mul]
    change 2 ^ 6 ≤ 2 ^ ((2 * m + 1) * 2)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hdim : 1 ≤ finrank K M := Module.finrank_pos
  intro a
  have ha2 : a * a = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
  have hd : operatorFixedCodim (σ a) ≤ 24 := by
    have hs := hsmall a
    omega
  have hphi : φ a = 1 := by
    by_contra hne
    have hs := TwistedRegular.shift_dimension_le_twice_displacement φ τ σ hσ a hne
      (by rw [← map_mul, ha2, map_one])
    nlinarith
  have hmult (v : M) : τ a v = v := by
    by_contra hne
    have hs := TwistedRegular.card_le_displacement_of_pure_multiplicity
      φ τ σ hσ a hphi ⟨v, hne⟩
    omega
  apply LinearMap.ext
  intro f
  funext x
  rw [hσ, hphi, inv_one, one_mul, hmult]
  rfl

end Representation.SuzukiSmallDegree
