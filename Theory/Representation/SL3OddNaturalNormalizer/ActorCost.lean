module
public import Theory.Representation.SL3OddNaturalNormalizer.Index
public import Theory.Representation.ScalarCoinvariants
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank.Intrinsic
public import Theory.Representation.BinaryOffender.CubicConjugateBound

/-!
# Actor cost on an odd-degree natural SL₃ constituent

An elementary two-subgroup of the binary natural normalizer lies in SL₃
when the field degree is odd. Its rank is at most twice that degree, while
its positive fixed codimension is a multiple of the degree. Thus rank is
at most twice fixed codimension. The invariant-subspace version retains the
literal action image, allowing a pointwise kernel in the original actor.

Source: Aschbacher--Smith B.5.9--10 and D.3.9, printed pp.107--109,200--201.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Representation.SL3OddNaturalNormalizer
variable {F G V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A faithful natural normalizer action costs at least half the actor rank. -/
theorem natural_actor_rank_le_twice_fixedCodim
    {n : ℕ} (hn : 0 < n) (ho : Odd n) (hF : Nat.card F = 2^n)
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (J : Subgroup G) [J.Normal] (j : J ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (b : V ≃ₗ[ZMod 2] (Fin 3 → F))
    (hb : ∀ (g : J) v, b (ρ g v) = specialLinearNatural 3 (j g) (b v))
    (A : Subgroup G) (hA : IsElementaryTwo A) : rank A ≤ 2*fixedCodim ρ A := by
  let τ : Representation (ZMod 2) G (Fin 3 → F) := b.conjRingEquiv.toMonoidHom.comp ρ
  have hτ : Function.Injective τ := b.conjRingEquiv.injective.comp hf
  have hnat (g : J) (v : Fin 3 → F) : τ g v = Matrix.mulVec (j g).val v := by
    change b (ρ g (b.symm v)) = _
    exact (hb g (b.symm v)).trans (by rw [b.apply_symm_apply]; rfl)
  let : IsElementaryAbelian 2 A := hA.2
  have hAJ := two_subgroup_le_of_natural hn ho hF J j τ hτ hnat A
    (IsElementaryAbelian.isPGroup 2 A)
  let A' := (A.subgroupOf J).map j.toMonoidHom
  let : IsElementaryAbelian 2 (A.subgroupOf J) := IsElementaryAbelian.subgroupOf hAJ
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
  have hr : rank A' = rank A := by
    rw [rank_map_injective _ j.injective]
    exact congrArg (Nat.log 2) (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv)
  have hAn : A' ≠ ⊥ := by
    intro hz
    have hp := hA.rank_pos
    rw [←hr,hz,BinaryOffender.rank_bot] at hp
    omega
  have hrank := rank_le_of_primeRank_le (show IsElementaryTwo A' from ⟨hAn,inferInstance⟩)
    (HermitianTensorThree.ImageOuter.OuterRank.specialLinearThree_twoRank F hn hF).le
  rw [hr] at hrank
  let σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F) (Fin 3 → F) :=
    restrictScalars (k := ZMod 2) (specialLinearNatural 3)
  have hc : fixedCodim ρ A = fixedCodim σ A' := by
    have he := fixedCodim_map_equivariant (ρ.comp J.subtype) σ j.toMonoidHom b hb
      (A.subgroupOf J)
    have hh : fixedCodim (ρ.comp J.subtype) (A.subgroupOf J) = fixedCodim ρ A := by
      unfold fixedCodim
      rw [fixedSpace_comp_map,Subgroup.map_subgroupOf_eq_of_le hAJ]
    exact hh.symm.trans he
  have hd : Module.finrank (ZMod 2) F = n := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2 ^ Module.finrank (ZMod 2) F = 2^n
    rw [←hF,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hdiv : n ∣ fixedCodim ρ A := by
    rw [hc,fixedCodim_restrictScalars,hd]
    exact dvd_mul_right _ _
  have hpos := fixedCodim_pos_of_faithful ρ hf hA.1
  have hle := Nat.le_of_dvd hpos hdiv
  omega

/-- The same cost on the actual invariant-subspace image, retaining its kernel. -/
theorem natural_invariant_actor_rank_cost
    {n : ℕ} (hn : 0 < n) (ho : Odd n) (hF : Nat.card F = 2^n)
    (ρ : Representation (ZMod 2) G V) (J : Subgroup G) [J.Normal]
    (R : Submodule (ZMod 2) V) (hJR : J ≤ subspaceStabilizer ρ R)
    (j : J ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (b : R ≃ₗ[ZMod 2] (Fin 3 → F))
    (hb : ∀ (g : J) v, b ((invariantSubspace ρ J R hJR).toRepresentation g v) =
      specialLinearNatural 3 (j g) (b v))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hAR : A ≤ subspaceStabilizer ρ R)
    (hmove : ¬ R ≤ fixedSpace ρ A) :
    rank (restrictedSubgroup ρ R A) ≤
      2 * fixedCodim (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R A) := by
  let f := subgroupActionHom ρ R J hJR
  have hf : Function.Injective f := by
    intro x y hxy
    apply j.injective
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := b.surjective v
    rw [←hb x w,←hb y w]
    apply congrArg b
    exact congrArg (fun g => subspaceImageRepresentation ρ R g w) hxy
  let er : J ≃* restrictedSubgroup ρ R J := (MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (subgroupActionHom_range ρ R J hJR))
  let jr := er.symm.trans j
  let : (restrictedSubgroup ρ R J).Normal :=
    Subgroup.Normal.map inferInstance (subspaceActionHom ρ R)
      (stabilizerRepresentation ρ R).asGroupHom.rangeRestrict_surjective
  have hnat (g : restrictedSubgroup ρ R J) (v : R) :
      b (subspaceImageRepresentation ρ R g v) = specialLinearNatural 3 (jr g) (b v) := by
    obtain ⟨x,rfl⟩ := er.surjective g
    change b ((invariantSubspace ρ J R hJR).toRepresentation x v) = _
    simpa only [jr,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hb x v
  exact natural_actor_rank_le_twice_fixedCodim hn ho hF
    (subspaceImageRepresentation ρ R) (subspaceImageRepresentation_injective ρ R)
    (restrictedSubgroup ρ R J) jr b hnat (restrictedSubgroup ρ R A)
    (hA.restrictedSubgroup ρ R hAR hmove)
end Representation.SL3OddNaturalNormalizer
