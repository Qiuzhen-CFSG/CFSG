module
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Mathlib.RepresentationTheory.Coinvariants
/-!
# Centralizers of eight-dimensional binary PSL₂(8) modules

A fixed-point-free, commutator-generated module of dimension eight is
irreducible: a nontrivial simple submodule has dimension at least six,
whereas its quotient of dimension at most two has trivial perfect-group
action. Full commutator generation kills that quotient. The actual Schur
field has degree dividing both three and eight, hence has order two.
Consequently every commuting linear automorphism is identity.

Source: the linear-centralizer step of Aschbacher--Smith 14.2.18, p.987.
The original extraspecial-core action is the consumer in
`Theory.SpecificGroups.PSL2.EightExtraspecialAction`.
-/
@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups MonoidAlgebra
namespace Representation.SL2
variable {H V : Type*} [Group H] [Finite H] [Group.IsPerfect H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem eight_irreducible_of_fixed_coinvariants
    (e : (H ⧸ pCore 2 H) ≃* SL(2,GaloisField 2 3))
    (ρ : Representation (ZMod 2) H V)
    (hd : Module.finrank (ZMod 2) V = 8)
    (hf : ρ.invariants = ⊥) (hc : Coinvariants.ker ρ = ⊤) : ρ.IsIrreducible := by
  have hnV : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) V)
  obtain ⟨A,hA,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ)).resolve_left top_ne_bot
  let : A.toRepresentation.IsIrreducible := (Subrepresentation.irreducible_iff_isAtom A).mpr hA
  have hnA : ∃ g, A.toRepresentation g ≠ 1 := by
    by_contra! hh
    apply hA.ne_bot
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    apply hf.le
    intro g
    exact congrArg Subtype.val (congrArg (fun f : Module.End (ZMod 2) A.toSubmodule =>
      f ⟨v,hv⟩) (hh g))
  have hlow := core_quotient_irreducible_finrank_bound e A.toRepresentation hnA 3 (by decide)
    (GaloisField.card 2 3 (by decide))
  have hsmall : Module.finrank (ZMod 2) (V ⧸ A.toSubmodule) ≤ 2 := by
    have hsum := Submodule.finrank_quotient_add_finrank A.toSubmodule
    omega
  have htrivial : ∀ g, A.quotientRepresentation g = 1 := by
    by_contra! hn
    have hl := perfect_core_quotient_finrank_bound e A.quotientRepresentation hn
      (by decide : 3 ≠ 0) (GaloisField.card 2 3 (by decide))
    omega
  have hCA : Coinvariants.ker ρ ≤ A.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero A.toSubmodule).mp
    change A.toSubmodule.mkQ (ρ g v - v) = 0
    rw [map_sub, ← Subrepresentation.quotientRepresentation_mk, htrivial]
    simp
  have htop : A = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    exact top_unique (hc ▸ hCA)
  exact isSimpleOrder_iff_isAtom_top.mpr (htop ▸ hA)

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem eight_intertwiner_eq_zero_or_one
    (ρ : Representation (ZMod 2) SL(2,GaloisField 2 3) W) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W = 8)
    (hnt : ∃ g, ρ g ≠ 1) (f : IntertwiningMap ρ ρ) : f = 0 ∨ f = 1 := by
  let E := Module.End (ZMod 2)[SL(2,GaloisField 2 3)] ρ.asModule
  let : Finite ρ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  obtain ⟨hs,n,hn,hsdiv,hper,hdim⟩ := Unsigned.exists_primeField_highestWeight_parameters
    2 ρ hnt 3 (GaloisField.card 2 3 (by decide))
  have hdiv8 : Module.finrank (ZMod 2) E ∣ 8 := by
    have ht := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
    rw [ρ.asModuleEquiv.finrank_eq, hd] at ht
    exact ⟨_,ht.symm⟩
  have hdeg : Module.finrank (ZMod 2) E = 1 := by
    have hh := Nat.dvd_gcd hsdiv hdiv8
    norm_num at hh
    exact hh
  have hcard : Nat.card E = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdeg, pow_one]
  obtain ⟨a,ha,hu⟩ := (Nat.card_eq_two_iff' (0 : E)).mp hcard
  by_cases hz : IntertwiningMap.equivAlgEnd ρ f = 0
  · left
    exact (IntertwiningMap.equivAlgEnd ρ).injective (hz.trans (map_zero _).symm)
  · right
    apply (IntertwiningMap.equivAlgEnd ρ).injective
    rw [map_one]
    exact (hu _ hz).trans (hu 1 one_ne_zero).symm

theorem eight_commuting_equiv_eq_one
    (e : (H ⧸ pCore 2 H) ≃* SL(2,GaloisField 2 3))
    (ρ : Representation (ZMod 2) H V)
    (hd : Module.finrank (ZMod 2) V = 8)
    (hf : ρ.invariants = ⊥) (hc : Coinvariants.ker ρ = ⊤)
    (u : V ≃ₗ[ZMod 2] V) (hu : ∀ h v, u (ρ h v) = ρ h (u v)) : u = 1 := by
  let : ρ.IsIrreducible := eight_irreducible_of_fixed_coinvariants e ρ hd hf hc
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hk := normal_p_subgroup_le_ker ρ (pCore 2 H) pCore_isPGroup
  let τ := quotientOfLEKer ρ (pCore 2 H) hk
  let σ := τ.comp e.symm.toMonoidHom
  let : τ.IsIrreducible := (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr inferInstance
  have hact (g : H) : σ (e (QuotientGroup.mk' (pCore 2 H) g)) = ρ g := by
    simp only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, τ, quotientOfLEKer_apply]
  have honto : Function.Surjective (fun g : H => e (QuotientGroup.mk' (pCore 2 H) g)) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hnt : ∃ g, σ g ≠ 1 := by
    by_contra! hn
    have ht : ρ.invariants = ⊤ := by
      apply top_unique
      intro v _ g
      rw [←hact g, hn]
      rfl
    exact (top_ne_bot (α := Submodule (ZMod 2) V)) (ht.symm.trans hf)
  let f : IntertwiningMap σ σ := {
    toLinearMap := u.toLinearMap
    isIntertwining' g := by
      obtain ⟨h,rfl⟩ := honto g
      ext v
      change u (σ _ v) = σ _ (u v)
      rw [hact]
      exact hu h v }
  rcases eight_intertwiner_eq_zero_or_one σ hd hnt f with hz | ho
  · have he (v : V) : u v = 0 := congrArg (fun k : IntertwiningMap σ σ => k v) hz
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    exact (hv (u.injective ((he v).trans (map_zero u).symm))).elim
  · ext v
    exact congrArg (fun k : IntertwiningMap σ σ => k v) ho
end Representation.SL2
