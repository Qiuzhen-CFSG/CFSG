module

public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer
public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.GroupTheory.PPrimeCorePGroupQuotient
/-!
# Minimal faithful binary degree for the extraspecial group of order 27

Maschke's theorem provides a simple constituent on which the center acts
nontrivially. It is faithful and has degree six, so in ambient dimension six
it is the whole module. In particular a nonidentity central element fixes
only zero, without an irreducibility hypothesis on the ambient overgroup.

The normal extraspecial subgroup with two-group quotient is the genuine odd
core (`pPrimeCore 2`). Its marked Heisenberg central generator therefore
supplies all the cubic witnesses used in Aschbacher–Smith, G.11.2(3),
printed p.364, and 6.2.19, printed p.691. This conditional structural result
still requires construction and identification of the concrete extension.
-/

@[expose] public section

open scoped MonoidAlgebra
open Representation Subgroup
namespace Representation.RankTwo.ExtraspecialModel
variable {P V : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem irreducible_of_faithful_six
    (ρ : Representation (ZMod 2) P V) (hρ : Function.Injective ρ)
    (hcard : Nat.card P = 27) (hdim : Module.finrank (ZMod 2) V = 6) :
    IsIrreducible ρ := by
  let : IsSemisimpleModule (ZMod 2)[P] ρ.asModule := by
    apply isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
    right
    rw [ZMod.ringChar_zmod_n, hcard]
    exact ⟨Nat.prime_two, by decide⟩
  have hcenter : ¬ center P ≤ ρ.ker := by
    intro h
    have he : center P = ⊥ := by
      apply bot_unique
      simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hρ] using h
    have hc := IsExtraspecial.center_order_p 3 P
    rw [he, Subgroup.card_bot] at hc
    omega
  obtain ⟨m, hm, hmk⟩ := exists_simple_submodule_nontrivial_of_not_le_ker ρ
    (center P) hcenter
  let W := Subrepresentation.ofSubmodule' m
  let τ := W.toRepresentation
  let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple ρ hm
  have hτ : Function.Injective τ := (MonoidHom.ker_eq_bot_iff _).mp
    (ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := 3) τ hmk)
  have hd := BinaryCoprimeDegree.extraspecial_irreducible_finrank (p := 3)
    (by decide) τ hτ hcard
  have hW : W = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    simpa only [hdim, BinaryPrimeDegree.orderOf_two_mod_three, Nat.reduceMul] using hd
  have ha : IsAtom W := (Subrepresentation.irreducible_iff_isAtom W).mp inferInstance
  rw [hW] at ha
  exact isSimpleOrder_iff_isAtom_top.mpr ha

/-- A nonidentity element of the cubic center generates that center. -/
theorem zpowers_eq_center (c : P) (hc : orderOf c = 3)
    (hz : c ∈ center P) : zpowers c = center P := by
  apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz)
  rw [Nat.card_zpowers, hc, IsExtraspecial.center_order_p 3 P]

/-- Faithfulness in degree six forces every nonidentity central cube root to
act without nonzero fixed vectors. -/
theorem fixed_free_of_faithful_six
    (ρ : Representation (ZMod 2) P V) (hρ : Function.Injective ρ)
    (hcard : Nat.card P = 27) (hdim : Module.finrank (ZMod 2) V = 6)
    (c : P) (hc : orderOf c = 3) (hz : c ∈ center P) :
    ∀ x, ρ c x = x → x = 0 := by
  let : IsIrreducible ρ := irreducible_of_faithful_six ρ hρ hcard hdim
  have hn : (zpowers c).Normal := by
    rw [zpowers_eq_center c hc hz]
    infer_instance
  exact fixed_free_of_faithful_irreducible_normal_three ρ hρ c hc hn

end Representation.RankTwo.ExtraspecialModel
