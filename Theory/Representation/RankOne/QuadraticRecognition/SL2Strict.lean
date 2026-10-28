module
public import Theory.Representation.RankOne.QuadraticRecognition.SL2Actors
public import Theory.Representation.RankOne.QuadraticRecognition.Generation
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Irreducibility in the strict binary SL₂ branch

The corrected Sylow fixed-space generation condition and zero global fixed
space imply V=[V,G]. Choose a simple submodule I. It is noncentral because
C_V(G)=0; if I were proper, V/I would also be noncentral because V=[V,G].
Every noncentral binary SL₂(2ⁿ) module has fixed codimension at least n for a
nontrivial two-subgroup. The section inequality would give codimension at
least 2n, contradicting |V/C_V(A)|<|A|²≤2^(2n).

This supplies the irreducibility reduction in the corrected DGS85 (5.12),
printed pp.113–114, for n>1 and proper as well as full Sylow actors. It does
not identify the remaining irreducible module or assume quadraticity.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance finiteStrictActorQuotient (C : Submodule (ZMod 2) V) : Finite (V ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

/-- The corrected generation premise excludes extensions with trivial quotients. -/
theorem sl2_strict_actor_irreducible
    (ρ : Representation (ZMod 2) SL(2,F) V) (hf : Function.Injective ρ)
    (S : Sylow 2 SL(2,F)) (A : Subgroup SL(2,F)) (hAS : A ≤ S)
    (hgen : GeneratedByFixedSpace ρ S) (hfix : fixedSpace ρ ⊤ = ⊥)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hstrict : Nat.card (V ⧸ fixedSpace ρ A) < Nat.card A ^ 2) :
    ρ.IsIrreducible := by
  have hA : A ≠ ⊥ := by
    intro h
    rw [h,card_bot,one_pow] at hstrict
    have hp : 0 < Nat.card (V ⧸ fixedSpace ρ ⊥) := Nat.card_pos
    omega
  have hSc : Nat.card S = 2^n := (Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).symm.toEquiv).trans hF
  have hAc : Nat.card A ≤ 2^n := by
    rw [←hSc]
    exact Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hAS)
  have hsmall : fixedCodim ρ A < 2*n := by
    have hh := hstrict.trans_le (Nat.pow_le_pow_left hAc 2)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,←pow_mul] at hh
    have he := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hh
    change fixedCodim ρ A < _ at he
    omega
  have hpos := fixedCodim_pos_of_faithful ρ hf hA
  have hdim := fixedCodim_add_finrank ρ A
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨I,hI,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ)).resolve_left top_ne_bot
  have hntI : ∃ g, I.toRepresentation g ≠ 1 := by
    by_contra! hh
    apply hI.ne_bot
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have hhf : v ∈ fixedSpace ρ ⊤ := fun g =>
      congrArg Subtype.val (LinearMap.congr_fun (hh g) (⟨v,hv⟩ : I))
    exact hfix ▸ hhf
  have hfull := moved_eq_top_of_sylow_generation ρ S hgen hfix
  have htop : I = ⊤ := by
    by_contra hne
    have hntQ : ∃ g, I.quotientRepresentation g ≠ 1 := by
      by_contra! hh
      have hle : Coinvariants.ker ρ ≤ I.toSubmodule := by
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨g,v⟩,rfl⟩
        exact (Submodule.Quotient.eq I.toSubmodule).mp
          (LinearMap.congr_fun (hh g) (I.toSubmodule.mkQ v))
      exact hne (Subrepresentation.toSubmodule_injective (top_unique (hfull ▸ hle)))
    have hp := S.isPGroup'.of_injective (Subgroup.inclusion hAS) (Subgroup.inclusion_injective hAS)
    have hi := SL2.two_subgroup_fixedCodim_lower I.toRepresentation hntI hn hF A hp hA
    have hq := SL2.two_subgroup_fixedCodim_lower I.quotientRepresentation hntQ hn hF A hp hA
    have hs := fixedCodim_quotient_add_subrepresentation_le ρ I A
    omega
  exact isSimpleOrder_iff_isAtom_top.mpr (htop ▸ hI)
end Representation.RankOne.QuadraticRecognition
