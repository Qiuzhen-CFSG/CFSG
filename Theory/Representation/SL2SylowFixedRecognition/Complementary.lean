module
public import Theory.Representation.SL2SylowFixedRecognition.Complementary.Roots
public import Theory.SpecificGroups.SL2.SylowBorelSeparation

/-!
# Natural coordinates from complementary Sylow fixed spaces

A nonidentity element of one Sylow and a distinct Sylow generate SL₂.
Complementarity therefore implies uniformity of the Sylow fixed spaces,
as well as fixed-space generation and the absence of global fixed vectors.
G.1.6 then gives a bijective coordinate map on the original module. This
includes multiplicity zero and makes no semisimplicity assumption.

Source: Aschbacher--Smith, G.1.7, printed pp.329--330.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2SylowFixedRecognition
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- A Sylow and a nonidentity element of a distinct Sylow generate binary SL₂. -/
theorem sylow_sup_zpowers_eq_top (R S : Sylow 2 SL(2,F)) (hRS : R ≠ S)
    {r : SL(2,F)} (hr : r ∈ R) (hr1 : r ≠ 1) :
    (S : Subgroup SL(2,F)) ⊔ zpowers r = ⊤ := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) S R
  by_contra hn
  have hN := Matrix.SpecialLinearGroup.overgroup_le_sylowNormalizer S le_sup_left hn
  have hrN := hN (mem_sup_right (mem_zpowers r))
  obtain ⟨x,hx,he⟩ := hr
  change g*x*g⁻¹ = r at he
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hr1
    rw [← he,hx1,mul_one,mul_inv_cancel]
  have hg := Matrix.SpecialLinearGroup.mem_sylow_normalizer_of_conjugate_mem
    S x g hx hx1 (he.symm ▸ hrN)
  exact hRS (Sylow.smul_eq_iff_mem_normalizer.mpr hg)

omit [CharP F 2] [Finite F] in
/-- Complementary fixed spaces force the global fixed space to vanish. -/
theorem fixed_eq_bot_of_isCompl (ρ : Representation (ZMod 2) SL(2,F) V)
    (R S : Sylow 2 SL(2,F)) (h : IsCompl (fixedSpace ρ R) (fixedSpace ρ S)) :
    fixedSpace ρ ⊤ = ⊥ := by
  apply bot_unique
  intro v hv
  exact h.disjoint.le_bot ⟨ρ.invariants_comp_subtype_antitone le_top hv,ρ.invariants_comp_subtype_antitone le_top hv⟩

/-- The hypotheses of G.1.7 imply the generation and uniformity in G.1.6.
No irreducibility or faithfulness of the representation is needed. -/
theorem fixedSpaceHypotheses_of_isCompl (ρ : Representation (ZMod 2) SL(2,F) V)
    (R S : Sylow 2 SL(2,F)) (h : IsCompl (fixedSpace ρ R) (fixedSpace ρ S)) :
    FixedSpaceHypotheses ρ R := by
  have hz := fixed_eq_bot_of_isCompl ρ R S h
  refine ⟨?_,?_⟩
  · apply top_unique
    rw [← h.sup_eq_top]
    apply sup_le
    · exact le_iSup_maps ρ _
    · obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) R S
      change fixedSpace ρ ((R : Subgroup SL(2,F)).map (MulAut.conj g).toMonoidHom) ≤ _
      rw [fixedSpace_conjugate]
      exact le_iSup (fun g => (fixedSpace ρ R).map (ρ g)) g
  · intro r hr hr1
    apply le_antisymm ?_ (ρ.invariants_comp_subtype_antitone (zpowers_le.mpr hr))
    intro v hv
    have hvtop : v ∈ fixedSpace ρ R ⊔ fixedSpace ρ S := by rw [h.sup_eq_top]; trivial
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hvtop
    by_cases hRS : R = S
    · subst S
      exact (fixedSpace ρ R).add_mem ha hb
    have hbr : b ∈ fixedSpace ρ (zpowers r) := by
      simpa only [add_sub_cancel_left] using
        (fixedSpace ρ (zpowers r)).sub_mem hv (ρ.invariants_comp_subtype_antitone (zpowers_le.mpr hr) ha)
    have hbtop : b ∈ fixedSpace ρ ⊤ := by
      have he : fixedSpace ρ ((S : Subgroup SL(2,F)) ⊔ zpowers r) =
          fixedSpace ρ S ⊓ fixedSpace ρ (zpowers r) := ρ.invariants_comp_sup _ _
      rw [← sylow_sup_zpowers_eq_top R S hRS hr hr1,he]
      exact ⟨hb,hbr⟩
    have hb0 : b = 0 := by simpa only [hz,Submodule.mem_bot] using hbtop
    change a + b ∈ fixedSpace ρ R
    rw [hb0,add_zero]
    exact ha

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- G.1.7, including multiplicity zero and the original matrix actors. -/
theorem natural_of_complementary_sylow_fixed [Finite V]
    (ρ : Representation (ZMod 2) SL(2,F) V) (R S : Sylow 2 SL(2,F))
    (h : IsCompl (fixedSpace ρ R) (fixedSpace ρ S))
    (d : ℕ) (hd : 2 ≤ d) (hF : Nat.card F = 2^d) : NaturalCoordinates ρ := by
  obtain ⟨c⟩ := quotientCoordinates_of_fixedSpaceHypotheses ρ R
    (fixedSpaceHypotheses_of_isCompl ρ R S h) d hd hF
  have hi : Function.Injective c.coordinates := by
    apply LinearMap.ker_eq_bot.mp
    rw [c.kernel,fixed_eq_bot_of_isCompl ρ R S h]
  exact ⟨c.multiplicity,LinearEquiv.ofBijective c.coordinates ⟨hi,c.surjective⟩,
    c.intertwines⟩

/-- Applying G.1.7 to the actual central quotient retains the exact original
quotient map, global-fixed kernel, and action in the output. -/
theorem quotientCoordinates_of_complementary_sylow_fixed [Finite V]
    (ρ : Representation (ZMod 2) SL(2,F) V) (R S : Sylow 2 SL(2,F))
    (h : IsCompl (fixedSpace (centralQuotient ρ) R) (fixedSpace (centralQuotient ρ) S))
    (d : ℕ) (hd : 2 ≤ d) (hF : Nat.card F = 2^d) : Nonempty (QuotientCoordinates ρ) := by
  let : Finite (V ⧸ fixedSpace ρ ⊤) :=
    Finite.of_surjective _ (fixedSpace ρ ⊤).mkQ_surjective
  exact quotientCoordinates_of_natural ρ
    (natural_of_complementary_sylow_fixed (centralQuotient ρ) R S h d hd hF)

end Representation.SL2SylowFixedRecognition
