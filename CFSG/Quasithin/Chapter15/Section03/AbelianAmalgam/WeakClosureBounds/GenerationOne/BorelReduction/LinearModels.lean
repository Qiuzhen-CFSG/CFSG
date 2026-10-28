module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.SourceCases.Models

/-!
# Linear models after the field restriction

The characteristic-two SL₂ projection is injective. At odd exponent f,
the scalar kernel of SL₃(2^f) → PSL₃(2^f) has order gcd(3, 2^f − 1) = 1.
The resulting actual isomorphisms carry the named matrix Borels to each other.
These comparisons refine models in H/J; they do not collapse the separate
central kernel of H/O₂(H) → H/J or classify arbitrary central covers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.2,
printed pp.215–216, and 15.3.65, printed p.1152.
-/

@[expose] public section
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups
noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
variable {F : Type*} [Field F] [Finite F]

/-- Odd f makes gcd(3, 2^f − 1) equal to one, killing the ordinary scalar kernel. -/
theorem psl3Projection_injective_of_odd {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : Odd f) : Function.Injective (projection F) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply Subgroup.eq_bot_of_card_eq
  rw [card_projectionKernel, hF]
  apply Nat.Coprime.gcd_eq_one
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
  intro hd
  have hm := Nat.mod_eq_zero_of_dvd hd
  have hmod : 2 ^ f % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hf
    rw [pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  omega

/-- The ordinary central projection is an isomorphism at odd field exponent. -/
def sl3ProjectiveEquiv {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : Odd f) :
    SL(3,F) ≃* PSL(3,F) :=
  MulEquiv.ofBijective (projection F)
    ⟨psl3Projection_injective_of_odd hF hf, projection_surjective F⟩

/-- The inverse projection identifies the projective flag Borel with the actual SL₃ Borel. -/
theorem sl3ProjectiveEquiv_borel {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : Odd f) :
    (borel F).map (sl3ProjectiveEquiv hF hf).symm.toMonoidHom = borelSL F := by
  change ((borelSL F).map (sl3ProjectiveEquiv hF hf).toMonoidHom).map _ = _
  exact (Subgroup.map_symm_eq_iff_map_eq (borelSL F) (e := sl3ProjectiveEquiv hF hf)).mpr rfl

variable {G : Type*} [Group G]

/-- A source PSL₃/Borel pair becomes an SL₃/Borel pair after proving oddness. -/
theorem SourceCases.ModelBorelPair.sl3 {H M K : Subgroup G} {f : ℕ}
    (h : SourceCases.ModelBorelPair H M K (borel F))
    (hF : Nat.card F = 2 ^ f) (hf : Odd f) :
    SourceCases.ModelBorelPair H M K (borelSL F) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.trans (sl3ProjectiveEquiv hF hf).symm, ?_⟩
  change (SourceCases.componentOverlap H M K).map
    ((sl3ProjectiveEquiv hF hf).symm.toMonoidHom.comp e.toMonoidHom) = _
  rw [← Subgroup.map_map, he]
  exact sl3ProjectiveEquiv_borel hF hf

omit [Finite F] in
section
variable [CharP F 2]

/-- The ordinary degree-two central projection is an isomorphism in characteristic two. -/
def sl2ProjectiveEquiv : BenderSuzuki.Converse.SL2 F ≃* BenderSuzuki.Converse.PSL2 F :=
  MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩

/-- The characteristic-two projection identifies the two concrete rank-one Borels. -/
theorem sl2ProjectiveEquiv_borel :
    (BenderSuzuki.Converse.PBorel F).map sl2ProjectiveEquiv.symm.toMonoidHom =
      BenderSuzuki.Converse.Borel F := by
  rw [BenderSuzuki.Converse.PBorel_eq_map]
  change ((BenderSuzuki.Converse.Borel F).map sl2ProjectiveEquiv.toMonoidHom).map _ = _
  exact (Subgroup.map_symm_eq_iff_map_eq (BenderSuzuki.Converse.Borel F)
    (e := sl2ProjectiveEquiv)).mpr rfl

/-- A source PSL₂/Borel pair gives an actual SL₂/Borel pair in characteristic two. -/
theorem SourceCases.ModelBorelPair.sl2 {H M K : Subgroup G}
    (h : SourceCases.ModelBorelPair H M K (BenderSuzuki.Converse.PBorel F)) :
    SourceCases.ModelBorelPair H M K (BenderSuzuki.Converse.Borel F) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.trans sl2ProjectiveEquiv.symm, ?_⟩
  change (SourceCases.componentOverlap H M K).map
    (sl2ProjectiveEquiv.symm.toMonoidHom.comp e.toMonoidHom) = _
  rw [← Subgroup.map_map, he]
  exact sl2ProjectiveEquiv_borel
end
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
