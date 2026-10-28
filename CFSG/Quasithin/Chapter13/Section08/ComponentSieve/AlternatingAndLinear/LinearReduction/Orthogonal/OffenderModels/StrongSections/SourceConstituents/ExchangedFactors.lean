module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Constituents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.IndexTwo

/-!
# Excluding exchanged factors in the strong-quotient branch

Every element outside an index-two component exchanges the two Clifford
summands. If a quadratic abelian actor contains such an element, its intersection
with the component fixes both summands, and is trivial in a faithful action.
The disjoint-transposition group has both an odd element and a nonidentity even
element, so this excludes the split restriction for the actor marked by B.3.2.

This argument does not exclude actors contained in the component. That case is
needed separately for the strong-submodule branch of Aschbacher–Smith 13.8.25,
printed p.960 (1 March 2004 manuscript).
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.SourceConstituents
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

private theorem map_of_mem (K : Subgroup H) (I : Subrepresentation (ρ.comp K.subtype))
    {k : H} (hk : k ∈ K) : I.toSubmodule.map (ρ k) = I.toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact I.apply_mem_toSubmodule ⟨k, hk⟩ hv
  · intro v hv
    refine ⟨ρ k⁻¹ v, I.apply_mem_toSubmodule ⟨k⁻¹, K.inv_mem hk⟩ hv, ?_⟩
    simp [← Module.End.mul_apply, ← map_mul]

private theorem map_left_of_outside (K : Subgroup H) [K.Normal]
    (hindex : K.index = 2) (d : RestrictionSplit ρ K) {a : H} (ha : a ∉ K) :
    d.left.toSubmodule.map (ρ a) = d.right.toSubmodule := by
  have hk : d.swapper⁻¹ * a ∈ K :=
    (K.mul_mem_iff_of_index_two hindex).mpr
      (iff_of_false (by simpa using d.outside) ha)
  have he : ρ a = (ρ d.swapper).comp (ρ (d.swapper⁻¹ * a)) := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel_left]
  rw [he, Submodule.map_comp, map_of_mem ρ K d.left hk]
  exact d.map_left

/-- A faithful quadratic actor meeting both component cosets nontrivially
cannot act on two exchanged complementary constituents. -/
theorem not_restrictionSplit_of_mixed_actor (K A : Subgroup H) [K.Normal] [IsMulCommutative A]
    (hindex : K.index = 2) (hf : Function.Injective ρ) (hq : IsQuadratic ρ A)
    (ho : ¬ A ≤ K) (he : A ⊓ K ≠ ⊥) : ¬ Nonempty (RestrictionSplit ρ K) := by
  rintro ⟨d⟩
  obtain ⟨a, ha, hak⟩ : ∃ a ∈ A, a ∉ K := by simpa only [SetLike.le_def, not_forall, exists_prop] using ho
  have hmap := map_left_of_outside ρ K hindex d hak
  have hd : Disjoint d.left.toSubmodule (d.left.toSubmodule.map (ρ a)) := by
    rw [hmap, disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule d.complementary.disjoint.eq_bot
  have hs : d.left.toSubmodule ⊔ d.left.toSubmodule.map (ρ a) = ⊤ := by
    rw [hmap]
    exact congrArg Subrepresentation.toSubmodule d.complementary.codisjoint.eq_top
  apply he
  apply quadratic_pair_component_inf_eq_bot ρ hf d.left.toSubmodule K A hq ha hd hs
  exact le_subspaceStabilizer ρ _ (fun k hk v hv => d.left.apply_mem_toSubmodule ⟨k, hk⟩ hv)

/-- The marked whole actor supplies both cosets and a nontrivial intersection. -/
theorem marked_D_mixed_actor (eH : H ≃* Equiv.Perm (Fin 8)) (K A : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hA : A.map eH.toMonoidHom = D 8) : ¬ A ≤ K ∧ A ⊓ K ≠ ⊥ := by
  have h0 : pairSwap 8 0 ∈ D 8 := pairSwap_mem 0 (by decide)
  have h1 : pairSwap 8 1 ∈ D 8 := pairSwap_mem 1 (by decide)
  have hodd : pairSwap 8 0 ∉ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have heven : pairSwap 8 0 * pairSwap 8 1 ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hne : pairSwap 8 0 * pairSwap 8 1 ≠ 1 := by decide
  constructor
  · intro h
    exact hodd (hK ▸ Subgroup.map_mono h (hA.symm ▸ h0))
  · intro h
    obtain ⟨a, ha, hea⟩ := hA.symm ▸ (D 8).mul_mem h0 h1
    change eH a = pairSwap 8 0 * pairSwap 8 1 at hea
    have hk : a ∈ K := by
      have hmem : eH a ∈ K.map eH.toMonoidHom := by rw [hK, hea]; exact heven
      obtain ⟨k, hk, he⟩ := hmem
      exact eH.injective he ▸ hk
    have ha1 : a = 1 := Subgroup.mem_bot.mp (h ▸ (show a ∈ A ⊓ K from ⟨ha, hk⟩))
    apply hne
    simpa [ha1] using hea.symm
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.SourceConstituents
