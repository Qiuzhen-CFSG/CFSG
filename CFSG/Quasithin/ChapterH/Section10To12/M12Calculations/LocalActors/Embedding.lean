module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.AmbientInput
public import Theory.Mathieu.M12.A5Fixer.Automorphisms.OuterIndex
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Representation.BinaryOffender.FixedSpaceSpan

/-!
# Ambient identification and elementary rank in H.11

The ambient embedding identifies the solvable residual with the actual inner
automorphisms. The proved outer-index bound then makes any proper enlargement
of the residual the full automorphism group. In particular an elementary group
of order sixteen, excluded from the residual by its two-rank bound, constructs
an actual ambient isomorphism with Aut(M₁₂).

The two numerical model rank bounds are explicit group-table premises. Fixed
spaces and their spans are transported by the given equivariant equivalence;
no module-dimension bounds for elementary actors are assumed here.
Source: Aschbacher–Smith H.11.1(1),(4), printed pp.392–393, combined manuscript
of 1 March 2004.
-/

public section
open Subgroup Representation.BinaryOffender Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
namespace AmbientExtension

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {h : M12ModuleInput ρ} (d : AmbientExtension ρ h)

omit [Finite G] in
theorem map_residual :
    (solvableResidual G).map d.embedding = MulAut.innerSubgroup M12 := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨h.residualEquiv ⟨g, hg⟩, (d.embedding_residual ⟨g, hg⟩).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨h.residualEquiv.symm x, (h.residualEquiv.symm x).property, ?_⟩
    rw [d.embedding_residual, h.residualEquiv.apply_symm_apply]

omit [Finite G] in
theorem embedding_mem_inner_iff (g : G) :
    d.embedding g ∈ MulAut.innerSubgroup M12 ↔ g ∈ solvableResidual G := by
  constructor
  · rintro ⟨x, hx⟩
    have he : d.embedding (h.residualEquiv.symm x : G) = d.embedding g := by
      rw [d.embedding_residual, h.residualEquiv.apply_symm_apply]
      exact hx
    exact d.embedding_injective he ▸ (h.residualEquiv.symm x).property
  · intro hg
    exact ⟨h.residualEquiv ⟨g, hg⟩, (d.embedding_residual ⟨g, hg⟩).symm⟩

omit [Finite G] in
theorem inner_le_range : MulAut.innerSubgroup M12 ≤ d.embedding.range := by
  rw [← d.map_residual]
  exact map_le_range _ _

omit [Finite G] in
/-- Any ambient outer element forces coverage of the full automorphism group. -/
theorem embedding_surjective_of_outer {g : G} (hg : g ∉ solvableResidual G) :
    Function.Surjective d.embedding := by
  apply MonoidHom.range_eq_top.mp
  apply index_eq_one.mp
  have hne : d.embedding.range ≠ MulAut.innerSubgroup M12 := by
    intro he
    apply hg
    apply (d.embedding_mem_inner_iff g).mp
    rw [← he]
    exact ⟨g, rfl⟩
  have hlt := index_strictAnti (lt_of_le_of_ne d.inner_le_range (Ne.symm hne))
  have hb : (MulAut.innerSubgroup M12).index ≤ 2 :=
    M12A5Fixer.Automorphisms.outerIndexBound
  have hpos := Nat.pos_of_ne_zero d.embedding.range.index_ne_zero_of_finite
  omega

/-- The isomorphism uses the original embedding, including its residual marking. -/
@[expose] noncomputable def automorphismEquivOfOuter {g : G} (hg : g ∉ solvableResidual G) :
    G ≃* MulAut M12 :=
  MulEquiv.ofBijective d.embedding ⟨d.embedding_injective, d.embedding_surjective_of_outer hg⟩

omit [Finite G] in
@[simp] theorem automorphismEquivOfOuter_apply {g : G} (hg : g ∉ solvableResidual G)
    (x : G) : d.automorphismEquivOfOuter hg x = d.embedding x := rfl

include d in
/-- The model two-rank bound transfers along the actual ambient embedding. -/
theorem primeRank_le_four (haut : primeRank 2 (MulAut M12) ≤ 4) : primeRank 2 G ≤ 4 :=
  (Theory.GroupTheory.primeRank_le_of_injective 2 d.embedding d.embedding_injective).trans haut

include d in
theorem elementary_rank_le_four (haut : primeRank 2 (MulAut M12) ≤ 4)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) : rank A ≤ 4 := by
  have hc := (primeRank_le_iff_elementary_card_le G).mp (d.primeRank_le_four haut) A hA
  have hl := Nat.log_monotone (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hl

include h in
/-- An elementary sixteen cannot be contained in the residual M₁₂. -/
theorem elementary_sixteen_not_le_residual (hinner : primeRank 2 M12 ≤ 3)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    ¬ A ≤ solvableResidual G := by
  intro hle
  let := hA
  let : IsElementaryAbelian 2 (A.subgroupOf (solvableResidual G)) :=
    IsElementaryAbelian.subgroupOf hle
  have hr : primeRank 2 (solvableResidual G) ≤ 3 := by
    rw [Theory.GroupTheory.primeRank_equiv 2 h.residualEquiv]
    exact hinner
  have hb := (primeRank_le_iff_elementary_card_le (solvableResidual G)).mp hr
    (A.subgroupOf (solvableResidual G)) inferInstance
  have hcard : Nat.card (A.subgroupOf (solvableResidual G)) = Nat.card A := by
    rw [← card_map_of_injective (solvableResidual G).subtype_injective,
      map_subgroupOf_eq_of_le hle]
  rw [hcard, hc] at hb
  norm_num at hb

/-- An elementary sixteen constructs the actual ambient automorphism identification. -/
theorem embedding_surjective_of_elementary_sixteen (hinner : primeRank 2 M12 ≤ 3)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    Function.Surjective d.embedding := by
  have hn := elementary_sixteen_not_le_residual (h := h) hinner A hA hc
  obtain ⟨g, hgA, hg⟩ := Set.not_subset.mp hn
  exact d.embedding_surjective_of_outer hg

@[expose] noncomputable def automorphismEquivOfElementarySixteen (hinner : primeRank 2 M12 ≤ 3)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    G ≃* MulAut M12 :=
  MulEquiv.ofBijective d.embedding
    ⟨d.embedding_injective, d.embedding_surjective_of_elementary_sixteen hinner A hA hc⟩

@[simp] theorem automorphismEquivOfElementarySixteen_apply (hinner : primeRank 2 M12 ≤ 3)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) (g : G) :
    d.automorphismEquivOfElementarySixteen hinner A hA hc g = d.embedding g := rfl

omit [Finite G] in
theorem fixedCodim_map (A : Subgroup G) :
    fixedCodim ρ A = fixedCodim d.automorphismRepresentation (A.map d.embedding) :=
  fixedCodim_map_equivariant ρ d.automorphismRepresentation d.embedding
    h.moduleEquiv.toLinearEquiv d.equivariant A

omit [Finite G] in
theorem finrank_fixedSpace_map [FiniteDimensional (ZMod 2) V] (A : Subgroup G) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) =
      Module.finrank (ZMod 2) (fixedSpace d.automorphismRepresentation (A.map d.embedding)) := by
  have hV := fixedCodim_add_finrank ρ A
  have hW := fixedCodim_add_finrank d.automorphismRepresentation (A.map d.embedding)
  rw [d.fixedCodim_map, h.finrank_eq_ten ρ] at hV
  rw [finrank_m12Heart] at hW
  omega

omit [Finite G] in
theorem finrank_fixedSpaceSpan_map [FiniteDimensional (ZMod 2) V] (A : Subgroup G) :
    Module.finrank (ZMod 2) (fixedSpaceSpan ρ A) =
      Module.finrank (ZMod 2) (fixedSpaceSpan d.automorphismRepresentation (A.map d.embedding)) := by
  have he := fixedSpaceSpan_codim_map_equivariant ρ d.automorphismRepresentation
    d.embedding d.embedding_injective h.moduleEquiv.toLinearEquiv d.equivariant A
  have hV := (fixedSpaceSpan ρ A).finrank_quotient_add_finrank
  have hW := (fixedSpaceSpan d.automorphismRepresentation (A.map d.embedding)).finrank_quotient_add_finrank
  rw [h.finrank_eq_ten ρ] at hV
  rw [finrank_m12Heart] at hW
  omega

end AmbientExtension
end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
