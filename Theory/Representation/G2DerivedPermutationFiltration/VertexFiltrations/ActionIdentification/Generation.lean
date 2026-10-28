module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.ActionIdentification.GenerationData

/-!
# The two published generators generate the actual derived G₂ group

Root and Weyl generation, with the sixteen checked Schreier identities,
expresses every ambient element as a word in the two generators times
1 or F(1). The sign character excludes the latter coset in the commutator
subgroup. Thus the published free-group homomorphism is surjective.
This supports Aschbacher–Smith G.7.2(3), printed p.348.
-/

public section

open Atlas.G2 Atlas.SplitOctonion
namespace G2DerivedPermutationFiltration.VertexCoordinates
open ActionGeneration
set_option maxRecDepth 10000

private theorem unipotent_le_of_roots (S : Subgroup FullGroup)
    (h : ∀ j : Fin 6, rootGenerator ⟨j.val, by omega⟩ ∈ S) :
    Atlas.G2.unipotent ≤ S := by
  have hr (r : ZMod 2 → FullGroup) (h0 : r 0 = 1) (h1 : r 1 ∈ S) :
      ∀ a, r a ∈ S := by
    intro a
    have ha : a = 0 ∨ a = 1 := (by decide +kernel : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
    rcases ha with rfl | rfl
    · rw [h0]; exact S.one_mem
    · exact h1
  rw [Atlas.G2.unipotent, Subgroup.closure_le]
  simp only [Set.union_subset_iff, Set.range_subset_iff]
  exact ⟨⟨⟨⟨⟨hr rootA rootA_zero (h 0), hr rootB rootB_zero (h 1)⟩,
    hr rootC rootC_zero (h 2)⟩, hr rootD rootD_zero (h 3)⟩,
    hr rootE rootE_zero (h 4)⟩, hr rootF rootF_zero (h 5)⟩

private theorem torus_le (S : Subgroup FullGroup) : splitTorus ≤ S := by
  rintro _ ⟨⟨a,b⟩,rfl⟩
  have ha : a = 1 := Subsingleton.elim _ _
  have hb : b = 1 := Subsingleton.elim _ _
  subst a; subst b
  change torus 1 1 ∈ S
  have he : torus (1 : (ZMod 2)ˣ) 1 = 1 := by
    exact map_one torusHom
  rw [he]
  exact S.one_mem

private theorem root_generation : Subgroup.closure (Set.range rootGenerator) = ⊤ := by
  let S := Subgroup.closure (Set.range rootGenerator)
  have hr (j : Fin 8) : rootGenerator j ∈ S := Subgroup.subset_closure ⟨j,rfl⟩
  have hu : Atlas.G2.unipotent ≤ S := unipotent_le_of_roots S (fun j => hr _)
  apply top_unique
  rw [← generated_eq_top (F := ZMod 2)]
  apply sup_le _ (torus_le S)
  rw [rootWeylSubgroup, Subgroup.closure_le]
  exact Set.union_subset hu (by
    intro x hx
    rcases hx with rfl | rfl
    · exact hr 6
    · exact hr 7)

private theorem evalSigned_mem (w : List (Fin 2 × Bool)) :
    evalSigned w ∈ ambientWordHom.range := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons a w ih =>
    apply Subgroup.mul_mem _ _ ih
    have ha : ambientGenerator a.1 ∈ ambientWordHom.range := ⟨FreeGroup.of a.1, rfl⟩
    unfold signedGenerator
    split
    · exact ha
    · exact Subgroup.inv_mem _ ha

private theorem rootGenerator_inv (i : Fin 8) : (rootGenerator i)⁻¹ = rootGenerator i := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.pi_ext
  have h : ∀ (i k : Fin 8) (a : ZMod 2),
      ((rootGenerator i)⁻¹).val (Pi.single k a) = (rootGenerator i).val (Pi.single k a) := by
    decide +kernel
  exact h i

private theorem ambient_factor (g : FullGroup) :
    ∃ h ∈ ambientWordHom.range, ∃ b : Fin 2, g = h * (rootF 1)^b.val := by
  let P (g : FullGroup) := ∃ h ∈ ambientWordHom.range, ∃ b : Fin 2,
    g = h * (rootF 1)^b.val
  have step (g : FullGroup) (i : Fin 8) (hg : P g) : P (g * rootGenerator i) := by
    obtain ⟨h,hh,b,rfl⟩ := hg
    refine ⟨h * schreierElement b i,
      Subgroup.mul_mem _ hh (by rw [schreier_identity]; exact evalSigned_mem _),
      b + rootParity i, ?_⟩
    dsimp only [schreierElement]
    group
  have hg : g ∈ Subgroup.closure (Set.range rootGenerator) := by
    rw [root_generation]; trivial
  apply Subgroup.closure_induction_right (p := fun g _ => P g) _ _ _ hg
  · exact ⟨1, Subgroup.one_mem _, 0, by simp⟩
  · rintro x _ _ ⟨i,rfl⟩ hx
    exact step x i hx
  · rintro x _ _ ⟨i,rfl⟩ hx
    simpa only [rootGenerator_inv] using step x i hx

private theorem ambient_range_le : ambientWordHom.range ≤ Group := by
  rintro _ ⟨w,rfl⟩
  rw [← subtype_comp_groupHom]
  exact (groupHom w).property

private theorem shortRoot_not_mem : rootF (1 : ZMod 2) ∉ Group := by
  intro hm
  rw [show Group = BinaryException.H from BinaryParabolicPair.commutator_eq_longRootClosure,
    ← BinaryException.lineSign_kernel] at hm
  have he := MonoidHom.mem_ker.mp hm
  rw [Binary.lineSign_rootF_one] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) he

theorem groupHom_surjective : Function.Surjective groupHom := by
  intro g
  obtain ⟨h,hh,b,hg⟩ := ambient_factor g.val
  have hm : g.val ∈ ambientWordHom.range := by
    fin_cases b
    · rw [hg]; simpa using hh
    · have hf : rootF (1 : ZMod 2) ∈ Group := by
        have h := Group.mul_mem (Group.inv_mem (ambient_range_le hh)) g.property
        rw [hg] at h
        simpa using h
      exact (shortRoot_not_mem hf).elim
  obtain ⟨w,hw⟩ := hm
  refine ⟨w, Subtype.ext ?_⟩
  change (Group.subtype.comp groupHom) w = g.val
  rw [subtype_comp_groupHom]
  exact hw

end G2DerivedPermutationFiltration.VertexCoordinates
