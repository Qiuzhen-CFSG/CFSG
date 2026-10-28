module
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.OrbitCover.Points
public import Theory.Alternating.Aut
/-!
# Comparing the actual orbit image with the alternating pair action

Conjugation along the certified point/pair bijection identifies the two
actual generators with the pair actions of the displayed even permutations.
Five checked words give the standard three-cycle generators of A7. The
faithful action on two-subsets therefore identifies the whole image.

Source: GLS3 Table 5.3p, outer 2C row; the pair correspondence in
`FixedStructure/Source/README.md`. The general three-cycle generation theorem
is the existing `GroupTheory.AutAlternating` result.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Held.OuterInvolution.FixedStructure
def permConj : Equiv.Perm PointOrbit ≃* Equiv.Perm Pair7 where
  toFun p := orbitPairEquiv.symm.trans (p.trans orbitPairEquiv)
  invFun p := orbitPairEquiv.trans (p.trans orbitPairEquiv.symm)
  left_inv p := by
    ext x
    simp
  right_inv p := by
    ext x
    simp
  map_mul' p q := by
    ext x
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.Perm.mul_apply]

def pairActionHom : candidate →* Equiv.Perm Pair7 :=
  permConj.toMonoidHom.comp orbitAction

def pairPermHom : alternatingGroup (Fin 7) →* Equiv.Perm Pair7 :=
  MulAction.toPermHom (alternatingGroup (Fin 7)) Pair7

theorem orbitPairEquiv_pointEquiv (i : Fin 21) :
    orbitPairEquiv (pointEquiv i) = pairEquiv i := by
  exact congrArg pairEquiv (pointEquiv.symm_apply_apply i)

theorem orbitPairEquiv_symm_pairEquiv (i : Fin 21) :
    orbitPairEquiv.symm (pairEquiv i) = pointEquiv i := by
  apply orbitPairEquiv.injective
  rw [Equiv.apply_symm_apply, orbitPairEquiv_pointEquiv]

theorem pairActionHom_first : pairActionHom firstGenerator = pairPermHom xAlt := by
  apply Equiv.ext
  intro p
  obtain ⟨i, rfl⟩ := pairEquiv.surjective p
  change orbitPairEquiv (orbitAction firstGenerator
    (orbitPairEquiv.symm (pairEquiv i))) = xAlt • pairEquiv i
  rw [orbitPairEquiv_symm_pairEquiv]
  have h : orbitAction firstGenerator (pointEquiv i) = pointEquiv (pointPermX i) := by
    apply Subtype.ext
    exact firstGenerator_smul_orbitPoints i
  rw [h, orbitPairEquiv_pointEquiv]
  exact (pairPoints_x i).symm

theorem pairActionHom_second : pairActionHom secondGenerator = pairPermHom yAlt := by
  apply Equiv.ext
  intro p
  obtain ⟨i, rfl⟩ := pairEquiv.surjective p
  change orbitPairEquiv (orbitAction secondGenerator
    (orbitPairEquiv.symm (pairEquiv i))) = yAlt • pairEquiv i
  rw [orbitPairEquiv_symm_pairEquiv]
  have h : orbitAction secondGenerator (pointEquiv i) = pointEquiv (pointPermY i) := by
    apply Subtype.ext
    exact secondGenerator_smul_orbitPoints i
  rw [h, orbitPairEquiv_pointEquiv]
  exact (pairPoints_y i).symm

set_option maxRecDepth 4096 in
theorem alternatingGenerators :
    Subgroup.closure ({xAlt, yAlt} : Set (alternatingGroup (Fin 7))) = ⊤ := by
  let H : Subgroup (alternatingGroup (Fin 7)) :=
    Subgroup.closure ({xAlt, yAlt} : Set (alternatingGroup (Fin 7)))
  have hx : xAlt ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : yAlt ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have h2 :
      (⟨GroupTheory.AutAlternating.genPerm 7 2,
        GroupTheory.AutAlternating.genPerm_mem_alternatingGroup (by decide) (by decide) (by decide)⟩ :
        alternatingGroup (Fin 7)) ∈ H := by
    rw [show (⟨GroupTheory.AutAlternating.genPerm 7 2, _⟩ : alternatingGroup (Fin 7)) =
        yAlt * xAlt * xAlt * yAlt * yAlt by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      fin_cases i <;> decide]
    exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hy hx) hx) hy) hy)
  have h3 :
      (⟨GroupTheory.AutAlternating.genPerm 7 3,
        GroupTheory.AutAlternating.genPerm_mem_alternatingGroup (by decide) (by decide) (by decide)⟩ :
        alternatingGroup (Fin 7)) ∈ H := by
    rw [show (⟨GroupTheory.AutAlternating.genPerm 7 3, _⟩ : alternatingGroup (Fin 7)) =
        xAlt⁻¹ * yAlt * yAlt * yAlt * xAlt⁻¹ * yAlt * yAlt by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      fin_cases i <;> decide]
    exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hx) hy) hy) hy) (H.inv_mem hx)) hy) hy)
  have h4 :
      (⟨GroupTheory.AutAlternating.genPerm 7 4,
        GroupTheory.AutAlternating.genPerm_mem_alternatingGroup (by decide) (by decide) (by decide)⟩ :
        alternatingGroup (Fin 7)) ∈ H := by
    rw [show (⟨GroupTheory.AutAlternating.genPerm 7 4, _⟩ : alternatingGroup (Fin 7)) =
        xAlt * yAlt * yAlt * xAlt⁻¹ * yAlt * yAlt * yAlt * xAlt⁻¹ * xAlt⁻¹ by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      fin_cases i <;> decide]
    exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hx hy) hy) (H.inv_mem hx)) hy) hy) hy) (H.inv_mem hx)) (H.inv_mem hx))
  have h5 :
      (⟨GroupTheory.AutAlternating.genPerm 7 5,
        GroupTheory.AutAlternating.genPerm_mem_alternatingGroup (by decide) (by decide) (by decide)⟩ :
        alternatingGroup (Fin 7)) ∈ H := by
    rw [show (⟨GroupTheory.AutAlternating.genPerm 7 5, _⟩ : alternatingGroup (Fin 7)) =
        xAlt * yAlt * xAlt⁻¹ * yAlt * yAlt * yAlt * xAlt⁻¹ * yAlt * xAlt⁻¹ by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      fin_cases i <;> decide]
    exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) hy) hy) hy) (H.inv_mem hx)) hy) (H.inv_mem hx))
  have h6 :
      (⟨GroupTheory.AutAlternating.genPerm 7 6,
        GroupTheory.AutAlternating.genPerm_mem_alternatingGroup (by decide) (by decide) (by decide)⟩ :
        alternatingGroup (Fin 7)) ∈ H := by
    rw [show (⟨GroupTheory.AutAlternating.genPerm 7 6, _⟩ : alternatingGroup (Fin 7)) =
        yAlt * xAlt⁻¹ * yAlt * yAlt * yAlt * xAlt⁻¹ * yAlt by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      fin_cases i <;> decide]
    exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hy (H.inv_mem hx)) hy) hy) hy) (H.inv_mem hx)) hy)
  apply le_antisymm le_top
  rw [← GroupTheory.AutAlternating.gen_closure_alternatingGroup_eq_top (n := 7) (by decide)]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨⟨i, hi0, hi1⟩, rfl⟩
  fin_cases i
  · exact (hi0 rfl).elim
  · exact (hi1 rfl).elim
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

theorem pairActionHom_range_eq : pairActionHom.range = pairPermHom.range := by
  apply le_antisymm
  · rintro p ⟨g, rfl⟩
    have hg : g ∈ Subgroup.closure ({firstGenerator, secondGenerator} : Set candidate) := by
      rw [closure_pair]
      exact Subgroup.mem_top _
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
        rcases Set.mem_insert_iff.mp hg with rfl | hg
        · exact ⟨xAlt, pairActionHom_first.symm⟩
        · rw [Set.mem_singleton_iff] at hg
          subst g
          exact ⟨yAlt, pairActionHom_second.symm⟩
    | one => exact ⟨1, by simp⟩
    | mul x y hx hy ihx ihy =>
        rw [map_mul]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
        rw [map_inv]
        exact Subgroup.inv_mem _ ih
  · rintro p ⟨g, rfl⟩
    have hg : g ∈ Subgroup.closure ({xAlt, yAlt} : Set (alternatingGroup (Fin 7))) := by
      have ht : g ∈ (⊤ : Subgroup (alternatingGroup (Fin 7))) := Subgroup.mem_top _
      rw [← alternatingGenerators] at ht
      exact ht
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
        rcases Set.mem_insert_iff.mp hg with rfl | hg
        · exact ⟨firstGenerator, pairActionHom_first⟩
        · rw [Set.mem_singleton_iff] at hg
          subst g
          exact ⟨secondGenerator, pairActionHom_second⟩
    | one => exact ⟨1, by simp⟩
    | mul x y hx hy ihx ihy =>
        rw [map_mul]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
        rw [map_inv]
        exact Subgroup.inv_mem _ ih

theorem permConj_map_orbitImage :
    Subgroup.map permConj.toMonoidHom orbitImage = pairActionHom.range := by
  ext p
  constructor
  · rintro ⟨q, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨orbitAction g, ⟨g, rfl⟩, rfl⟩

noncomputable def orbitImagePairEquiv : orbitImage ≃* pairActionHom.range :=
  (permConj.subgroupMap orbitImage).trans
    (MulEquiv.subgroupCongr permConj_map_orbitImage)

local instance : FaithfulSMul (alternatingGroup (Fin 7)) Pair7 :=
  Set.powersetCard.faithfulSMul (G := alternatingGroup (Fin 7))
    (α := Fin 7) (n := 2) (by decide) (by norm_num [ENat.card_eq_coe_fintype_card])

theorem pairPermHom_injective : Function.Injective pairPermHom := by
  intro g h gh
  apply MulAction.toPerm_injective (α := alternatingGroup (Fin 7)) (β := Pair7)
  exact gh

noncomputable def pairPermEquiv : alternatingGroup (Fin 7) ≃* pairPermHom.range :=
  MulEquiv.ofBijective pairPermHom.rangeRestrict
    ⟨by
      intro g h gh
      apply pairPermHom_injective
      exact congrArg Subtype.val gh,
      pairPermHom.rangeRestrict_surjective⟩

end Held.OuterInvolution.FixedStructure
