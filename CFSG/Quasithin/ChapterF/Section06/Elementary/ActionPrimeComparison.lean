module
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.DistinctCores

/-!
# Comparing the action and prime-to-three quotients of a Goldschmidt triple

Suppose a quotient with trivial two-core has two-group kernels on both
vertices. F.6.8 identifies each local kernel with the ambient two-core.
F.6.11 gives the same local kernel for the prime-to-three quotient. Thus
both quotients have canonically isomorphic local groups, with their original
maps preserved, even without an identification of the whole quotients.
The action kernel is solvable by F.6.8 and extension closure.

This comparison is used in the original 14.3.31 amalgam to apply F.6.18
to the actual SQTK cover. Source: Aschbacher--Smith F.6.8 and F.6.11,
printed pp.305--307.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
variable {G D : Type*} [Group G] [Finite G] [Group D]
variable {A B : Subgroup G}

/-- The local action kernel is precisely the ambient two-core. -/
theorem IsGoldschmidtTriple.action_kernel_on_vertex
    (h : IsGoldschmidtTriple A B) (f : G →* D) (hf : Function.Surjective f)
    (hc : pCore 2 D = ⊥)
    (ha : IsPGroup 2 (f.subgroupMap A).ker)
    (hb : IsPGroup 2 (f.subgroupMap B).ker)
    (C : Subgroup G) (hCA : C ≤ A) :
    (f.subgroupMap C).ker = (pCore 2 G).subgroupOf C := by
  have hlocal (M : Subgroup G) (hm : IsPGroup 2 (f.subgroupMap M).ker) :
      M ⊓ f.ker ≤ M.pCoreIn 2 := by
    have hp : (f.subgroupMap M).ker ≤ pCore 2 M := le_sSup ⟨inferInstance,hm⟩
    rintro x ⟨hx,hxf⟩
    refine ⟨⟨x,hx⟩,hp ?_,rfl⟩
    exact Subtype.ext hxf
  have hleft := hlocal A ha
  have hright := hlocal B hb
  have hk : pCore 2 G ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    apply le_bot_iff.mp
    rw [←hc]
    exact le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  rw [ker_subgroupMap]
  ext x
  change f (x:G) = 1 ↔ (x:G) ∈ pCore 2 G
  constructor
  · intro hx
    apply h.normal_intersection_le_twoCore f.ker hleft hright
    exact ⟨h.local_twoCore_le_intersection (hleft ⟨hCA x.property,hx⟩),hx⟩
  · exact fun hx => hk hx


/-- Two-group kernels on both vertices make the full action kernel solvable. -/
theorem IsGoldschmidtTriple.action_kernel_solvable
    (h : IsGoldschmidtTriple A B) (f : G →* D)
    (ha : IsPGroup 2 (f.subgroupMap A).ker)
    (hb : IsPGroup 2 (f.subgroupMap B).ker) : Group.IsSolvable f.ker := by
  have hlocal (M : Subgroup G) (hm : IsPGroup 2 (f.subgroupMap M).ker) :
      M ⊓ f.ker ≤ M.pCoreIn 2 := by
    have hp : (f.subgroupMap M).ker ≤ pCore 2 M := le_sSup ⟨inferInstance,hm⟩
    rintro x ⟨hx,hxf⟩
    exact ⟨⟨x,hx⟩,hp (Subtype.ext hxf),rfl⟩
  let X := f.ker ⊔ pCore 2 G
  let N := (pCore 2 G).subgroupOf X
  have hq : Group.IsSolvable (X ⧸ N) :=
    h.normal_quotient_solvable f.ker (hlocal A ha) (hlocal B hb)
  let : Group.IsNilpotent N := pCore_isPGroup.comap_subtype.isNilpotent
  let : Group.IsSolvable X := (Group.isSolvable_iff_subgroup_quotient N).mpr
    ⟨inferInstance,hq⟩
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective (show f.ker ≤ X from le_sup_left))

/-- Canonical local comparison with the prime-to-three quotient of the cover. -/
noncomputable def IsGoldschmidtTriple.action_prime_local_equiv
    (h : IsGoldschmidtTriple A B) (f : G →* D) (hf : Function.Surjective f)
    (hc : pCore 2 D = ⊥)
    (ha : IsPGroup 2 (f.subgroupMap A).ker)
    (hb : IsPGroup 2 (f.subgroupMap B).ker)
    (C : Subgroup G) (hCA : C ≤ A) :
    C.map f ≃* C.map (QuotientGroup.mk' (pPrimeCore 3 G)) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (f.subgroupMap_surjective C)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      ((h.action_kernel_on_vertex f hf hc ha hb C hCA).trans
        (h.primeToThreeCore_subgroup_kernel C hCA).symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap_surjective C)))

/-- The comparison retains the two original quotient maps on every local element. -/
theorem IsGoldschmidtTriple.action_prime_local_equiv_apply
    (h : IsGoldschmidtTriple A B) (f : G →* D) (hf : Function.Surjective f)
    (hc : pCore 2 D = ⊥)
    (ha : IsPGroup 2 (f.subgroupMap A).ker)
    (hb : IsPGroup 2 (f.subgroupMap B).ker)
    (C : Subgroup G) (hCA : C ≤ A) (x : C) :
    h.action_prime_local_equiv f hf hc ha hb C hCA (f.subgroupMap C x) =
      (QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap C x := by
  have he : (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap C)
    (f.subgroupMap_surjective C)) (QuotientGroup.mk' _ x) = f.subgroupMap C x := rfl
  rw [←he]
  simp [action_prime_local_equiv]
  rfl
end CFSG.Quasithin.ChapterF
