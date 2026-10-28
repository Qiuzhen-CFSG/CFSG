module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixModel
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ProductCentralizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreImage
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The literal six-letter kernel above the source block

If I=KS with S a two-group and K a normal short subgroup, then the
centralizer of U(K) in I is O₂(I). The upper bound follows because the
quotient I/K is a two-group and C_K(U(K))=O₂(K); the reverse bound is the
short-group two-subgroup action theorem. Applying this to the same full-core
coordinates identifies the six-letter action kernel, preserves its alternating
component, and maps the actual source Sylow subgroup onto a Sylow of the image.

Source: Aschbacher–Smith C.1.11 and 14.6.10(5), printed pp.124,1029–1030.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- A normal short subgroup with a two-group supplement determines the full-module action kernel. -/
theorem source_centralizer_eq_core (I K S : Subgroup G)
    (hKI : K ≤ I) (hIK : I ≤ normalizer (K : Set G))
    (hK : IsShort K) (hS : IsPGroup 2 S) (hgen : K ⊔ S = I) :
    (centralizer (sourceModule K : Set G)).subgroupOf I = pCore 2 I := by
  let N := K.subgroupOf I
  let : N.Normal := normal_subgroupOf_of_le_normalizer hIK
  have hSI : S ≤ I := le_sup_right.trans hgen.le
  have hsup : N ⊔ S.subgroupOf I = ⊤ := by
    rw [←subgroupOf_sup hKI hSI,hgen,subgroupOf_self]
  have hquot := isPGroup_quotient_of_sup_eq_top N (S.subgroupOf I) hS.comap_subtype hsup
  let C := (centralizer (sourceModule K : Set G)).subgroupOf I
  have hIW : I ≤ normalizer (sourceModule K : Set G) :=
    hIK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hCN : C.Normal :=
    (normal_subgroupOf_centralizer_normalizer (sourceModule K : Set G)).comap (inclusion hIW)
  let := hCN
  have hCp : IsPGroup 2 C := by
    intro c
    obtain ⟨n,hn⟩ := hquot (QuotientGroup.mk' N c.val)
    have hnk : (c.val : G) ^ 2^n ∈ K := by
      have hh : c.val ^ 2^n ∈ N := by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' N (c.val ^ 2^n) = 1
        rwa [map_pow]
      exact hh
    have hnc : (⟨(c.val : G) ^ 2^n,hnk⟩ : K) ∈ centralizer (blockU K : Set K) := by
      intro v hv
      apply Subtype.ext
      exact (centralizer (sourceModule K : Set G)).pow_mem c.property (2^n)
        v.val (mem_map_of_mem K.subtype hv)
    rw [hK.centralizer_blockU] at hnc
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := K)) ⟨_,hnc⟩
    refine ⟨n+m,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (c.val : G) ^ 2^(n+m) = 1
    rw [pow_add,pow_mul]
    exact congrArg (fun x : pCore 2 K => ((x : K) : G)) hm
  have hCle : C ≤ pCore 2 I := le_sSup (show C.Normal ∧ IsPGroup 2 C from ⟨hCN,hCp⟩)
  apply le_antisymm hCle
  intro q hq
  have hQN : I.pCoreIn 2 ≤ normalizer (K : Set G) := (pCoreIn_le 2 I).trans hIK
  have hKQ : K ≤ normalizer (I.pCoreIn 2 : Set G) := hKI.trans
    (I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  exact hK.normalizing_twoGroup_centralizes_blockU (isPGroup_pCoreIn 2 I) hKQ hQN
    (mem_map_of_mem I.subtype hq)

/-- Restrict the actual normalizer action without changing its coordinates. -/
def restrictedActor (I K : Subgroup G) (hIK : I ≤ normalizer (K : Set G))
    (f : normalizer (K : Set G) →* Equiv.Perm (Fin 6)) : I →* Equiv.Perm (Fin 6) :=
  f.comp (inclusion hIK)

/-- Restricting the original six-letter action to I kills exactly O₂(I). -/
theorem restrictedActor_kernel (I K S : Subgroup G)
    (hKI : K ≤ I) (hIK : I ≤ normalizer (K : Set G))
    (hK : IsShort K) (hS : IsPGroup 2 S) (hgen : K ⊔ S = I)
    (E : sourceModule K ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (K : Set G) →* Equiv.Perm (Fin 6))
    (he : ∀ (n : normalizer (K : Set G)) (u : sourceModule K)
      (hu : n.val * u.val * n.val⁻¹ ∈ sourceModule K),
      (E ⟨n.val*u.val*n.val⁻¹,hu⟩).toAdd =
        coreRepresentation (Fin 6) (f n) (E u).toAdd) :
    (restrictedActor I K hIK f).ker = pCore 2 I := by
  rw [←source_centralizer_eq_core I K S hKI hIK hK hS hgen]
  have hk := source_action_kernel K E f he
  ext i
  change inclusion hIK i ∈ f.ker ↔ _
  rw [hk]
  rfl


omit [Finite G] in
/-- The restricted image retains the full alternating component. -/
theorem alternating_le_restricted_range (I K : Subgroup G)
    (hKI : K ≤ I) (hIK : I ≤ normalizer (K : Set G))
    (f : normalizer (K : Set G) →* Equiv.Perm (Fin 6))
    (hA : (K.subgroupOf (normalizer (K : Set G))).map f = alternatingGroup (Fin 6)) :
    alternatingGroup (Fin 6) ≤ (restrictedActor I K hIK f).range := by
  intro g hg
  obtain ⟨n,hn,he⟩ := hA.symm ▸ hg
  exact ⟨⟨n.val,hKI hn⟩,he⟩

/-- The actual source Sylow subgroup maps to a Sylow subgroup of the
restricted six-letter image. -/
theorem restrictedActor_sylow (I K S : Subgroup G)
    (hIK : I ≤ normalizer (K : Set G)) (hSyl : Chapter1.IsSylowIn 2 S I)
    (f : normalizer (K : Set G) →* Equiv.Perm (Fin 6)) :
    Chapter1.IsSylowIn 2 ((S.subgroupOf I).map (restrictedActor I K hIK f))
      (restrictedActor I K hIK f).range := by
  let a := restrictedActor I K hIK f
  obtain ⟨P,hP⟩ := hSyl
  have hSI : S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  have he : S.subgroupOf I = (P : Subgroup I) := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hSI,hP]
  refine ⟨P.mapSurjective a.rangeRestrict_surjective,?_⟩
  change ((P : Subgroup I).map a.rangeRestrict).map a.range.subtype = _
  rw [map_map,MonoidHom.subtype_comp_rangeRestrict,he]

/-- The source group above the rank-five block has the literal six-letter
action with exactly its own two-core as kernel. -/
theorem source_core_coordinates_with_kernel (I K S : Subgroup G)
    (hKI : K ≤ I) (hIK : I ≤ normalizer (K : Set G))
    (hK : IsAlternatingBlock K 6) (hc : Nat.card (sourceModule K) = 32)
    (hSyl : Chapter1.IsSylowIn 2 S I) (hgen : K ⊔ S = I) :
    ∃ E : sourceModule K ≃* Multiplicative (core (Fin 6)),
    ∃ f : normalizer (K : Set G) →* Equiv.Perm (Fin 6),
      (∀ (n : normalizer (K : Set G)) (u : sourceModule K)
        (hu : n.val*u.val*n.val⁻¹ ∈ sourceModule K),
        (E ⟨n.val*u.val*n.val⁻¹,hu⟩).toAdd =
          coreRepresentation (Fin 6) (f n) (E u).toAdd) ∧
      (K.subgroupOf (normalizer (K : Set G))).map f = alternatingGroup (Fin 6) ∧
      (restrictedActor I K hIK f).ker = pCore 2 I ∧
      alternatingGroup (Fin 6) ≤ (restrictedActor I K hIK f).range ∧
      Chapter1.IsSylowIn 2 ((S.subgroupOf I).map (restrictedActor I K hIK f))
        (restrictedActor I K hIK f).range := by
  obtain ⟨E,f,he,hA⟩ := source_core_coordinates K hK hc
  have hS : IsPGroup 2 S := (Chapter1.isSylowIn_iff.mp hSyl).1
  exact ⟨E,f,he,hA,restrictedActor_kernel I K S hKI hIK hK.2.1 hS hgen E f he,
    alternating_le_restricted_range I K hKI hIK f hA,
    restrictedActor_sylow I K S hIK hSyl f⟩
end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
