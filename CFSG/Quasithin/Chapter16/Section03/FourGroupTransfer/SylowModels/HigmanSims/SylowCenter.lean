module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.ModelFacts
public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Enumeration
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# The whole center of the certified HS Sylow subgroup

The existing enumeration certifies a Sylow subgroup with 512 elements.
Commuting with its generators leaves exactly rows 0 and 10, namely 1 and e₀.
The reverse inclusion is checked against the same generators. Conjugation and
an actual HS equivalence then realize every conjugate of ⟨e₀⟩ as the whole
embedded center of an actual Sylow subgroup.

Source: Aschbacher–Smith, proof of 16.3.4, printed p.1178; the exact degree-100
ATLAS carrier and enumeration used in HSInner.ClassCoverage.Enumeration.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
open Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

private theorem center_indices : ∀ i : Fin 512,
    (∀ s : Fin 4, value i (localValue s 1) = localValue s (value i 1) ∧
      value i (localValue s 4) = localValue s (value i 4)) → i = 0 ∨ i = 10 := by
  apply allFin
  decide +kernel

private theorem element_ten : element 10 = e0 := by
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  intro p
  rw [value_spec]
  have hv : ∀ q : Fin 100, value 10 q = inclusion e0 q := by
    apply allFin
    decide +kernel
  exact hv p

private theorem e0_centralizes : subgroup ≤ centralizer ({e0} : Set Carrier) := by
  apply (closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  change sylowGenerator j ∈ centralizer ({e0} : Set Carrier)
  rw [mem_centralizer_singleton_iff]
  have h : ∀ j : Fin 3, ∀ p : Fin 100,
      inclusion (e0 * sylowGenerator j) p = inclusion (sylowGenerator j * e0) p := by
    apply allFin
    decide +kernel
  exact Sporadic.LeechRelated.HS.inclusion_injective (Equiv.ext (fun p => (h j p).symm))

theorem hs_seed_center_eq : (center subgroup).map subgroup.subtype = zpowers e0 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := element_cover x x.property
    have ht (s : Fin 4) : element i * localLetter s = localLetter s * element i := by
      have hm : localLetter s ∈ subgroup := by
        have h (j : Fin 3) : sylowGenerator j ∈ subgroup := subset_closure ⟨j, rfl⟩
        fin_cases s
        · exact h 0
        · exact h 1
        · exact h 2
        · exact subgroup.inv_mem (h 2)
      have hh := congrArg Subtype.val (mem_center_iff.mp hx ⟨localLetter s, hm⟩)
      change localLetter s * (x : Carrier) = (x : Carrier) * localLetter s at hh
      rw [hi] at hh
      exact hh.symm
    have hv (s : Fin 4) (p : Fin 100) :
        value i (localValue s p) = localValue s (value i p) := by
      have hh := congrArg (fun g : Carrier => inclusion g p) (ht s)
      simpa only [map_mul, Equiv.Perm.mul_apply, value_spec, ← localValue_spec] using hh
    change (x : Carrier) ∈ zpowers e0
    rcases center_indices i (fun s => ⟨hv s 1, hv s 4⟩) with rfl | rfl
    · rw [hi, element_zero]
      exact (zpowers e0).one_mem
    · rw [hi, element_ten]
      exact mem_zpowers e0
  · apply zpowers_le.mpr
    have hm : e0 ∈ subgroup := element_ten ▸ element_mem 10
    refine ⟨⟨e0, hm⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (e0_centralizes y.property))

/-- Conjugacy to the marked involution constructs a Sylow subgroup with exactly
this ambient cyclic subgroup as its center. -/
theorem hs_center_embedding_of_isConj {G : Type*} [Group G] (K : Subgroup G)
    (eK : K ≃* ClassificationModels.SporadicName.hs.Carrier)
    (x : K) (hx : IsConj e0 (eK x)) : SylowCenterEmbedding K (zpowers (x : G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  let f : Carrier ≃* K := (MulAut.conj g).trans eK.symm
  refine ⟨Certificate.sylow.mapSurjective (f := f.toMonoidHom) f.surjective, ?_⟩
  change (center ((subgroup.map f.toMonoidHom).map K.subtype)).map
    ((subgroup.map f.toMonoidHom).map K.subtype).subtype = zpowers (x : G)
  rw [map_map, map_center_image_of_injective subgroup
    (K.subtype.comp f.toMonoidHom) (K.subtype_injective.comp f.injective)]
  rw [← map_map, hs_seed_center_eq, MonoidHom.map_zpowers]
  congr 1
  change (eK.symm ((MulAut.conj g) e0) : G) = (x : G)
  rw [show (MulAut.conj g) e0 = eK x from hg, eK.symm_apply_apply]

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
