module

public import Theory.SpecificGroups.SU3.FullTorusNormalizer
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source

/-!
# Full-torus escape in the marked unitary source component

Every odd-primary subgroup of the marked projective Borel has an escaping
normalizer. The proof uses the full quadratic-field torus and conjugacy
inside the Borel. Transport through the literal source component marking
therefore requires no containment in the smaller selected cyclic subgroup.
For the original component, coprime quotient normalizer lifting retains
the actual source quotient map and the prescribed subgroup.

Source: Aschbacher–Smith 4.4.13(1), pp.623–624, and E.2.2(2a), pp.215–216.
The last theorem leaves coprimality with the source kernel explicit.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels BenderSuzuki.MatrixGroups
variable {X : Type*} [Group X]

/-- The actual source component and overlap satisfy full unitary escape. -/
theorem unitary_sourceImage_escape {M K : Subgroup X} {f : ℕ}
    (hm : UnitaryModel M K f) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup (sourceImage M K)) (hA : IsPGroup p A)
    (hAB : A ≤ componentOverlap M K) :
    ¬ normalizer (A : Set _) ≤ componentOverlap M K := by
  obtain ⟨F,hfield,hfin,hchar,J,hJ,_,_,_,_,e,he⟩ := hm
  let := hfield
  let := hfin
  let := hchar
  have hmodel := Theory.SpecificGroups.UnitaryBorel.odd_normalizer_not_le_borel J hJ hp
    (A.map e.toMonoidHom) (hA.map e.toMonoidHom) ((map_mono hAB).trans_eq he)
  intro hn
  apply hmodel
  rw [← map_equiv_normalizer_eq]
  exact (map_mono hn).trans_eq he

private theorem source_projection_overlap_preimage (M K : Subgroup X) :
    (componentOverlap M K).comap ((QuotientGroup.mk' (sourceKernel M)).subgroupMap K) =
      M.subgroupOf K := by
  ext k
  change QuotientGroup.mk' (sourceKernel M) k ∈
    (M ⊓ K).map (QuotientGroup.mk' (sourceKernel M)) ↔ (k : X) ∈ M
  constructor
  · rintro ⟨m,hm,hmk⟩
    have hd := M.normalCore_le (QuotientGroup.eq_iff_div_mem.mp hmk)
    have hh := M.mul_mem (M.inv_mem hd) hm.1
    simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one]
      using hh
  · intro hk
    exact ⟨k,⟨hk,k.property⟩,rfl⟩

variable [Finite X]

/-- The marked unitary branch lifts escape for the prescribed original
odd-primary subgroup whenever the literal source projection is coprime. -/
theorem unitary_original_escape_of_coprime_kernel {M K : Subgroup X} {f : ℕ}
    (hm : UnitaryModel M K f) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup X) (hA : IsPGroup p A) (hAM : A ≤ M) (hAK : A ≤ K)
    (hcop : Nat.Coprime p
      (Nat.card ((QuotientGroup.mk' (sourceKernel M)).subgroupMap K).ker)) :
    ¬ normalizer (A : Set X) ≤ M := by
  let r : K →* sourceImage M K := (QuotientGroup.mk' (sourceKernel M)).subgroupMap K
  let AK := A.subgroupOf K
  have hpre : (componentOverlap M K).comap r = M.subgroupOf K :=
    source_projection_overlap_preimage M K
  have hAKp : IsPGroup p AK := hA.comap_subtype
  let : Fact (IsPGroup p AK) := ⟨hAKp⟩
  have hAB : AK.map r ≤ componentOverlap M K := by
    apply map_le_iff_le_comap.mpr
    rw [hpre]
    exact fun a ha => hAM ha
  have hn := unitary_sourceImage_escape hm hp (AK.map r) (hAKp.map r) hAB
  intro hN
  apply hn
  rw [normalizer_map_eq_of_coprime_kernel p AK r
    ((QuotientGroup.mk' (sourceKernel M)).subgroupMap_surjective K) hcop]
  apply map_le_iff_le_comap.mpr
  rw [hpre]
  intro k hk
  apply hN
  have hh := AK.le_normalizer_map K.subtype (mem_map_of_mem K.subtype hk)
  rwa [map_subgroupOf_eq_of_le hAK] at hh

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
