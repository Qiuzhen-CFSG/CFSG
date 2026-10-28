module

public import Theory.GroupAction.CyclicQuotientSmallLayer

/-!
# The literal cyclic displacement homomorphism

For a homomorphism from a normalized finite subgroup to an abelian group,
`u ↦ q(u) q(i u i⁻¹)⁻¹` is a homomorphism. Its range is exactly the image
of the subgroup [U,⟨i⟩]. This packages the cyclic-power argument independently
of the small-layer estimate, for quotient-module identifications.

Source: the displacement argument in Aschbacher–Smith 14.4.9, p.1010.
-/

@[expose] public section
namespace Subgroup
open scoped commutatorElement IsMulCommutative
variable {G Q : Type*} [Group G] [Group Q] [IsMulCommutative Q]

/-- Conjugation by the chosen normalizing element, as an endomorphism. -/
def normalizingConjugation (U : Subgroup G) (i : G)
    (hiU : i ∈ normalizer (U : Set G)) : U →* U where
  toFun u := ⟨i * (u : G) * i⁻¹, (mem_normalizer_iff.mp hiU u).mp u.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' := by intro u v; apply Subtype.ext; simp [mul_assoc]

/-- The displacement in the prescribed abelian image. -/
def cyclicDisplacement (U : Subgroup G) (q : U →* Q) (i : G)
    (hiU : i ∈ normalizer (U : Set G)) : U →* Q :=
  q * (q.comp (normalizingConjugation U i hiU))⁻¹

/-- Its value is the image of the literal commutator. -/
theorem cyclicDisplacement_apply (U : Subgroup G) (q : U →* Q) (i : G)
    (hiU : i ∈ normalizer (U : Set G)) (u : U) :
    cyclicDisplacement U q i hiU u = q ⟨⁅(u : G),i⁆,
      (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU))
        (commutator_mem_commutator u.property (mem_zpowers i))⟩ := by
  change q u * (q (normalizingConjugation U i hiU u))⁻¹ = _
  rw [← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  simp [normalizingConjugation, commutatorElement_def, mul_assoc]

/-- Single displacements have exactly the whole cyclic commutator image. -/
theorem cyclicDisplacement_range [Finite G]
    (U : Subgroup G) (q : U →* Q) (i : G)
    (hiU : i ∈ normalizer (U : Set G)) :
    (cyclicDisplacement U q i hiU).range = ((⁅U,zpowers i⁆).subgroupOf U).map q := by
  let f := cyclicDisplacement U q i hiU
  have hBU : ⁅U,zpowers i⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)
  apply le_antisymm
  · rintro v ⟨u,rfl⟩
    rw [cyclicDisplacement_apply]
    exact mem_map_of_mem q (commutator_mem_commutator u.property (mem_zpowers i))
  · let E := (f.range.comap q).map U.subtype
    have hsingle (u : G) (hu : u ∈ U) : ⁅u,i⁆ ∈ E := by
      refine ⟨⟨⁅u,i⁆,hBU (commutator_mem_commutator hu (mem_zpowers i))⟩,?_,rfl⟩
      exact ⟨⟨u,hu⟩,cyclicDisplacement_apply U q i hiU ⟨u,hu⟩⟩
    have hE : ⁅U,zpowers i⁆ ≤ E :=
      commutator_zpowers_le_of_generator_normalizes U E i hiU hsingle
    rintro v ⟨u,hu,rfl⟩
    obtain ⟨w,hw,he⟩ := hE hu
    exact (show w = u from Subtype.ext he) ▸ hw

/-- First isomorphism theorem with the literal map on representatives. -/
theorem exists_quotient_equiv_image
    {V W : Type*} [Group V] [Group W] (f : V →* W)
    (N : Subgroup V) [N.Normal] (M : Subgroup W)
    (hker : f.ker = N) (hrange : f.range = M) :
    ∃ e : (V ⧸ N) ≃* M, ∀ v : V,
      (e (QuotientGroup.mk' N v) : W) = f v := by
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange)), ?_⟩
  intro v
  rfl
end Subgroup
