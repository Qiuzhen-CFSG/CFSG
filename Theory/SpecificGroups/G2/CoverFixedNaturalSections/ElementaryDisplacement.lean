module
public import Theory.SpecificGroups.G2.CoverFixedNaturalSections.CentralCover
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Abelian two-subgroups and central covers of the first G₂ local

A two-perfect subgroup covering the first G₂ local over an even field of
order greater than two centralizes every abelian two-subgroup which it
normalizes and which normalizes it. The commutator is an abelian normal
subgroup of its two-core, hence central by the root-coordinate theorem.
Idempotence of two-perfect action then makes that commutator trivial.

This also applies when the covering subgroup is only subnormal inside a
specified overgroup. The reciprocal normalization follows there from the
subnormal two-perfect lemma, retaining the original ambient embeddings.

Source application: the G₂ alternative in Aschbacher--Smith F.1.12(I)(3),
printed pp.262--263, in the two-chief exclusions of 15.2.4 and 15.2.8,
pp.1105--1110. The imported root calculations retain the ATLAS attribution
in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped IsMulCommutative
namespace Atlas.G2.CoverFixedNaturalSections
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
variable {D : Type*} [Group D] [Finite D]

/-- A central two-cover of the first G₂ local has trivial displacement on
an abelian two-subgroup with reciprocal normalization. -/
theorem abelian_pgroup_commutator_eq_bot_of_cover (hq : 2 < Nat.card F) (K U : Subgroup D)
    (hp : IsPPerfect 2 K) (hu : IsPGroup 2 U) [IsMulCommutative U]
    (hn : K ≤ normalizer (U : Set D))
    (hUK : U ≤ normalizer (K : Set D))
    (f : K →* local₁ (F := F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center K) (hk : IsPGroup 2 f.ker) :
    ⁅U,K⁆ = ⊥ := by
  let C := ⁅U,K⁆
  have hCK : C ≤ K := le_normalizer_iff_commutator_le_right.mp hUK
  have hCU : C ≤ U := le_normalizer_iff_commutator_le_left.mp hn
  let B := C.subgroupOf K
  let : B.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right U K)
  let : IsMulCommutative C := ⟨⟨fun x y => Subtype.ext (congrArg (fun x : U => (x : D))
    (mul_comm (⟨x,hCU x.property⟩ : U) ⟨y,hCU y.property⟩))⟩⟩
  let : IsMulCommutative B := inferInstance
  have hcore : C ≤ (pCore 2 K).map K.subtype :=
    isPGroup_le_pCoreAmbient_of_isSubnormalIn K C 2 hCK
      (inferInstance : B.Normal).isSubnormal (hu.to_le hCU)
  have hB : B ≤ pCore 2 K := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hcore hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hcent := abelian_core_le_center_of_cover hq hp f hf hc hk B hB
  have hcen : C ≤ centralizer (K : Set D) := by
    intro x hx k hkm
    exact congrArg Subtype.val (mem_center_iff.mp
      (hcent (show (⟨x,hCK hx⟩ : K) ∈ B from hx)) ⟨k,hkm⟩)
  have hid := commutator_isPPerfect_idempotent K U hp hu hn
  exact hid.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hcen)

/-- Relative subnormality supplies the reciprocal normalization; no ambient
normality of K is required. -/
theorem abelian_pgroup_commutator_eq_bot_of_subnormal_cover
    (hq : 2 < Nat.card F) (H K U : Subgroup D)
    (hKH : K ≤ H) (hUH : U ≤ H) (hsub : (K.subgroupOf H).IsSubnormal)
    (hp : IsPPerfect 2 K) (hu : IsPGroup 2 U) [IsMulCommutative U]
    (hn : K ≤ normalizer (U : Set D))
    (f : K →* local₁ (F := F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center K) (hk : IsPGroup 2 f.ker) :
    ⁅U,K⁆ = ⊥ := by
  let R := K.subgroupOf H
  let B := U.subgroupOf H
  have hpR : IsPPerfect 2 R := hp.of_surjective
    (subgroupOfEquivOfLe hKH).symm.toMonoidHom (subgroupOfEquivOfLe hKH).symm.surjective
  have hnR : R ≤ normalizer (B : Set H) := by
    rw [← subgroupOf_normalizer_eq hUH]
    exact subgroupOf_mono H hn
  have hNR := le_normalizer_of_isSubnormal_isPPerfect R B hsub hpR hu.comap_subtype hnR
  have hUK : U ≤ normalizer (K : Set D) := by
    rw [← subgroupOf_normalizer_eq hKH] at hNR
    intro x hx
    exact hNR (show (⟨x,hUH hx⟩ : H) ∈ B from hx)
  exact abelian_pgroup_commutator_eq_bot_of_cover hq K U hp hu hn hUK f hf hc hk

end Atlas.G2.CoverFixedNaturalSections
