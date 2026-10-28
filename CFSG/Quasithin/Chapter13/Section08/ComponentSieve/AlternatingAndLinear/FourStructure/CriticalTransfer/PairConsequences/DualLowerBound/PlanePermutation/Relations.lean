module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Centralizer relations in binary permutation modules

If an actor has displacement rank one over the binary field, every element
of its centralizer fixes the displacement pointwise. Consequently every
translated double displacement vanishes in the representation. If these
relations span the actor's displacements in a permutation module, no cyclic
equivariant image of that module can have displacement rank one.

The argument permits kernels, trivial representations, and arbitrary
extensions. Simplicity is used only in the separate faithfulness lemma.
This is the linear reduction for the plane-permutation input in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.4(5), printed p.947, and 13.8.25, pp.960–962.
The finite plane calculation is a separate obligation.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.PlanePermutation

section Relations
variable {G X : Type*} [Group G] [MulAction G X]

/-- A translate of the double displacement attached to a commuting pair. -/
noncomputable def relation (t h c : G) (x : X) : X →₀ ZMod 2 :=
  Finsupp.single (h • (c • (t • x))) 1 - Finsupp.single (h • (c • x)) 1 -
    Finsupp.single (h • (t • x)) 1 + Finsupp.single (h • x) 1

/-- The invariant span of the centralizer double displacements for `t`. -/
noncomputable def centralizerRelations (t : G) : Submodule (ZMod 2) (X →₀ ZMod 2) :=
  Submodule.span (ZMod 2) {w | ∃ h c : G, Commute c t ∧ ∃ x : X, w = relation t h c x}

/-- The finite permutation-module calculation needed for one actor. -/
def DisplacementRelations (t : G) : Prop :=
  ∀ x : X, Finsupp.single (t • x) 1 - Finsupp.single x 1 ∈
    centralizerRelations (X := X) t

/-- The relation space is invariant under every permutation actor. -/
theorem centralizerRelations_map_le (t a : G) :
    (centralizerRelations (X := X) t).map
      (Finsupp.lmapDomain (ZMod 2) (ZMod 2) (a • ·)) ≤
        centralizerRelations (X := X) t := by
  classical
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨h, c, hc, x, rfl⟩
  change Finsupp.lmapDomain (ZMod 2) (ZMod 2) (a • ·) (relation t h c x) ∈
    centralizerRelations (X := X) t
  have he : Finsupp.lmapDomain (ZMod 2) (ZMod 2) (a • ·) (relation t h c x) =
      relation t (a * h) c x := by
    simp only [relation, map_add, map_sub]
    simp [mul_smul]
  rw [he]
  exact Submodule.subset_span ⟨a * h, c, hc, x, rfl⟩

/-- One relation between permutation points transports to their whole orbit. -/
theorem difference_mem_of_translate (t a : G) {x y : X}
    (hxy : Finsupp.single x 1 - Finsupp.single y 1 ∈
      centralizerRelations (X := X) t) :
    Finsupp.single (a • x) 1 - Finsupp.single (a • y) 1 ∈
      centralizerRelations (X := X) t := by
  have h := centralizerRelations_map_le t a
    (Submodule.mem_map_of_mem
      (f := Finsupp.lmapDomain (ZMod 2) (ZMod 2) (a • ·)) hxy)
  simp only [map_sub] at h
  simpa using h

/-- Relations along a chain of permutation points give its endpoint relation. -/
theorem difference_mem_trans (t : G) {x y z : X}
    (hxy : Finsupp.single x 1 - Finsupp.single y 1 ∈
      centralizerRelations (X := X) t)
    (hyz : Finsupp.single y 1 - Finsupp.single z 1 ∈
      centralizerRelations (X := X) t) :
    Finsupp.single x 1 - Finsupp.single z 1 ∈
      centralizerRelations (X := X) t := by
  convert (centralizerRelations (X := X) t).add_mem hxy hyz using 1
  abel


/-- Conjugating an actor transports its centralizer relations. -/
theorem DisplacementRelations.conjugate {t : G}
    (ht : DisplacementRelations (X := X) t) (a : G) :
    DisplacementRelations (X := X) (a * t * a⁻¹) := by
  classical
  let L : (X →₀ ZMod 2) →ₗ[ZMod 2] (X →₀ ZMod 2) :=
    Finsupp.lmapDomain (ZMod 2) (ZMod 2) (a • ·)
  have hm : (centralizerRelations (X := X) t).map L ≤
      centralizerRelations (X := X) (a * t * a⁻¹) := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨h, c, hc, x, rfl⟩
    change L (relation t h c x) ∈ centralizerRelations (X := X) (a * t * a⁻¹)
    have hc' : Commute (a * c * a⁻¹) (a * t * a⁻¹) := by
      exact hc.map (MulAut.conj a)
    have he : L (relation t h c x) =
        relation (a * t * a⁻¹) (a * h * a⁻¹) (a * c * a⁻¹) (a • x) := by
      simp only [relation, map_add, map_sub]
      simp [L, mul_smul]
    rw [he]
    exact Submodule.subset_span ⟨a * h * a⁻¹, a * c * a⁻¹, hc', a • x, rfl⟩
  intro x
  have hh := hm (Submodule.mem_map_of_mem (f := L) (ht (a⁻¹ • x)))
  simp only [map_sub] at hh
  simpa [L, mul_smul] using hh


/-- The relation calculation depends only on the conjugacy class of the actor. -/
theorem DisplacementRelations.of_isConj {t s : G}
    (ht : DisplacementRelations (X := X) t) (h : IsConj t s) :
    DisplacementRelations (X := X) s := by
  obtain ⟨a, rfl⟩ := isConj_iff.mp h
  exact ht.conjugate a

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Over the binary field, the centralizer of an actor fixes its rank-one
image pointwise. This uses invertibility of the representation, not faithfulness. -/
theorem fixes_displacement_of_commute (ρ : Representation (ZMod 2) G V) (t c : G)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 1)
    (hc : Commute c t) (v : V) : ρ c (ρ t v - v) = ρ t v - v := by
  let W := LinearMap.range (ρ t - 1)
  have hct (w : V) : ρ c (ρ t w) = ρ t (ρ c w) := by
    change (ρ c * ρ t) w = (ρ t * ρ c) w
    rw [← map_mul, ← map_mul, hc.eq]
  have hinv (w : V) (hw : w ∈ W) : ρ c w ∈ W := by
    obtain ⟨u, rfl⟩ := hw
    exact ⟨ρ c u, by simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hct]⟩
  let w := ρ t v - v
  have hw : w ∈ W := ⟨v, rfl⟩
  by_cases hw0 : w = 0
  · change ρ c w = w
    simp [hw0]
  have hW : W = Submodule.span (ZMod 2) {w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hr hw hw0
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hW ▸ hinv w hw)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at ha
    exact hw0 ((ρ.apply_bijective c).injective (ha.symm.trans (map_zero _).symm))
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
  simpa only [ha1, one_smul] using ha.symm


/-- A binary rank-one displacement squares to the identity, even if the
representation has a kernel. -/
theorem square_eq_one_of_rank_one (ρ : Representation (ZMod 2) G V) (t : G)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 1) :
    ρ (t ^ 2) = 1 := by
  ext v
  have h := fixes_displacement_of_commute ρ t t hr (Commute.refl t) v
  rw [map_sub, ZModModule.sub_eq_add, ZModModule.sub_eq_add] at h
  have he : ρ t (ρ t v) = v := by
    exact add_right_cancel (h.trans (add_comm _ _))
  simpa only [pow_two, map_mul, Module.End.mul_apply, Module.End.one_apply] using he

/-- Simplicity makes a representation with a nonzero displacement faithful.
Thus faithfulness need not be added to a permutation-module input. -/
theorem faithful_of_rank_one [IsSimpleGroup G]
    (ρ : Representation (ZMod 2) G V) (t : G)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 1) :
    Function.Injective ρ := by
  apply ρ.ker_eq_bot_iff.mp
  rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have he : ρ t = 1 := show t ∈ ρ.ker from ht ▸ Subgroup.mem_top t
    rw [he, sub_self, LinearMap.range_zero, finrank_bot] at hr
    exact (Nat.zero_ne_one hr).elim

/-- A generating equivariant image of a permutation basis has no rank-one
actor whenever its displacement lies in the centralizer relations. -/
theorem finrank_ne_one_of_relations (ρ : Representation (ZMod 2) G V)
    (f : X → V) (hf : ∀ g x, f (g • x) = ρ g (f x))
    (hspan : Submodule.span (ZMod 2) (Set.range f) = ⊤)
    (t : G) (ht : DisplacementRelations (X := X) t) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≠ 1 := by
  intro hr
  let F := Finsupp.linearCombination (ZMod 2) f
  have hR : centralizerRelations (X := X) t ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, c, hc, x, rfl⟩
    change F (relation t h c x) = 0
    simp only [relation, map_add, map_sub, F, Finsupp.linearCombination_single, one_smul, hf]
    rw [← map_sub, ← map_sub, ← map_add, ← map_sub]
    rw [fixes_displacement_of_commute ρ t c hr hc]
    convert map_zero (ρ h) using 1
    congr 1
    abel
  have hfix (x : X) : ρ t (f x) = f x := by
    have hz := hR (ht x)
    change F (Finsupp.single (t • x) 1 - Finsupp.single x 1) = 0 at hz
    simpa only [F, map_sub, Finsupp.linearCombination_single, one_smul, hf,
      sub_eq_zero] using hz
  have htop : (⊤ : Submodule (ZMod 2) V) ≤ (ρ t - 1).ker := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change ρ t (f x) - f x = 0
    exact sub_eq_zero.mpr (hfix x)
  have he : ρ t - 1 = 0 := by
    ext v
    exact htop Submodule.mem_top
  rw [he, LinearMap.range_zero, finrank_bot] at hr
  exact Nat.zero_ne_one hr

end Relations
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.PlanePermutation
