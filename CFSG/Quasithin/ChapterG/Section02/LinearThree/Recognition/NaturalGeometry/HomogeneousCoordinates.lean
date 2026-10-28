module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.NaturalGeometry.RootAction
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.Coordinates

/-!
# Projective point images in homogeneous natural coordinates

The G.1.3 root clauses determine the point images under any actual equivariant
binary linear equivalence to repeated natural SL₃ modules. At the coordinate
point Fe₀, the transvections t₀₁ and t₀₂ force each component to lie in Fe₀.
Conversely, t₀₁ realizes every tuple in that line as a displacement. Nonzero
vector transitivity and equivariance transport this equality to every point.
No positive multiplicity, dimension of a point image, or fixed-space identity
is assumed. The binary module structure on the natural space is the same one
as in `Projective.Homogeneous`; finite characteristic-two fields supply it.

The consumer applies `naturalPointMap_criterion` and identifies the literal
images of W, Wᵍ and Wʰ in S/S₃ with `ChiefFactors.lineCopies`, preserving the
canonical quotient projection and the source's inverse-action convention for
right conjugates. Earlier structural inputs and the actual homogeneous
isomorphism remain explicit, as required by this conditional helper contract.
The natural-geometry assembly owner retains the three-term direct sum and order
adapters; the recognition owner retains the genuine G.1.3 application.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.1–4, printed pp.327–328, and G.2.5(7), printed pp.335–336.
-/

public section

open Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
variable {F K : Type*} [Field F] [Group K]

private def coordinatePoint : Point F (Fin 3 → F) :=
  ⟨Submodule.span F {Pi.single 0 1}, finrank_span_singleton (by
    intro h
    have := congrFun h 0
    simp at this)⟩

private theorem mem_coordinatePoint (v : Fin 3 → F) :
    v ∈ (coordinatePoint (F := F)).val ↔ ∀ j, j ≠ 0 → v j = 0 := by
  constructor
  · intro hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    intro j hj
    simp [Pi.single_eq_of_ne hj]
  · intro hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v 0, ?_⟩
    ext j
    by_cases hj : j = 0
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj, hv j hj]

private def coordinateAxis (j : Fin 3) : Submodule F (Fin 3 → F) :=
  LinearMap.ker (LinearMap.proj j)

private theorem coordinateAxis_dimension (j : Fin 3) :
    Module.finrank F (coordinateAxis (F := F) j) + 1 =
      Module.finrank F (Fin 3 → F) := by
  apply Module.Dual.finrank_ker_add_one_of_ne_zero
  intro he
  have := LinearMap.congr_fun he (Pi.single j 1)
  simp at this

private theorem coordinatePoint_le_axis (j : Fin 3) (hj : j ≠ 0) :
    (coordinatePoint (F := F)).val ≤ coordinateAxis j := by
  intro v hv
  exact (mem_coordinatePoint v).mp hv j hj

private def coordinateRoot (μ : K ≃* SpecialLinearGroup (Fin 3) F)
    (j : Fin 3) (hj : j ≠ 0) : K :=
  μ.symm (SpecialLinearGroup.transvection hj.symm (1 : F))

private theorem coordinateRoot_action (μ : K ≃* SpecialLinearGroup (Fin 3) F)
    (j : Fin 3) (hj : j ≠ 0) (v : Fin 3 → F) :
    (Representation.specialLinearNatural 3).comp μ.toMonoidHom
      (coordinateRoot μ j hj) v = v + Pi.single 0 (v j) := by
  change (μ (μ.symm _)).val.mulVec v = _
  rw [μ.apply_symm_apply]
  simp [SpecialLinearGroup.transvection_coe, add_mulVec, single_mulVec_eq, ← Pi.single_smul]

private theorem coordinateRoot_mem (μ : K ≃* SpecialLinearGroup (Fin 3) F)
    (j : Fin 3) (hj : j ≠ 0) :
    coordinateRoot μ j hj ∈ rootGroup ((Representation.specialLinearNatural 3).comp
      μ.toMonoidHom) (coordinatePoint (F := F)).val (coordinateAxis j) := by
  constructor
  · intro v
    rw [coordinateRoot_action, add_sub_cancel_left]
    apply (mem_coordinatePoint _).mpr
    intro k hk
    simp [Pi.single_eq_of_ne hk]
  · intro v hv
    change v j = 0 at hv
    rw [coordinateRoot_action, hv]
    simp

variable [Module (ZMod 2) (Fin 3 → F)] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (μ : K ≃* SpecialLinearGroup (Fin 3) F)
    (ρ : Representation (ZMod 2) K M)
    (φ : Point F (Fin 3 → F) → Submodule (ZMod 2) M)
    (hc : Criterion ((Representation.specialLinearNatural 3).comp μ.toMonoidHom) ρ φ)
    {r : ℕ} (e : M ≃ₗ[ZMod 2] (Fin r → Fin 3 → F))
    (he : ∀ k v i, e (ρ k v) i =
      (Representation.specialLinearNatural 3).comp μ.toMonoidHom k (e v i))

include hc he in
private theorem coordinatePoint_correspondence (v : M) :
    v ∈ φ (coordinatePoint (F := F)) ↔
      ∀ i, e v i ∈ (coordinatePoint (F := F)).val := by
  constructor
  · intro hv i
    apply (mem_coordinatePoint _).mpr
    intro j hj
    have hf := hc.root_fixed coordinatePoint (coordinateAxis j)
      (coordinateAxis_dimension j) (coordinatePoint_le_axis j hj)
      coordinatePoint (coordinatePoint_le_axis j hj)
      (coordinateRoot μ j hj) (coordinateRoot_mem μ j hj) v hv
    have hh := congrArg (fun w => e w i) hf
    rw [he, coordinateRoot_action] at hh
    have hh0 := congrFun hh 0
    simpa using hh0
  · intro hv
    let w : M := e.symm (fun i => Pi.single 1 (e v i 0))
    have hw := hc.root_moved coordinatePoint (coordinateAxis 1)
      (coordinateAxis_dimension 1) (coordinatePoint_le_axis 1 (by decide))
      (coordinateRoot μ 1 (by decide)) (coordinateRoot_mem μ 1 (by decide)) w
    have hd : ρ (coordinateRoot μ 1 (by decide)) w - w = v := by
      apply e.injective
      ext i j
      rw [map_sub]
      change (e (ρ (coordinateRoot μ 1 (by decide)) w) i - e w i) j = e v i j
      rw [he, coordinateRoot_action, add_sub_cancel_left]
      have hew : e w = fun i => Pi.single 1 (e v i 0) := e.apply_symm_apply _
      rw [hew]
      by_cases hj : j = 0
      · subst j; simp
      · simp [Pi.single_eq_of_ne hj, (mem_coordinatePoint _).mp (hv i) j hj]
    exact hd ▸ hw

omit [Module (ZMod 2) (Fin 3 → F)] in
private theorem coordinatePoint_transitive (A : Point F (Fin 3 → F)) :
    ∃ k : K, (coordinatePoint (F := F)).val.map
      (((Representation.specialLinearNatural 3).comp μ.toMonoidHom) k) = A.val := by
  obtain ⟨v, hv, hv0⟩ := A.val.ne_bot_iff.mp
    (Submodule.isAtom_iff_finrank_eq_one.mpr A.property).ne_bot
  obtain ⟨a, ha⟩ := SpecialLinearGroup.exists_mulVec_eq_three
    (Pi.single 0 1) v (by intro he; have := congrFun he 0; simp at this) hv0
  refine ⟨μ.symm a, ?_⟩
  change (Submodule.span F {Pi.single 0 1}).map _ = _
  rw [eq_span_singleton_of_mem_of_finrank_eq_one A.property hv hv0,
    Submodule.map_span]
  simp only [Set.image_singleton]
  change Submodule.span F {((μ (μ.symm a)).val.mulVec (Pi.single 0 1))} = _
  rw [μ.apply_symm_apply, ha]

include hc he in
/-- The root conditions determine every point image in any equivariant
homogeneous natural realization, including multiplicity zero. -/
theorem Criterion.mem_iff_homogeneous_coordinates (A : Point F (Fin 3 → F)) (v : M) :
    v ∈ φ A ↔ ∀ i, e v i ∈ A.val := by
  let γ : Representation F K (Fin 3 → F) :=
    (Representation.specialLinearNatural 3).comp μ.toMonoidHom
  obtain ⟨k, hk⟩ := coordinatePoint_transitive μ A
  have hφ := hc.equivariant k coordinatePoint A hk.symm
  rw [hφ]
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    rw [he, ← hk]
    exact ⟨e w i, (coordinatePoint_correspondence μ ρ φ hc e he w).mp hw i, rfl⟩
  · intro hv
    refine ⟨ρ k⁻¹ v, ?_, ρ.self_inv_apply k v⟩
    apply (coordinatePoint_correspondence μ ρ φ hc e he _).mpr
    intro i
    have hi := hv i
    rw [← hk] at hi
    obtain ⟨w, hw, hwi⟩ := hi
    rw [he, ← hwi]
    change γ k⁻¹ (γ k w) ∈ (coordinatePoint (F := F)).val
    rw [γ.inv_self_apply]
    exact hw

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
open Subgroup Projective Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] [Module (ZMod 2) (Fin 3 → F)]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {hLI : D.L ≤ I D g h} (comparison : StarComparison D g h hLI)
  (σ : Representation (ZMod 2) (D.star D.L) M)
  (s : Representation.BinaryConjugationSection (I D g h) (S D g h) (S₃ D g h)
    (σ.comp comparison.projection))
  (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
  (hU : S D g h ≤ normalizer (D.U : Set G))
  (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h)
  (hrad : UpperRadicalIdentification d comparison)
  {r : ℕ} (e : M ≃ₗ[ZMod 2] (Fin r → Fin 3 → F))
  (he : ∀ k v i, e (σ k v) i = naturalAction d k (e v i))

include hUT hf hU hgen hrad he in
/-- Apply rigidity to the projective point map constructed from W. The
remaining structural inputs are those of the already proved criterion. -/
theorem naturalPointMap_mem_iff_homogeneous_coordinates
    (A : Point F (Fin 3 → F)) (v : M) :
    v ∈ naturalPointMap d comparison σ s A ↔ ∀ i, e v i ∈ A.val := by
  exact Criterion.mem_iff_homogeneous_coordinates d.model σ
    (naturalPointMap d comparison σ s)
    (naturalPointMap_criterion d comparison σ s hUT hf hU hgen hrad) e he A v

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Subgroup
variable {G : Type*} [Group G] {D : Setup G} {g h : G}
  [((S₃ D g h).subgroupOf (S D g h)).Normal]
  [IsElementaryAbelian 2 (UpperQuotient D g h)]
  {F : Type*} [Field F] [Module (ZMod 2) (Fin 3 → F)]
  {hLI : D.L ≤ I D g h} (comparison : StarComparison D g h hLI)
  (σ : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g h)))
  (s : Representation.BinaryConjugationSection (I D g h) (S D g h) (S₃ D g h)
    (σ.comp comparison.projection))
  (hq : ∀ a : S D g h, (s.coordinates a).toAdd =
    Additive.ofMul (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) a))
  {r : ℕ} (e : Additive (UpperQuotient D g h) ≃ₗ[ZMod 2] (Fin r → Fin 3 → F))

include hq in
private theorem canonical_upperImage_coordinates (A : Subgroup G)
    (P : Submodule F (Fin 3 → F))
    (hP : ∀ v, v ∈ SectionGeometry.image s A ↔ ∀ i, e v i ∈ P) :
    (upperImage D g h A).map e.toAddEquiv.toMultiplicativeRight.toMonoidHom =
      ChiefFactors.lineCopies P r := by
  ext v
  constructor
  · rintro ⟨q, hqA, rfl⟩
    apply (hP (Additive.ofMul q)).mp
    obtain ⟨a, ha, haq⟩ := hqA
    apply (SectionGeometry.mem_image s A _).mpr
    exact ⟨a, ha, (hq a).trans (congrArg Additive.ofMul haq)⟩
  · intro hv
    let q : UpperQuotient D g h := (e.symm v.toAdd).toMul
    have hm : Additive.ofMul q ∈ SectionGeometry.image s A := by
      apply (hP _).mpr
      change ∀ i, e (e.symm v.toAdd) i ∈ P
      rw [e.apply_symm_apply]
      exact hv
    obtain ⟨a, ha, haq⟩ := (SectionGeometry.mem_image s A _).mp hm
    refine ⟨q, ?_, ?_⟩
    · refine ⟨a, ha, ?_⟩
      exact Additive.ofMul.injective ((hq a).symm.trans haq)
    · change Multiplicative.ofAdd (e (e.symm v.toAdd)) = v
      simp

namespace Hypothesis
open Projective Setup
variable [Finite G] [Finite F] {n : ℕ} (d : LinearThree.Hypothesis D F n g h)
  (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
  (hU : S D g h ≤ normalizer (D.U : Set G))
  (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h)
  (hrad : UpperRadicalIdentification d comparison)
  (he : ∀ k v i, e (σ k v) i = naturalAction d k (e v i))

include hUT hf hU hgen hrad he hq in
/-- Literal quotient images of W and all its L-conjugates are the copies
of the original marked point and its inverse-action conjugate points.
The equation for s retains the canonical projection S → S/S₃. -/
theorem upperImage_homogeneous_coordinates :
    (upperImage D g h (W D g h)).map e.toAddEquiv.toMultiplicativeRight.toMonoidHom =
      ChiefFactors.lineCopies d.point r ∧
    ∀ l : D.L, (upperImage D g h (conjugate (W D g h) l)).map
      e.toAddEquiv.toMultiplicativeRight.toMonoidHom =
        ChiefFactors.lineCopies (conjugatePoint d l).val r := by
  constructor
  · apply canonical_upperImage_coordinates comparison σ s hq e
    intro v
    rw [← naturalPointMap_mark d comparison σ s]
    exact naturalPointMap_mem_iff_homogeneous_coordinates d comparison σ s
      hUT hf hU hgen hrad e he (naturalPoint d) v
  · intro l
    apply canonical_upperImage_coordinates comparison σ s hq e
    intro v
    rw [← naturalPointMap_conjugate d comparison σ s l]
    exact naturalPointMap_mem_iff_homogeneous_coordinates d comparison σ s
      hUT hf hU hgen hrad e he (conjugatePoint d l) v

include hUT hf hU hgen hrad he hq in
/-- The three original G.2.5(7) marks, at W, Wᵍ and Wʰ. -/
theorem upperImage_three_homogeneous_coordinates :
    (upperImage D g h (W D g h)).map e.toAddEquiv.toMultiplicativeRight.toMonoidHom =
      ChiefFactors.lineCopies d.point r ∧
    (upperImage D g h (conjugate (W D g h) g)).map
      e.toAddEquiv.toMultiplicativeRight.toMonoidHom =
        ChiefFactors.lineCopies (conjugatePoint d ⟨g, d.g_mem⟩).val r ∧
    (upperImage D g h (conjugate (W D g h) h)).map
      e.toAddEquiv.toMultiplicativeRight.toMonoidHom =
        ChiefFactors.lineCopies (conjugatePoint d ⟨h, d.h_mem⟩).val r := by
  obtain ⟨hW, hconj⟩ := upperImage_homogeneous_coordinates comparison σ s hq e d
    hUT hf hU hgen hrad he
  exact ⟨hW, hconj ⟨g, d.g_mem⟩, hconj ⟨h, d.h_mem⟩⟩

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
