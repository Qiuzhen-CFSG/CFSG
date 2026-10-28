module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.Filtration

/-!
# Restriction of the actual natural upper section to L₁

When I=L, the two-core S centralizes the point and normalizes its two-residual
L₁. A cubic element of the marked local image acts freely on S/S₂. Its
commutator map proves that S∩L₁ maps onto S/S₂. Thus intersecting the upper
section loses no vectors. The resulting quotient isomorphism intertwines the
literal L₁ conjugation and carries exactly the original NaturalLayer coordinates.

This is the transport needed before restricting each natural SL₂(4) plane to
the Borel. It does not identify the orthogonal lower module with that plane.

Source: Aschbacher–Smith, 13.5.22, printed p.924 (PDF p.941), and G.2.4(6).
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement Matrix
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- S lies in the normalizer of the actual O²(N_L(V₁)). -/
theorem core_normalizes_residual (d : Hypothesis D g) (hgen : D.I g = D.L) :
    D.S g ≤ normalizer (D.L₁ : Set G) := by
  have hSL : D.S g ≤ D.L := (pCoreIn_le 2 (D.I g)).trans hgen.le
  have hSC : D.S g ≤ centralizer (D.VL : Set G) :=
    le_centralizer_iff.mp ((d.central_first d.L_le_I).trans inf_le_right)
  have hSG : D.S g ≤ D.G₁ :=
    (hSC.trans (centralizer_le (le_conjugateSpanBy D.V₁ D.L))).trans
      (Subgroup.centralizer_le_normalizer _)
  exact (le_inf hSL hSG).trans (le_normalizer_embedded_pResidual 2 (D.L ⊓ D.G₁))

/-- The commutators used to lift the natural quotient lie in the actual L₁. -/
theorem core_commutator_le_residual (d : Hypothesis D g) (hgen : D.I g = D.L) :
    ⁅D.S g, D.L₁⁆ ≤ D.L₁ :=
  le_normalizer_iff_commutator_le_right.mp (core_normalizes_residual d hgen)

variable (d : Hypothesis D g) [((AlternatingFive.S₂ D g).subgroupOf (D.S g)).Normal]

/-- Inclusion of S∩L₁ into S, retaining the original ambient representative. -/
def coreRepresentative : (core d).val →* D.S g where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Restrict the original quotient map S→S/S₂ to S∩L₁. -/
def upperHom : (core d).val →* UpperQuotient D g :=
  (QuotientGroup.mk' ((AlternatingFive.S₂ D g).subgroupOf (D.S g))).comp
    (coreRepresentative d)

/-- The denominator of this restriction is exactly S₂∩L₁. -/
theorem upperHom_kernel :
    (upperHom d).ker = (second d).val.subgroupOf (core d).val := by
  ext x
  exact QuotientGroup.eq_one_iff (coreRepresentative d x)

/-- Every upper vector lifts to S∩L₁; no dimension is lost on restriction. -/
theorem upperHom_surjective (hgen : D.I g = D.L)
    {F : Type*} [Field F] {s : ℕ} (c : NaturalLayer D g F s d.L_le_I) :
    Function.Surjective (upperHom d) := by
  obtain ⟨t, htL, ht⟩ := d.terminal_exists_local_cubic_star d.earlierStructure
  intro x
  let q := QuotientGroup.mk' ((AlternatingFive.S₂ D g).subgroupOf (D.S g))
  let tI : D.I g := ⟨t, d.L_le_I t.property⟩
  obtain ⟨y, hy⟩ := (c.cubic_fixedPointFree t ht).commutatorMap_surjective x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ y
  change q z / c.action tI (q z) = x at hy
  rw [c.action_mk, ← map_div] at hy
  let w : D.S g := z / coreConjugate D g tI z
  have hw : (w : G) ∈ D.L₁ := by
    apply core_commutator_le_residual d hgen
    have he : (w : G) = ⁅(z : G), (t : G)⁆ := by
      dsimp [w, coreConjugate, tI]
      simp only [commutatorElement_def, div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
      group
    rw [he]
    exact commutator_mem_commutator z.property htL
  exact ⟨⟨⟨w, hw⟩, w.property⟩, hy⟩

/-- The isomorphism is induced by the inclusion and the original quotient map. -/
noncomputable def upperSectionEquiv (hgen : D.I g = D.L)
    {F : Type*} [Field F] {s : ℕ} (c : NaturalLayer D g F s d.L_le_I) :
    Section (second d) (core d) ≃* UpperQuotient D g :=
  (QuotientGroup.quotientMulEquivOfEq (upperHom_kernel d).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (upperHom d)
      (upperHom_surjective d hgen c))

@[simp] theorem upperSectionEquiv_mk (hgen : D.I g = D.L)
    {F : Type*} [Field F] {s : ℕ} (c : NaturalLayer D g F s d.L_le_I)
    (x : (core d).val) :
    upperSectionEquiv d hgen c (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (coreRepresentative d x) := rfl

/-- Equivariance is checked on representatives of the literal relative quotient. -/
theorem upperSectionEquiv_equivariant (hgen : D.I g = D.L)
    {F : Type*} [Field F] {s : ℕ} (c : NaturalLayer D g F s d.L_le_I)
    (k : D.L₁) (x : Section (second d) (core d)) :
    upperSectionEquiv d hgen c (sectionAction (second d) (core d) k x) =
      c.action ⟨k, ((residual_le_L D).trans d.L_le_I) k.property⟩
        (upperSectionEquiv d hgen c x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [sectionAction_mk, upperSectionEquiv_mk, upperSectionEquiv_mk, c.action_mk]
  rfl

/-- Natural coordinates on the restricted quotient, with the SAME multiplicity s. -/
noncomputable def upperCoordinates (hgen : D.I g = D.L)
    {F : Type*} [Field F] {s : ℕ} (c : NaturalLayer D g F s d.L_le_I) :
    Section (second d) (core d) ≃* Multiplicative (Fin s → Fin 2 → F) :=
  (upperSectionEquiv d hgen c).trans c.coordinates

/-- Restriction keeps the original star marking and matrix action. -/
theorem upperCoordinates_equivariant (hgen : D.I g = D.L)
    {F : Type*} [Field F] {s : ℕ} (c : NaturalLayer D g F s d.L_le_I)
    (k : D.L₁) (x : Section (second d) (core d)) :
    (upperCoordinates d hgen c (sectionAction (second d) (core d) k x)).toAdd =
      fun j => (c.model (starProjection D (inclusion (residual_le_L D) k))).val *ᵥ
        (upperCoordinates d hgen c x).toAdd j := by
  change (c.coordinates (upperSectionEquiv d hgen c
    (sectionAction (second d) (core d) k x))).toAdd = _
  rw [upperSectionEquiv_equivariant]
  exact c.equivariant (inclusion (residual_le_L D) k) (upperSectionEquiv d hgen c x)

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
