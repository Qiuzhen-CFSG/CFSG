module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Layers
public import Theory.Representation.BinaryConjugationSection.Canonical
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# The actual quadratic section in G.2.6

From the core product and normalization of U by S, the two marked
factors commute modulo S₂. Their squares lie in the marked points and
therefore in V_L ≤ S₂. This constructs an elementary abelian quotient.
Its canonical conjugation action descends through I/O₂(I); the coordinates
are the original quotient projection. Finally the source commutator
bounds give the quadratic identity for all pairs of elements of U.

This adapts the square calculation in Section02/Binary/Quotient to the
larger denominator V_L(U ∩ Uᵍ). No containment S₂ ≤ W is used.
Source: Aschbacher–Smith, G.2.6, printed p.336.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
variable {G : Type*} [Group G]

/-- G.2.2's Frattini conclusion bounds every square in U. -/
theorem square_mem_point [Finite G] {D : Setup G}
    (h : D.BaseHypothesis) (hc : ClosureConclusions D) (u : G) (hu : u ∈ D.U) :
    u ^ 2 ∈ D.V₁ := by
  let : Fact (IsPGroup 2 D.U) := ⟨U_isPGroup h hc⟩
  exact hc.frattini (mem_map_of_mem D.U.subtype
    (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u, hu⟩ : D.U)))

/-- The elementary binary structure is proved on the literal quotient.
Only the structural core identity, not module recognition, is an input. -/
theorem quotient_elementary [Finite G] {D : Setup G} {g : G}
    (h : D.BaseHypothesis) (hc : ClosureConclusions D)
    (hgL : g ∈ D.L) (hgI : g ∈ D.I g)
    (hEN : D.I g ≤ normalizer (S₂ D g : Set G))
    (hSU : D.S g ≤ normalizer (D.U : Set G))
    (hsplit : D.S g = coreProduct D g) :
    letI : ((S₂ D g).subgroupOf (D.S g)).Normal :=
      normal_subgroupOf_of_le_normalizer ((pCoreIn_le 2 (D.I g)).trans hEN)
    IsElementaryAbelian 2 (Quotient D g) := by
  let S := D.S g
  let N := (S₂ D g).subgroupOf S
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 (D.I g)).trans hEN)
  change IsElementaryAbelian 2 (S ⧸ N)
  let q := QuotientGroup.mk' N
  have hWS : D.W g ≤ S := inf_le_right
  have hXS : conjugate (D.W g) g ≤ S := by
    rw [conjugate_W D g hgI]
    exact inf_le_right
  obtain ⟨hSW, hSX⟩ := core_normalizes_marks hgI hSU
  have hWX : ⁅D.W g, conjugate (D.W g) g⁆ ≤ S₂ D g := by
    apply le_trans _ (show D.S₂ g ≤ S₂ D g from le_sup_right)
    exact le_inf
      ((le_normalizer_iff_commutator_le_left.mp (hXS.trans hSW)).trans inf_le_left)
      ((le_normalizer_iff_commutator_le_right.mp (hWS.trans hSX)).trans
        (map_mono (show D.W g ≤ D.U from inf_le_left)))
  have hsqW : ∀ w ∈ D.W g, w ^ 2 ∈ S₂ D g :=
    fun w hw => mem_sup_left ((point_le_VL D) (square_mem_point h hc w hw.1))
  have hsqX : ∀ x ∈ conjugate (D.W g) g, x ^ 2 ∈ S₂ D g := by
    rintro x ⟨w, hw, rfl⟩
    apply mem_sup_left
    have hh := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom
      ((point_le_VL D) (square_mem_point h hc w hw.1))
    have he : D.VL.map (MulAut.conj g⁻¹).toMonoidHom = D.VL :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (D.VL : Set G)).inv_mem (L_normalizes_VL D hgL))
    rw [he] at hh
    simpa only [map_pow] using hh
  have hsq : ∀ a : S ⧸ N, a ^ 2 = 1 := by
    intro a
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N a
    have hprod : (s : G) ∈ (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
      rw [← coreProduct_product hgI hSU, ← hsplit]
      exact s.property
    obtain ⟨w, hw, x, hx, hwx⟩ := hprod
    let wS : S := ⟨w, hWS hw⟩
    let xS : S := ⟨x, hXS hx⟩
    have hs : wS * xS = s := Subtype.ext hwx
    have hqw : (q wS) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsqW w hw)
    have hqx : (q xS) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsqX x hx)
    have hqcomm : Commute (q wS) (q xS) := by
      change q wS * q xS = q xS * q wS
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hWX (commutator_mem_commutator hw hx))
    change (q s) ^ 2 = 1
    rw [← hs, map_mul, hqcomm.mul_pow, hqw, hqx, mul_one]
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsq x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }

/-- Construct the action of the actual quotient I/O₂(I), with its
original projection onto the elementary section S/S₂. -/
theorem exists_quotient_representation {D : Setup G} {g : G}
    (hES : S₂ D g ≤ D.S g) (hEN : D.I g ≤ normalizer (S₂ D g : Set G))
    [((S₂ D g).subgroupOf (D.S g)).Normal] [IsElementaryAbelian 2 (Quotient D g)] :
    ∃ (σ : Representation (ZMod 2) ((D.I g) ⧸ pCore 2 (D.I g))
        (Additive (Quotient D g)))
      (d : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
        (σ.comp (QuotientGroup.mk' (pCore 2 (D.I g))))),
      ∀ s : D.S g, (d.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) s) := by
  apply Representation.BinaryConjugationSection.exists_canonical
    (D.I g) (D.S g) (S₂ D g) (pCoreIn_le 2 (D.I g)) hES
    (core_normalized D g) hEN (QuotientGroup.mk' (pCore 2 (D.I g)))
    (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  exact ((pCore 2 (D.I g)).comap_map_eq_self_of_injective (D.I g).subtype_injective).symm

/-- Every U-displacement lies in the image of W, and every element of U
fixes that image. This is quadraticity for the whole U-action, including
the mixed identities involving its two factor involutions. -/
theorem quotient_quadratic [Finite G] {D : Setup G} {g : G}
    (h : D.BaseHypothesis) (hc : ClosureConclusions D)
    (hSU : D.S g ≤ normalizer (D.U : Set G))
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) (D.I g) M)
    (d : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g) ρ) :
    (∀ u : D.I g, (u : G) ∈ D.U →
      LinearMap.range (ρ u - 1) ≤ d.imageSpace (D.W g)) ∧
    (∀ u : D.I g, (u : G) ∈ D.U → ∀ v ∈ d.imageSpace (D.W g), ρ u v = v) ∧
    (∀ u v : D.I g, (u : G) ∈ D.U → (v : G) ∈ D.U →
      (ρ u - 1) * (ρ v - 1) = 0) := by
  have hUS : ⁅D.U, D.S g⁆ ≤ D.W g := by
    rw [commutator_comm]
    exact core_commutator_U hSU
  have hUW : ⁅D.U, D.W g⁆ ≤ S₂ D g :=
    ((commutator_mono le_rfl (show D.W g ≤ D.U from inf_le_left)).trans
      (derived_le_point h hc)).trans ((point_le_VL D).trans le_sup_left)
  have hr := d.displacement_range_le_imageSpace_of_commutator_le D.U (D.W g) hUS
  have hf := d.fixed_on_imageSpace_of_commutator_le D.U (D.W g) hUW
  refine ⟨hr, hf, ?_⟩
  intro u v hu hv
  ext m
  change ρ u ((ρ v - 1) m) - (ρ v - 1) m = 0
  exact sub_eq_zero.mpr (hf u hu _ (hr v hv ⟨m, rfl⟩))

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
