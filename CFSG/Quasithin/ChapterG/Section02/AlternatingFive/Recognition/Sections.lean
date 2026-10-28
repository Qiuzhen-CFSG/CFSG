module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.QuotientImages
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.NaturalLayer
public import Theory.Representation.BinaryConjugationSection.Canonical
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The genuine binary upper section of G.2.4

The canonical starred-kernel equality puts S inside O₂(LT), which normalizes
U. Consequently S normalizes W and Wᵍ. Their cross-commutators lie in
U∩Uᵍ, and their squares lie in V_L by G.2.2. The product decomposition
therefore makes the literal S/S₂ elementary abelian. For any compatible
binary coordinates the original U-action has moved space contained in
the W-image, and fixes that image pointwise.

The earlier structural inputs remain explicit; no recognition or quotient
action witness is used in proving elementary abelianness.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(3–6), printed pp.334–335, using G.2.3 on pp.333–334.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
  (d : Hypothesis D g)
include d

theorem recognition_core_normalizes_U
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2) :
    D.S g ≤ normalizer (D.U : Set G) := by
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  have hc : D.LT.pCoreIn 2 ≤ D.T := hP ▸ pCoreIn_le_sylow D.LT P
  exact (hcore.le.trans inf_le_right).trans (hc.trans ((normal_subgroupOf_iff_le_normalizer d.setup.U_normal_in_T.1).mp
    d.setup.U_normal_in_T.2))

theorem recognition_conjugate_core (hLI : D.L ≤ D.I g) :
    conjugate (D.S g) g = D.S g :=
  mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (D.S g : Set G)).inv_mem (I_normalizes_core D g (hLI d.g_mem)))

theorem recognition_conjugate_W (hLI : D.L ≤ D.I g) :
    conjugate (D.W g) g = conjugate D.U g ⊓ D.S g := by
  change (D.U ⊓ D.S g).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective]
  exact congrArg (conjugate D.U g ⊓ ·) (d.recognition_conjugate_core hLI)

theorem recognition_core_normalizes_W
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2) :
    D.S g ≤ normalizer (D.W g : Set G) :=
  (le_inf (d.recognition_core_normalizes_U hcore) (D.S g).le_normalizer).trans
    inf_normalizer_le_normalizer_inf

theorem recognition_core_normalizes_conjugate_W (hLI : D.L ≤ D.I g)
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2) :
    D.S g ≤ normalizer (conjugate (D.W g) g : Set G) := by
  have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
    (d.recognition_core_normalizes_W hcore)).trans
      ((D.W g).le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
  change conjugate (D.S g) g ≤ normalizer (conjugate (D.W g) g : Set G) at hh
  rwa [d.recognition_conjugate_core hLI] at hh

theorem recognition_square (u : G) (hu : u ∈ D.U) : u ^ 2 ∈ D.V₁ := by
  let : Fact (IsPGroup 2 D.U) := ⟨d.setup.U_isPGroup⟩
  exact d.setup.frattini_U_le_point
    ⟨(⟨u, hu⟩ : D.U) ^ 2, pth_power_mem_frattini_of_isPGroup _, rfl⟩

/-- The actual upper quotient is elementary, before invoking recognition. -/
theorem upper_elementary (hLI : D.L ≤ D.I g)
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2)
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    [((S₂ D g).subgroupOf (D.S g)).Normal] :
    IsElementaryAbelian 2 (UpperQuotient D g) := by
  let q := QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g))
  have hXS : conjugate (D.W g) g ≤ D.S g := by
    rw [d.recognition_conjugate_W hLI]; exact inf_le_right
  have hSW := d.recognition_core_normalizes_W hcore
  have hSX := d.recognition_core_normalizes_conjugate_W hLI hcore
  have hWX : ⁅D.W g, conjugate (D.W g) g⁆ ≤ S₂ D g := by
    have hc := le_inf (le_normalizer_iff_commutator_le_left.mp (hXS.trans hSW))
      (le_normalizer_iff_commutator_le_right.mp
        ((show D.W g ≤ D.S g from inf_le_right).trans hSX))
    exact hc.trans ((inf_le_inf inf_le_left (map_mono inf_le_left)).trans le_sup_right)
  have hsqW : ∀ w ∈ D.W g, w ^ 2 ∈ S₂ D g :=
    fun w hw => (show D.V₁ ≤ S₂ D g from (le_conjugateSpanBy _ _).trans le_sup_left)
      (d.recognition_square w hw.1)
  have hsqX : ∀ x ∈ conjugate (D.W g) g, x ^ 2 ∈ S₂ D g := by
    rintro x ⟨w, hw, rfl⟩
    apply (show D.VL ≤ S₂ D g from le_sup_left)
    have hh := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom
      ((le_conjugateSpanBy D.V₁ D.L) (d.recognition_square w hw.1))
    have he : D.VL.map (MulAut.conj g⁻¹).toMonoidHom = D.VL :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (D.VL : Set G)).inv_mem (L_normalizes_VL D d.g_mem))
    change (MulAut.conj g⁻¹).toMonoidHom (w ^ 2) ∈
      D.VL.map (MulAut.conj g⁻¹).toMonoidHom at hh
    rw [he] at hh
    simpa only [map_pow] using hh
  have hsq : ∀ a : UpperQuotient D g, a ^ 2 = 1 := by
    intro a
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ a
    have hprod : (s : G) ∈ (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (hXS.trans hSW), ← hsplit]
      exact s.property
    obtain ⟨w, hw, x, hx, hwx⟩ := hprod
    let wS : D.S g := ⟨w, hw.2⟩
    let xS : D.S g := ⟨x, hXS hx⟩
    have hs : wS * xS = s := Subtype.ext hwx
    have hqw : (q wS) ^ 2 = 1 := by
      rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).mpr (hsqW w hw)
    have hqx : (q xS) ^ 2 = 1 := by
      rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).mpr (hsqX x hx)
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

/-- The marked root acts quadratically, with the literal W-image between
its moved space and its fixed space. -/
theorem upper_root_bounds (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) (D.I g) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g) ρ)
    (u : D.I g) (hu : (u : G) ∈ D.U) :
    LinearMap.range (ρ u - 1) ≤ c.imageSpace (D.W g) ∧
    ∀ v ∈ c.imageSpace (D.W g), ρ u v = v := by
  have hUS : ⁅D.U, D.S g⁆ ≤ D.W g :=
    le_inf (le_normalizer_iff_commutator_le_left.mp (d.recognition_core_normalizes_U hcore))
      (le_normalizer_iff_commutator_le_right.mp
        ((show D.U ≤ D.I g from le_sup_left).trans (I_normalizes_core D g)))
  have hUW : ⁅D.U, D.W g⁆ ≤ S₂ D g :=
    ((commutator_mono le_rfl (show D.W g ≤ D.U from inf_le_left)).trans
      (derived_le_of_frattini_image_le d.setup.U_isPGroup d.setup.frattini_U_le_point)).trans
        ((le_conjugateSpanBy _ _).trans le_sup_left)
  exact ⟨c.displacement_range_le_imageSpace_of_commutator_le D.U (D.W g) hUS u hu,
    c.fixed_on_imageSpace_of_commutator_le D.U (D.W g) hUW u hu⟩

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
