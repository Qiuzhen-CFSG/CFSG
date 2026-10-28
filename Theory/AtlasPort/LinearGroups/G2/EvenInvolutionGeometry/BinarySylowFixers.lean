module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Binary
public import Theory.GroupAction.SylowPointwiseInner
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.RootElements

/-!
# Sylow fixers on the actual derived G₂(2)

A conjugating element of the full G₂(2) that centralizes the derived Sylow
subgroup lies in the full unipotent subgroup, by its known normalizer.
Commutation with B(1), E(1), and D(1)F(1) then forces the derived-group parity
condition. Thus every ambient Sylow fixer is induced by an element of the
derived Sylow itself. Conjugacy transports the result to all its Sylow subgroups.

Under the explicit binary automorphism-coverage hypothesis, this proves
innerness for arbitrary pointwise fixers, hence arbitrary two-elements.
Injectivity of that action supplies the square equation for an involutory
fixer's inducing element; the binary Sylow-center calculation makes it long-root.
The initial conjugating element is allowed outside the derived subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 16.1.4(1)
and 16.1.6, printed pp.1171–1172. Root coordinates are from the licensed ATLAS
port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. The small finite
coordinate test is kernel checked.
-/

public section

open Subgroup
namespace Atlas.G2.EvenInvolutionGeometry
open LieParabolicSetup LieAutomorphismExtensions BinaryParabolicPair
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The actual derived-group membership test in the positive-root coordinates. -/
theorem binary_unipotent_mem_derived (t : Fin 6 → ZMod 2) :
    unipotentProduct t ∈ BinaryDerived ↔ t 2 + t 3 + t 5 = 0 := by
  rw [binaryDerived_eq, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (unipotentProduct t) = 1 ↔ _
  simp only [unipotentProduct, map_mul, BinaryException.project_A,
    BinaryException.project_B, BinaryException.project_E, one_mul, mul_one,
    BinaryException.project_C_eq_D, BinaryException.project_D_eq_F]
  rw [← map_mul, ← map_mul, rootF_add, rootF_add]
  have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases hb (t 2 + t 3 + t 5) with h | h
  · simp [h, rootF_zero]
  · rw [h]
    exact iff_of_false quotientBit_ne_one (by decide)

private theorem binary_centralizer_parameters : ∀ t : Fin 6 → ZMod 2,
    unipotentProductParameters ![0,1,0,0,0,0] t =
      unipotentProductParameters t ![0,1,0,0,0,0] →
    unipotentProductParameters ![0,0,0,0,1,0] t =
      unipotentProductParameters t ![0,0,0,0,1,0] →
    unipotentProductParameters ![0,0,0,1,0,1] t =
      unipotentProductParameters t ![0,0,0,1,0,1] →
    t 2 + t 3 + t 5 = 0 := by
  decide +kernel

/-- The ambient centralizer of the derived Sylow subgroup lies in that subgroup. -/
theorem binary_centralizer_derivedSylowAmbient_le :
    centralizer (derivedSylowAmbient : Set (Model (ZMod 2))) ≤ derivedSylowAmbient := by
  intro g hg
  have hU : g ∈ unipotent := by
    rw [← DerivedNormalizerSolvable.binary_normalizer_derivedSylowAmbient]
    exact centralizer_le_normalizer _ hg
  refine ⟨hU,?_⟩
  rw [unipotent_eq_range] at hU
  obtain ⟨t,rfl⟩ := hU
  apply (binary_unipotent_mem_derived t).mpr
  have hc (u : Fin 6 → ZMod 2) (hu : u 2 + u 3 + u 5 = 0) :
      unipotentProductParameters u t = unipotentProductParameters t u := by
    apply unipotentProduct_injective
    rw [← unipotentProduct_mul, ← unipotentProduct_mul]
    exact mem_centralizer_iff.mp hg _
      ⟨unipotentProduct_mem _, (binary_unipotent_mem_derived _).mpr hu⟩
  exact binary_centralizer_parameters t
    (hc _ (by decide)) (hc _ (by decide)) (hc _ (by decide))

/-- Standard derived Sylow fixers are inner, even if initially induced from the full group. -/
theorem binary_fixing_standard_sylow_inner
    (hcover : Function.Surjective binaryConjugation)
    (r : MulAut BinaryDerived) (hr : ∀ x ∈ derivedSylow, r x = x) :
    ∃ x ∈ derivedSylow, r = MulAut.conj x := by
  obtain ⟨g,rfl⟩ := hcover r
  have hc : g ∈ centralizer (derivedSylowAmbient : Set (Model (ZMod 2))) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    rw [← derivedSylow_map_subtype] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    have h := congrArg Subtype.val (hr x hx)
    change g * x.val * g⁻¹ = x.val at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hg := binary_centralizer_derivedSylowAmbient_le hc
  rw [← derivedSylow_map_subtype] at hg
  obtain ⟨x,hx,rfl⟩ := hg
  exact ⟨x,hx,binaryConjugation_inner x⟩

/-- Arbitrary derived Sylow fixers are inner, including all two-power automorphisms. -/
theorem binary_fixing_sylow_inner
    (hcover : Function.Bijective binaryConjugation)
    (S : Sylow 2 BinaryDerived) (r : MulAut BinaryDerived)
    (hr : ∀ x ∈ S, r x = x) : ∃ x ∈ S, r = MulAut.conj x :=
  MulAut.fixing_inner_sylow derivedSylow S
    (binary_fixing_standard_sylow_inner hcover.2) r hr

/-- An involutory fixer on the derived group is induced by an actual long root. -/
theorem binary_fixing_sylow_involution_longRoot
    (hcover : Function.Bijective binaryConjugation)
    (S : Sylow 2 BinaryDerived) (r : MulAut BinaryDerived)
    (hr : ∀ x ∈ S, r x = x) (hsq : r ^ 2 = 1) (hne : r ≠ 1) :
    ∃ x ∈ S, r = MulAut.conj x ∧ IsLongRootElement x.val := by
  obtain ⟨x,hx,he⟩ := binary_fixing_sylow_inner hcover S r hr
  refine ⟨x,hx,he,binary_central_involution_isLongRoot S hx ?_ ?_ ?_⟩
  · apply Subtype.ext
    apply hcover.1
    change binaryConjugation (x.val ^ 2) = binaryConjugation 1
    rw [map_pow, binaryConjugation_inner, ← he, hsq, map_one]
  · intro y hy
    have h := hr y hy
    rw [he, MulAut.conj_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · intro hxone
    apply hne
    rw [he, hxone, map_one]

end Atlas.G2.EvenInvolutionGeometry
