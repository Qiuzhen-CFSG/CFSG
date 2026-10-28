module
public import Theory.Representation.BinaryPermutation
public import Mathlib.RepresentationTheory.Intertwining
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Binary permutation quotients of conjugate spans

An equivariant finite family of vectors extends linearly to a map from
its permutation module. If the family spans, this map is surjective.
For an elementary abelian conjugate span, the original conjugacy orbit
supplies that family with its literal conjugation action. Orbit-stabilizer
counts its permutation basis, and surjectivity bounds the binary dimension.

This gives the permutation-module input used by Aschbacher--Smith,
14.3.29, printed p.1002, before the Fano-module calculation in H.5.3,
printed p.386. It does not classify the resulting quotient.
-/

@[expose] public noncomputable section
namespace BinaryPermutation
open Representation
variable {A Ω M : Type*} [Group A] [Fintype Ω] [AddCommGroup M] [Module (ZMod 2) M]

noncomputable local instance : DecidableEq Ω := Classical.decEq _

def orbitSum (v : Ω → M) : Full Ω →ₗ[ZMod 2] M where
  toFun c := ∑ i, c i • v i
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c d := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem orbitSum_single (v : Ω → M) (i : Ω) : orbitSum v (Pi.single i 1) = v i := by
  classical
  simp [orbitSum, Pi.single_apply]

def orbitQuotient (ρ : Representation (ZMod 2) A M) (α : A →* Equiv.Perm Ω)
    (v : Ω → M) (hv : ∀ a i, v (α a i) = ρ a (v i)) :
    Representation.IntertwiningMap ((representation Ω).comp α) ρ :=
  ⟨orbitSum v, by
    intro a
    apply LinearMap.ext
    intro c
    change (∑ i, c ((α a).symm i) • v i) = ρ a (∑ i, c i • v i)
    rw [← Equiv.sum_comp (α a) (fun i => c ((α a).symm i) • v i)]
    simp only [Equiv.symm_apply_apply, hv, map_sum, map_smul]⟩

theorem orbitQuotient_surjective (ρ : Representation (ZMod 2) A M)
    (α : A →* Equiv.Perm Ω) (v : Ω → M) (hv : ∀ a i, v (α a i) = ρ a (v i))
    (hspan : Submodule.span (ZMod 2) (Set.range v) = ⊤) :
    Function.Surjective (orbitQuotient ρ α v hv) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨Pi.single i 1, orbitSum_single v i⟩

end BinaryPermutation


namespace Representation.BinaryConjugacyOrbit
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

local instance ambientAction (A : Subgroup G) : MulAction A G :=
  MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp A.subtype)

abbrev Orbit (A : Subgroup G) (e : G) := ↥(MulAction.orbit A e)

instance [Finite G] (A : Subgroup G) (e : G) : Fintype (Orbit A e) := Fintype.ofFinite _

def permutation (A : Subgroup G) (e : G) : A →* Equiv.Perm (Orbit A e) :=
  MulAction.toPermHom A (Orbit A e)

theorem mem_orbit (A : Subgroup G) (e x : G) :
    x ∈ MulAction.orbit A e ↔ ∃ a ∈ A, a * e * a⁻¹ = x := by
  rw [MulAction.mem_orbit_iff]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, a.property, ha⟩, fun ⟨a, ha, hx⟩ => ⟨⟨a, ha⟩, hx⟩⟩

theorem orbit_card (A : Subgroup G) (e : G) :
    Nat.card (Orbit A e) = (centralizer ({e} : Set G)).relIndex A := by
  have hs : MulAction.stabilizer A e = (centralizer ({e} : Set G)).subgroupOf A := by
    ext a
    simp only [MulAction.mem_stabilizer_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
    change (a : G) * e * (a : G)⁻¹ = e ↔ (a : G) * e = e * (a : G)
    exact mul_inv_eq_iff_eq_mul
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer A e), ← index_eq_card, hs]
  rfl

abbrev Span (A : Subgroup G) (e : G) := conjugateSpanBy (zpowers e) A

def element (A : Subgroup G) (e : G) (i : Orbit A e) : Additive (Span A e) :=
  Additive.ofMul ⟨i, by
    obtain ⟨a, ha, he⟩ := (mem_orbit A e i).mp i.property
    exact subset_closure ⟨a, ha, e, mem_zpowers e, he⟩⟩

theorem element_injective (A : Subgroup G) (e : G) : Function.Injective (element A e) := by
  intro i j hij
  exact Subtype.ext (congrArg (fun x : Additive (Span A e) => (x.toMul : G)) hij)

variable (A : Subgroup G) (e : G) [IsElementaryAbelian 2 (Span A e)]

def representation : Representation (ZMod 2) A (Additive (Span A e)) :=
  elementaryRepresentation ((Span A e).normalizerMonoidHom.comp
    (inclusion (le_normalizer_conjugateSpanBy (zpowers e) A)))

theorem representation_ker :
    (representation A e).ker = (centralizer (Span A e : Set G)).subgroupOf A := by
  ext a
  change representation A e a = 1 ↔ (a : G) ∈ centralizer (Span A e : Set G)
  constructor
  · intro ha w hw
    have hh := congrArg (fun x : Additive (Span A e) => (x.toMul : G))
      (LinearMap.congr_fun ha (Additive.ofMul ⟨w, hw⟩))
    change (a : G) * w * (a : G)⁻¹ = w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro ha
    ext w
    change (a : G) * (w.toMul : G) * (a : G)⁻¹ = w.toMul
    exact mul_inv_eq_iff_eq_mul.mpr (ha w.toMul w.toMul.property).symm

theorem element_equivariant (a : A) (i : Orbit A e) :
    element A e (permutation A e a i) = representation A e a (element A e i) := rfl

theorem elements_span : Submodule.span (ZMod 2) (Set.range (element A e)) = ⊤ := by
  let S := Submodule.span (ZMod 2) (Set.range (element A e))
  let K : Subgroup (Span A e) := S.toAddSubgroup.toSubgroup
  have hspan : Span A e ≤ K.map (Span A e).subtype := by
    apply (closure_le _).mpr
    rintro x ⟨a, ha, z, hz, rfl⟩
    have hae : a * e * a⁻¹ ∈ K.map (Span A e).subtype := by
      let i : Orbit A e := ⟨a * e * a⁻¹, (mem_orbit A e _).mpr ⟨a, ha, rfl⟩⟩
      refine ⟨(element A e i).toMul, ?_, rfl⟩
      change element A e i ∈ S
      exact Submodule.subset_span ⟨i, rfl⟩
    have hm : (zpowers e).map (MulAut.conj a).toMonoidHom ≤ K.map (Span A e).subtype := by
      rw [MonoidHom.map_zpowers]
      exact zpowers_le.mpr hae
    exact hm (mem_map_of_mem (MulAut.conj a).toMonoidHom hz)
  apply Submodule.eq_top_iff'.mpr
  intro w
  obtain ⟨y, hy, he⟩ := hspan w.toMul.property
  have he' : y = w.toMul := Subtype.ext he
  change Additive.ofMul w.toMul ∈ S
  rw [← he']
  exact hy

def quotient [Finite G] :
    Representation.IntertwiningMap
      ((BinaryPermutation.representation (Orbit A e)).comp (permutation A e)) (representation A e) :=
  BinaryPermutation.orbitQuotient (representation A e) (permutation A e)
    (element A e) (element_equivariant A e)

theorem quotient_surjective [Finite G] : Function.Surjective (quotient A e) :=
  BinaryPermutation.orbitQuotient_surjective _ _ _ _ (elements_span A e)

theorem dimension_le_orbit_card [Finite G] :
    Module.finrank (ZMod 2) (Additive (Span A e)) ≤ Nat.card (Orbit A e) := by
  have h := LinearMap.finrank_le_finrank_of_surjective (quotient_surjective A e)
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using h

end Representation.BinaryConjugacyOrbit
