module
public import Theory.Representation.PermutationBasisOrbits
public import Theory.Representation.BinaryOffender.Basic
public import Theory.GroupTheory.PGroup.MaximalIndex
public import Mathlib.GroupTheory.Sylow

/-!
# Hyperplane fixed vectors from permutation bases

For a faithful action of a nontrivial finite two-group on a permuted basis,
a moved basis index has a proper stabilizer. Enlarge that stabilizer to a
maximal subgroup. Its orbit indicator is fixed by this index-two subgroup
but not by the whole group. Conjugacy of Sylow subgroups transports the
construction to every two-subgroup of an ambient group.

This is the fixed-space calculation for the deleted pair and tensor modules
in Aschbacher--Smith 10.3.1, printed pp.755--756.
-/

public section

open Representation Representation.BinaryOffender

namespace Representation
variable {G V ι : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite ι] [MulAction G ι]

theorem hyperplane_witness_of_permutedBasis (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hG : IsPGroup 2 G) [Nontrivial G]
    (b : Module.Basis ι (ZMod 2) V) (hb : ∀ g i, ρ g (b i) = b (g • i)) :
    ∃ B : Subgroup G, B.index = 2 ∧ ∃ v : V,
      (∀ g : B, ρ g v = v) ∧ ¬ (∀ g : G, ρ g v = v) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  have hm : ∃ i : ι, a • i ≠ i := by
    by_contra! hn
    apply ha
    apply hρ
    apply b.ext
    intro i
    simp only [hb, hn, map_one, Module.End.one_apply]
  obtain ⟨i, hi⟩ := hm
  have hstab : MulAction.stabilizer G i ≠ ⊤ := by
    intro hh
    exact hi (show a • i = i from (show a ∈ MulAction.stabilizer G i from hh ▸ Subgroup.mem_top a))
  obtain ⟨B, hB, hSB⟩ := (eq_top_or_exists_le_coatom (MulAction.stabilizer G i)).resolve_left hstab
  obtain ⟨a, ha⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hB.ne_top)
  have haB : a ∉ B := ha.2
  have hai : a • i ∉ MulAction.orbit B i := by
    rintro ⟨g, hg⟩
    have hs : (g : G)⁻¹ * a ∈ MulAction.stabilizer G i := by
      change ((g : G)⁻¹ * a) • i = i
      rw [mul_smul, ← hg]
      exact inv_smul_smul (g : G) i
    have h := B.mul_mem g.property (hSB hs)
    exact haB (by simpa only [mul_inv_cancel_left] using h)
  let f : ι → ZMod 2 := fun j => if j ∈ MulAction.orbit B i then 1 else 0
  let v : V := b.equivFun.symm f
  have hv : b.equivFun v = f := b.equivFun.apply_symm_apply f
  have hf (g : B) (j : ι) : f (g • j) = f j := by
    have he : g • j ∈ MulAction.orbit B i ↔ j ∈ MulAction.orbit B i := by
      constructor
      · intro hj
        have h := MulAction.mem_orbit_of_mem_orbit g⁻¹ hj
        simpa only [inv_smul_smul] using h
      · exact MulAction.mem_orbit_of_mem_orbit g
    simp only [f, he]
  refine ⟨B, hG.index_of_isCoatom B hB, v, ?_, ?_⟩
  · intro g
    apply b.equivFun.injective
    funext j
    obtain ⟨k, rfl⟩ := (MulAction.toPerm (g : G)).surjective j
    have he := equivariantBasis_equivFun_apply b (ρ g) (MulAction.toPerm (g : G)) (hb g) v k
    change b.equivFun (ρ g v) ((g : G) • k) = b.equivFun v ((g : G) • k)
    simp only [MulAction.toPerm_apply] at he
    rw [he, hv]
    exact (hf g k).symm
  · intro hh
    have he := equivariantBasis_equivFun_apply b (ρ a) (MulAction.toPerm a) (hb a) v i
    rw [hh a, hv] at he
    have hz : (0 : ZMod 2) = 1 := by
      simpa only [MulAction.toPerm_apply, f, if_neg hai, MulAction.mem_orbit_self, if_true] using he
    exact zero_ne_one hz

/-- A permutation basis for one Sylow subgroup supplies an actual hyperplane
fixed-vector witness for every nontrivial two-subgroup. -/
theorem hyperplane_witness_of_sylow_permutedBasis
    {X : Type*} [Group X] [Finite X]
    (ρ : Representation (ZMod 2) X V) (hρ : Function.Injective ρ)
    (P : Sylow 2 X) [MulAction P ι]
    (b : Module.Basis ι (ZMod 2) V) (hb : ∀ g : P, ∀ i, ρ g (b i) = b (g • i))
    (A : Subgroup X) (hA : IsPGroup 2 A) (hne : A ≠ ⊥) :
    ∃ B ≤ A, B.relIndex A = 2 ∧ fixedSpace ρ A < fixedSpace ρ B := by
  classical
  obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  have hQP : (Q : Subgroup X).map (MulAut.conj g).toMonoidHom = P :=
    congrArg Sylow.toSubgroup hg
  let f : A →* P := ((MulAut.conj g).toMonoidHom.comp A.subtype).codRestrict P (by
    intro a
    change (MulAut.conj g) (a : X) ∈ (P : Subgroup X)
    rw [← hQP]
    exact Subgroup.mem_map_of_mem _ (hAQ a.property))
  let : MulAction A ι := MulAction.compHom ι f
  let E : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (ρ g⁻¹) (ρ.apply_bijective g⁻¹)
  have hc (a : A) (i : ι) : (ρ.comp A.subtype) a ((b.map E) i) = (b.map E) (a • i) := by
    change ρ a (ρ g⁻¹ (b i)) = ρ g⁻¹ (b (f a • i))
    rw [← hb (f a) i]
    change ρ a (ρ g⁻¹ (b i)) = ρ g⁻¹ (ρ (g * a * g⁻¹) (b i))
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left]
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne
  obtain ⟨B, hB, v, hv, hnv⟩ := hyperplane_witness_of_permutedBasis
    (ρ.comp A.subtype) (hρ.comp A.subtype_injective) hA (b.map E) hc
  refine ⟨B.map A.subtype, Subgroup.map_subtype_le B, ?_, ?_⟩
  · have he := Subgroup.relIndex_map_map_of_injective B ⊤ A.subtype_injective
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.relIndex_top_right] using he.trans (by simpa using hB)
  · apply lt_of_le_of_ne
    · intro w hw x
      obtain ⟨a, ha, he⟩ := x.property
      change ρ (x : X) w = w
      rw [← he]
      exact hw a
    · intro he
      have hvB : v ∈ fixedSpace ρ (B.map A.subtype) := by
        rintro ⟨_, a, ha, rfl⟩
        exact hv ⟨a, ha⟩
      rw [← he] at hvB
      exact hnv hvB

end Representation
