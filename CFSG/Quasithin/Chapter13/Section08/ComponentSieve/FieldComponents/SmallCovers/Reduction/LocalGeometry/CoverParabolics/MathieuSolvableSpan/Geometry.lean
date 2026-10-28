module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient
public import Theory.Mathieu.M22.Properties.HexadMaximal
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Invariant hexads in the actual automorphism group of M₂₂

The faithful design realization transfers the action on all 77 hexads to
abstract automorphisms. Every two-subgroup fixes a hexad. The inner action
is primitive because its actual hexad stabilizers are ordinary maximal
subgroups, and primitivity passes to each group containing the inner group.

The inner group has index two. Consequently a Sylow two-subgroup supplements
it, and the stabilizer of an invariant hexad is exactly the join of the
inner hexad stabilizer and that Sylow subgroup. This proves ordinary
maximality in every intermediate automorphism group, including the outer case.

Source: the Mathieu geometry used in Aschbacher--Smith 13.8.21(2),
printed p.956 (PDF p.973). Solvable-overgroup generation is proved separately;
no C-component dichotomy is assumed here.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M22ValueBound.Concrete
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MathieuSolvableSpan
abbrev Hexad := { B : Finset (Fin 22) // B ∈ m22Blocks }

theorem design_smul_mem (g : m22DesignAut) (B : Hexad) :
    g • B.val ∈ m22Blocks := by
  have h := (Theory.GroupTheory.SteinerSystem.mem_aut_iff m22WittDesign g.val).mp g.property
  have hm := Set.smul_mem_smul_set B.property (a := g.val)
  change g.val • B.val ∈ g.val • (m22WittDesign.blocks : Set (Finset (Fin 22))) at hm
  rw [h] at hm
  exact hm

noncomputable instance designHexadAction : MulAction m22DesignAut Hexad where
  smul g B := ⟨g • B.val, design_smul_mem g B⟩
  one_smul B := Subtype.ext (one_smul m22DesignAut B.val)
  mul_smul g h B := Subtype.ext (mul_smul g h B.val)

noncomputable instance autHexadAction : MulAction (MulAut M22) Hexad :=
  MulAction.compHom Hexad designAutEquiv.symm.toMonoidHom
noncomputable instance innerHexadAction : MulAction M22 Hexad :=
  MulAction.compHom Hexad inclusion

@[simp] theorem inner_smul (g : M22) (B : Hexad) : MulAut.conj g • B = g • B := by
  change designAutEquiv.symm (MulAut.conj g) • B = inclusion g • B
  rw [← designAutEquiv_inclusion, MulEquiv.symm_apply_apply]

theorem hexad_card : Nat.card Hexad = 77 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, m22Blocks_cardinality]

instance hexad_nontrivial : Nontrivial Hexad := Finite.one_lt_card_iff_nontrivial.mp (by rw [hexad_card]; decide)

noncomputable def innerHexad (B : Hexad) : Subgroup (MulAut M22) :=
  (MulAction.stabilizer M22 B.val).map (MulAut.conj : M22 →* MulAut M22)

theorem exists_invariant_hexad (S : Subgroup (MulAut M22)) (hS : IsPGroup 2 S) :
    ∃ B : Hexad, S ≤ MulAction.stabilizer (MulAut M22) B := by
  obtain ⟨B, hB⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card Hexad (by
    rw [hexad_card]; decide)
  exact ⟨B, fun s hs => (MulAction.mem_fixedPoints.mp hB) ⟨s, hs⟩⟩

instance innerHexad_pretransitive : MulAction.IsPretransitive M22 Hexad where
  exists_smul_eq B C := by
    obtain ⟨g, hg⟩ := exists_smul_m22Hexad123_eq B.property
    obtain ⟨h, hh⟩ := exists_smul_m22Hexad123_eq C.property
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    change (h * g⁻¹) • B.val = C.val
    rw [mul_smul, ← hg, inv_smul_smul, hh]

instance innerHexad_preprimitive : MulAction.IsPreprimitive M22 Hexad := by
  apply (MulAction.isCoatom_stabilizer_iff_preprimitive M22
    (⟨m22Hexad123, m22Hexad123_mem⟩ : Hexad)).mp
  have he : MulAction.stabilizer M22 (⟨m22Hexad123, m22Hexad123_mem⟩ : Hexad) =
      MulAction.stabilizer M22 m22Hexad123 := by
    ext g
    exact Subtype.ext_iff
  rw [he]
  exact m22HexadStabilizer_isCoatom

noncomputable def innerTo (A : Subgroup (MulAut M22)) (hA : m22InnerAut ≤ A) : M22 →* A :=
  (MulAut.conj : M22 →* MulAut M22).codRestrict A (fun g => hA ⟨g, rfl⟩)

theorem primitive (A : Subgroup (MulAut M22)) (hA : m22InnerAut ≤ A) :
    MulAction.IsPreprimitive A Hexad := by
  let f : Hexad →ₑ[innerTo A hA] Hexad := ⟨id, fun g B => (inner_smul g B).symm⟩
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

theorem innerHexad_eq_inf (B : Hexad) :
    innerHexad B = MulAction.stabilizer (MulAut M22) B ⊓ m22InnerAut := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, ⟨g, rfl⟩⟩
    change MulAut.conj g • B = B
    rw [inner_smul]
    exact Subtype.ext hg
  · rintro ⟨ha, g, rfl⟩
    refine ⟨g, ?_, rfl⟩
    change MulAut.conj g • B = B at ha
    rw [inner_smul] at ha
    exact congrArg Subtype.val ha

theorem innerHexad_normalized (B : Hexad) :
    MulAction.stabilizer (MulAut M22) B ≤ normalizer (innerHexad B : Set (MulAut M22)) := by
  rw [innerHexad_eq_inf]
  exact (le_inf (MulAction.stabilizer (MulAut M22) B).le_normalizer
    le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

theorem innerHexad_le_inner (B : Hexad) : innerHexad B ≤ m22InnerAut :=
  (MulAction.stabilizer M22 B.val).map_le_range _

theorem map_inner : inner.map designAutEquiv.toMonoidHom = m22InnerAut := by
  have he : designAutEquiv.toMonoidHom.comp inclusion =
      (MulAut.conj : M22 →* MulAut M22) := by
    apply MonoidHom.ext
    exact designAutEquiv_inclusion
  rw [← inclusion_range, MonoidHom.map_range, he]
  rfl

theorem inner_index_two : m22InnerAut.index = 2 := by
  rw [← map_inner]
  exact (index_map_of_bijective designAutEquiv.bijective inner).trans inner_index

theorem inner_sup_sylow (A : Subgroup (MulAut M22)) (hA : m22InnerAut ≤ A)
    (P : Sylow 2 A) :
    m22InnerAut ⊔ (P : Subgroup A).map A.subtype = A := by
  have hd : Nat.card (A ⧸ m22InnerAut.subgroupOf A) ∣ 2 := by
    change m22InnerAut.relIndex A ∣ 2
    rw [← inner_index_two]
    exact m22InnerAut.relIndex_dvd_index_of_normal (K := A)
  have hp : IsPGroup 2 (A ⧸ m22InnerAut.subgroupOf A) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hd)
  have he := congrArg (map A.subtype)
    (P.sup_eq_top_of_quotient_isPGroup (m22InnerAut.subgroupOf A) hp)
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hA, ← MonoidHom.range_eq_map, range_subtype] at he
  rwa [sup_comm] at he

theorem stabilizer_eq_join (A : Subgroup (MulAut M22)) (hA : m22InnerAut ≤ A)
    (P : Sylow 2 A) (B : Hexad)
    (hfix : (P : Subgroup A).map A.subtype ≤ MulAction.stabilizer (MulAut M22) B) :
    (MulAction.stabilizer (MulAut M22) B) ⊓ A =
      innerHexad B ⊔ (P : Subgroup A).map A.subtype := by
  let S := (P : Subgroup A).map A.subtype
  have hSA : S ≤ A := map_subtype_le _
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ m22InnerAut ⊔ S := (inner_sup_sylow A hA P).symm ▸ hx.2
    rw [← SetLike.mem_coe, normal_mul] at hx'
    obtain ⟨n, hn, s, hs, rfl⟩ := hx'
    have hns : n ∈ MulAction.stabilizer (MulAut M22) B := by
      have h := (MulAction.stabilizer (MulAut M22) B).mul_mem hx.1
        ((MulAction.stabilizer (MulAut M22) B).inv_mem (hfix hs))
      simpa only [mul_inv_cancel_right] using h
    have hnE : n ∈ innerHexad B := by rw [innerHexad_eq_inf]; exact ⟨hns, hn⟩
    exact (innerHexad B ⊔ S).mul_mem (mem_sup_left hnE) (mem_sup_right hs)
  · exact sup_le
      (le_inf ((innerHexad_eq_inf B).le.trans inf_le_left) ((innerHexad_le_inner B).trans hA))
      (le_inf hfix hSA)

theorem join_isCoatom (A : Subgroup (MulAut M22)) (hA : m22InnerAut ≤ A)
    (P : Sylow 2 A) (B : Hexad)
    (hfix : (P : Subgroup A).map A.subtype ≤ MulAction.stabilizer (MulAut M22) B) :
    IsCoatom ((innerHexad B ⊔ (P : Subgroup A).map A.subtype).subgroupOf A) := by
  let := primitive A hA
  have hm := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive A B
  have he : (innerHexad B ⊔ (P : Subgroup A).map A.subtype).subgroupOf A =
      MulAction.stabilizer A B := by
    rw [← stabilizer_eq_join A hA P B hfix]
    ext x
    exact and_iff_left x.property
  rwa [he]


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MathieuSolvableSpan
