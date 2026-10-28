module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.ModelData
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Transporting marked normalizer models

An ambient automorphism preserving L, r and z preserves the actual embedded
residual O²(C_L(r)). Mapping Q transports its relative quaternion quotient,
its cyclic-four centralizer quotient and its irreducibility on that residual.
The quotient equivalences use the transported restricted subgroup E in each
ambient Q; no ambient normality of E is asserted.

This supports the compatible Sylow choice in Aschbacher–Smith, proof of
16.4.9(2), combined manuscript of 1 March 2004, printed p.1191.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {r z : G}

omit [Finite G] in
private theorem map_four (e : G ≃* G) (hr : e r = r) (hz : e z = z) :
    (fourGroup r z).map e.toMonoidHom = fourGroup r z := by
  simp only [fourGroup, Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hr, hz]

private theorem map_residual (e : G ≃* G) (hL : L.map e.toMonoidHom = L)
    (hr : e r = r) : (residual L r).map e.toMonoidHom = residual L r := by
  change ((pResidual 2 (L ⊓ centralizer ({r} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({r} : Set G)).subtype).map e.toMonoidHom = _
  rw [map_embedded_pResidual, map_inf _ _ _ e.injective, hL, map_centralizer_equiv]
  rw [show e '' ({r} : Set G) = {r} by rw [Set.image_singleton, hr]]
  rfl

omit [Finite G] in
private theorem map_relative (e : G ≃* G) (Q E : Subgroup G)
    (hE : E.map e.toMonoidHom = E) :
    (E.subgroupOf Q).map (e.subgroupMap Q).toMonoidHom =
      E.subgroupOf (Q.map e.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hE ▸ mem_map_of_mem e.toMonoidHom hy
  · intro hx
    refine ⟨(e.subgroupMap Q).symm x, ?_, (e.subgroupMap Q).apply_symm_apply x⟩
    have hx' : (x : G) ∈ E.map e.toMonoidHom := hE.symm ▸ hx
    change e.symm (x : G) ∈ E
    exact (mem_map_equiv (f := e)).mp hx'

/-- Transport every normalizer field while fixing the two marked generators. -/
noncomputable def NormalizerData.transport (d : NormalizerData L r z)
    (e : G ≃* G) (hL : L.map e.toMonoidHom = L) (hr : e r = r) (hz : e z = z) :
    NormalizerData L r z := by
  have hE : (fourGroup r z).map e.toMonoidHom = fourGroup r z := by
    exact map_four e hr hz
  have hD : (residual L r).map e.toMonoidHom = residual L r := by
    exact map_residual e hL hr
  have hN : (d.Q.map e.toMonoidHom) ≤ normalizer (fourGroup r z : Set G) := by
    have hh := map_mono (f := e.toMonoidHom) d.normalizes_four
    rwa [map_equiv_normalizer_eq, hE] at hh
  refine {
    Q := d.Q.map e.toMonoidHom
    two_group := d.two_group.map e.toMonoidHom
    four_le := hE ▸ map_mono (f := e.toMonoidHom) d.four_le
    le_product := ?_
    normalizes_four := hN
    normalizes_residual := ?_
    normalizer_eq := ?_
    centralizer_eq := ?_
    residual_fixer := d.residual_fixer
    quaternion := ?_ }
  · have hh := map_mono (f := e.toMonoidHom) d.le_product
    rwa [Subgroup.map_sup, hL, hE] at hh
  · have hh := map_mono (f := e.toMonoidHom) d.normalizes_residual
    rwa [map_equiv_normalizer_eq, hD] at hh
  · have hh := congrArg (fun A : Subgroup G => A.map e.toMonoidHom) d.normalizer_eq
    rwa [map_inf _ _ _ e.injective, Subgroup.map_sup, hL, hE, map_equiv_normalizer_eq,
      hE, Subgroup.map_sup, hD] at hh
  · have hh := congrArg (fun A : Subgroup G => A.map e.toMonoidHom) d.centralizer_eq
    rw [map_inf _ _ _ e.injective, map_centralizer_equiv] at hh
    change d.Q.map e.toMonoidHom ⊓ centralizer ((residual L r).map e.toMonoidHom : Set G) =
      (fourGroup r z).map e.toMonoidHom at hh
    rwa [hD, hE] at hh
  · let : ((fourGroup r z).subgroupOf d.Q).Normal :=
      normal_subgroupOf_of_le_normalizer d.normalizes_four
    let : ((fourGroup r z).subgroupOf (d.Q.map e.toMonoidHom)).Normal :=
      normal_subgroupOf_of_le_normalizer hN
    obtain ⟨q⟩ := d.quaternion
    exact ⟨(QuotientGroup.congr ((fourGroup r z).subgroupOf d.Q)
      ((fourGroup r z).subgroupOf (d.Q.map e.toMonoidHom)) (e.subgroupMap d.Q)
      (map_relative e d.Q (fourGroup r z) hE)).symm.trans q⟩

/-- The transported model has exactly the ambient image of the original Q. -/
theorem NormalizerData.transport_Q (d : NormalizerData L r z)
    (e : G ≃* G) (hL : L.map e.toMonoidHom = L) (hr : e r = r) (hz : e z = z) :
    (d.transport e hL hr hz).Q = d.Q.map e.toMonoidHom := by
  change d.Q.map e.toMonoidHom = d.Q.map e.toMonoidHom
  exact Eq.refl _

/-- Transport the marked transvection, cyclic-four quotient and irreducibility. -/
theorem CoverActionData.transport {d : NormalizerData L r z} (c : CoverActionData d)
    (e : G ≃* G) (hL : L.map e.toMonoidHom = L) (hr : e r = r) (hz : e z = z) :
    CoverActionData (d.transport e hL hr hz) := by
  have hE := map_four e hr hz
  have hD := map_residual e hL hr
  have hC : (d.Q ⊓ centralizer (fourGroup r z : Set G)).map e.toMonoidHom =
      (d.transport e hL hr hz).Q ⊓ centralizer (fourGroup r z : Set G) := by
    rw [map_inf _ _ _ e.injective, map_centralizer_equiv]
    change d.Q.map e.toMonoidHom ⊓ centralizer ((fourGroup r z).map e.toMonoidHom : Set G) = _
    rw [hE]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := map_mono (f := e.toMonoidHom) c.fixes_z
    rw [map_centralizer_equiv, Set.image_singleton, hz] at hh
    exact hh
  · obtain ⟨t, ht, htr⟩ := c.transvection
    refine ⟨e t, mem_map_of_mem e.toMonoidHom ht, ?_⟩
    have hh := congrArg e htr
    simpa only [MulAut.conj_apply, map_mul, map_inv, hr, hz] using hh
  · let C := d.Q ⊓ centralizer (fourGroup r z : Set G)
    let C' := (d.transport e hL hr hz).Q ⊓ centralizer (fourGroup r z : Set G)
    let : ((fourGroup r z).subgroupOf C).Normal :=
      normal_subgroupOf_of_le_normalizer (inf_le_left.trans d.normalizes_four)
    let : ((fourGroup r z).subgroupOf (C.map e.toMonoidHom)).Normal := by
      apply normal_subgroupOf_of_le_normalizer
      rw [hC]
      exact inf_le_left.trans (d.transport e hL hr hz).normalizes_four
    let : ((fourGroup r z).subgroupOf C').Normal :=
      normal_subgroupOf_of_le_normalizer
        (inf_le_left.trans (d.transport e hL hr hz).normalizes_four)
    obtain ⟨q⟩ := c.cyclic_four
    let a := QuotientGroup.congr ((fourGroup r z).subgroupOf C)
      ((fourGroup r z).subgroupOf (C.map e.toMonoidHom)) (e.subgroupMap C) (map_relative e C (fourGroup r z) hE)
    let b := QuotientGroup.equivQuotientSubgroupOfOfEq (A' := fourGroup r z)
      (B' := fourGroup r z) (A := C.map e.toMonoidHom) (B := C') rfl hC
    exact ⟨b.symm.trans (a.symm.trans q)⟩
  · intro A hAD hAN
    let B := A.map e.symm.toMonoidHom
    have hback : B.map e.toMonoidHom = A := by
      exact (map_symm_eq_iff_map_eq B (e := e)).mp rfl
    have hBD : B ≤ residual L r := by
      apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
      rwa [hback, hD]
    have hBN : d.Q ⊓ centralizer (fourGroup r z : Set G) ≤ normalizer (B : Set G) := by
      apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
      rwa [hC, map_equiv_normalizer_eq, hback]
    rcases c.irreducible B hBD hBN with hb | hb
    · left
      rw [← hback, hb, Subgroup.map_bot]
    · right
      rw [← hback, hb, hD]
end CFSG.Quasithin.Chapter16.Intersections.GraphField
