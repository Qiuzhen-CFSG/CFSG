module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PPerfectHom

/-!
# Residual and fixed-element preliminaries for 14.7.67–68

The genuine 14.7.63 data put K in the actual Chapter 1 local-component family:
T is Sylow in KT=H, and the nonidentity flag point lies in O₂(H).
For an element fixed modulo V₁, its commutator displacement is a homomorphism
into the central binary point group. Two-perfectness kills this displacement
on K. Thus K centralizes the original U₀, rather than merely its image modulo
V₁. On T the same homomorphism has kernel C_T(u), giving normality and index
at most two. These are the opening reductions in 14.7.68 and inputs to the
residual-normalizer and component-exclusion branches.

This module proves neither maximal membership in L*(G,T), nor N_G(K)=H,
nor the ambient fixed-element centralizer bound. Those are the substantial
remaining source arguments. It imports no legacy CriticalFusion.Setup.Input.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.67–68, printed pp.1070–1072.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
omit [Finite G] in
theorem K_le_H (F : InvariantFlag T V 3) : K F ≤ F.H := map_subtype_le _

theorem K_twoPerfect (F : InvariantFlag T V 3) : IsPPerfect 2 (K F) := isPPerfect_embedded_pResidual 2 F.H

omit [Finite G] in
theorem H_normalizes_K (F : InvariantFlag T V 3) : F.H ≤ normalizer (K F : Set G) :=
  le_normalizer_embedded_pResidual 2 F.H

namespace Data
variable (d : Data T L V F W)

include d in
theorem H_centralizes_point : F.H ≤ centralizer (F.Vi 1 : Set G) := by
  rw [d.point, zpowers_eq_closure, centralizer_closure, d.centralizer_eq]

include d in
theorem point_le_H : F.Vi 1 ≤ F.H :=
  d.conjugationSection.kernel_le.trans d.conjugationSection.section_le

include d in
theorem point_twoGroup : IsPGroup 2 (F.Vi 1) := by
  let := d.U_elementary
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le d.conjugationSection.kernel_le
  exact IsElementaryAbelian.isPGroup 2 _

include d in
theorem K_mem_localFamily : K F ∈ Chapter1.L G (T : Subgroup G) := by
  change ((K F).subgroupOf (K F ⊔ (T : Subgroup G))).IsCComponent ∧ _
  rw [← d.residual_product]
  refine ⟨d.component, ⟨T.subtype (F.invariant 1),
    map_subgroupOf_eq_of_le (F.invariant 1)⟩, ?_⟩
  have hp : F.Vi 1 ≤ F.H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes d.point_twoGroup d.point_le_H le_rfl
  intro he
  have hz : d.z ∈ F.H.pCoreIn 2 := hp (by rw [d.point]; exact mem_zpowers d.z)
  rw [he] at hz
  exact d.z_ne_one hz

private theorem commutator_mem_point (a : F.H) (u : F.U)
    (hfix : d.action a (d.conjugationSection.coordinates u).toAdd =
      (d.conjugationSection.coordinates u).toAdd) : ⁅(a : G), (u : G)⁆ ∈ F.Vi 1 := by
  let v : F.U := ⟨a * u * (a : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized a.property) u).mp u.property⟩
  have he : d.conjugationSection.coordinates v = d.conjugationSection.coordinates u :=
    Multiplicative.toAdd.injective ((d.conjugationSection.equivariant a u).trans hfix)
  exact (d.conjugationSection.coordinates_eq_one_iff (v * u⁻¹)).mp (by
    rw [map_mul, map_inv, he, mul_inv_cancel])

/-- The displacement into the original point group, not its quotient image. -/
def pointDisplacement (A : Subgroup G) (hAH : A ≤ F.H) (u : F.U)
    (hfix : ∀ a : A, d.action ⟨a, hAH a.property⟩ (d.conjugationSection.coordinates u).toAdd =
      (d.conjugationSection.coordinates u).toAdd) : A →* F.Vi 1 where
  toFun a := ⟨⁅(a : G), (u : G)⁆, by
    exact d.commutator_mem_point ⟨a, hAH a.property⟩ u (hfix a)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅(a : G) * b, (u : G)⁆ = ⁅(a : G), (u : G)⁆ * ⁅(b : G), (u : G)⁆
    have ha := d.commutator_mem_point ⟨a, hAH a.property⟩ u (hfix a)
    have hb := d.commutator_mem_point ⟨b, hAH b.property⟩ u (hfix b)
    have hc := mem_centralizer_iff.mp (d.H_centralizes_point (hAH a.property)) _ hb
    rw [commutatorElement_mul_left_eq_conj_mul, ← hc, mul_inv_cancel_right]
    exact mem_centralizer_iff.mp (d.H_centralizes_point (d.point_le_H ha)) _ hb

theorem K_centralizes_U₀ : K F ≤ centralizer (d.U₀ : Set G) := by
  intro k hk
  apply mem_centralizer_iff.mpr
  intro u hu
  let v : F.U := ⟨u, d.U₀_le_U hu⟩
  have hf : ∀ a : K F,
      d.action ⟨a, K_le_H F a.property⟩ (d.conjugationSection.coordinates v).toAdd =
        (d.conjugationSection.coordinates v).toAdd := by
    intro a
    have hi := (d.mem_U₀ v).mp hu
    rw [d.fixed_kernel] at hi
    exact (Representation.mem_invariants _ _).mp hi ⟨⟨a, K_le_H F a.property⟩, a.property⟩
  let f := d.pointDisplacement (K F) (K_le_H F) v hf
  have he := (K_twoPerfect F).hom_eq_one_of_isPGroup d.point_twoGroup f
  have hcomm := congrArg (fun q : K F →* F.Vi 1 => (q ⟨k, hk⟩ : G)) he
  exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm

/-- Fixation of the original coordinate modulo V₁ by the actual Sylow T. -/
def FixedModuloPoint (u : F.U) : Prop :=
  ∀ t : T, d.action ⟨t, F.invariant 1 t.property⟩ (d.conjugationSection.coordinates u).toAdd =
    (d.conjugationSection.coordinates u).toAdd

/-- The kernel is the actual intrinsic centralizer of the element. -/
theorem pointDisplacement_ker (A : Subgroup G) (hAH : A ≤ F.H) (u : F.U)
    (hfix : ∀ a : A, d.action ⟨a, hAH a.property⟩ (d.conjugationSection.coordinates u).toAdd =
      (d.conjugationSection.coordinates u).toAdd) :
    (d.pointDisplacement A hAH u hfix).ker = (centralizer ({(u : G)} : Set G)).subgroupOf A := by
  ext a
  change (d.pointDisplacement A hAH u hfix a = 1) ↔
    (a : G) ∈ centralizer ({(u : G)} : Set G)
  rw [Subtype.ext_iff]
  change ⁅(a : G), (u : G)⁆ = 1 ↔ _
  rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]

/-- The intrinsic centralizer in T has index at most two. -/
theorem fixedModuloPoint_centralizer_index (u : F.U) (hu : d.FixedModuloPoint u) :
    ((centralizer ({(u : G)} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2 := by
  let f := d.pointDisplacement (T : Subgroup G) (F.invariant 1) u hu
  rw [← d.pointDisplacement_ker (T : Subgroup G) (F.invariant 1) u hu, index_ker]
  calc
    Nat.card f.range ≤ Nat.card (F.Vi 1) := Nat.card_le_card_of_injective _ f.range.subtype_injective
    _ = 2 := by simpa using F.card 1 (by decide)

/-- The same displacement realizes C_T(u) as a normal subgroup of T. -/
theorem fixedModuloPoint_centralizer_normal (u : F.U) (hu : d.FixedModuloPoint u) :
    ((centralizer ({(u : G)} : Set G)).subgroupOf (T : Subgroup G)).Normal := by
  rw [← d.pointDisplacement_ker (T : Subgroup G) (F.invariant 1) u hu]
  infer_instance

theorem fixedModuloPoint_of_mem_point (u : F.U) (hu : (u : G) ∈ F.Vi 1) :
    d.FixedModuloPoint u := by
  have hz : (d.conjugationSection.coordinates u).toAdd = 0 :=
    (d.conjugationSection.coordinates_eq_one_iff u).mpr hu
  intro t
  rw [hz, map_zero]

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
