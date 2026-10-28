module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CentralProduct
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Alternating
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.ZMod

/-!
# The marked natural head of the six-dimensional module

The Q/U and Q/HC coordinate maps factor through a surjective equivariant
binary linear map. Its two-dimensional kernel is the literal HC/U section.
The preceding J.2.2(3) commutator assertion makes that kernel A₅-fixed.
If an actor moves a kernel vector, the decomposition HC=C_Q(B)U supplies
an element of C_Q(B) whose commutator lies outside Z. This last transport
does not assume a splitting, and it retains the original H/Q marking.

The nontriviality of the outer action on this kernel is a separate
representation-theoretic obligation; it is not proved by the transport lemma.
Source: Aschbacher–Smith, J.2.2(3) and J.2.5, printed pp.432, 434
(PDF pp.443, 445 of `refs/quasithin.pdf`).
-/

@[expose] public section

noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]
variable (d : LocalSetup G) (head : NaturalHead d.toTypeRuSetup)

def NaturalHead.sixProjectionHom : Multiplicative SixSpace →* Multiplicative FourSpace :=
  d.ru2.six.coordinates.liftOfSurjective d.ru2.six.onto
    ⟨head.sectionData.coordinates, by
      rw [d.ru2.six.kernel_eq, head.sectionData.kernel_eq]
      exact comap_mono d.U_le_HC⟩

def NaturalHead.sixProjection : SixSpace →ₗ[ZMod 2] FourSpace :=
  (AddMonoidHom.toMultiplicative.symm (head.sixProjectionHom d)).toZModLinearMap 2

theorem NaturalHead.sixProjection_coordinates (q : d.toTypeRuSetup.Q) :
    head.sixProjection d (d.ru2.six.coordinates q).toAdd =
      (head.sectionData.coordinates q).toAdd := by
  change ((head.sixProjectionHom d) (d.ru2.six.coordinates q)).toAdd = _
  simp only [NaturalHead.sixProjectionHom, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply]

theorem NaturalHead.sixProjection_surjective : Function.Surjective (head.sixProjection d) := by
  intro v
  obtain ⟨q, hq⟩ := head.sectionData.onto (Multiplicative.ofAdd v)
  exact ⟨(d.ru2.six.coordinates q).toAdd,
    (head.sixProjection_coordinates d q).trans (congrArg Multiplicative.toAdd hq)⟩

theorem NaturalHead.sixProjection_equivariant (g : S5) (v : SixSpace) :
    head.sixProjection d (d.ru2.sixAction g v) = head.action.action g (head.sixProjection d v) := by
  obtain ⟨h, rfl⟩ := d.ru2.quotient_surjective g
  obtain ⟨q, hq⟩ := d.ru2.six.onto (Multiplicative.ofAdd v)
  have hq' : (d.ru2.six.coordinates q).toAdd = v := congrArg Multiplicative.toAdd hq
  rw [← hq']
  have he := d.ru2.six.equivariant h q
  simp only [MonoidHom.comp_apply] at he
  rw [← he, head.sixProjection_coordinates, head.sixProjection_coordinates]
  exact head.sectionData.equivariant h q

theorem NaturalHead.sixProjection_kernel_coordinates (q : d.toTypeRuSetup.Q) :
    (d.ru2.six.coordinates q).toAdd ∈ (head.sixProjection d).ker ↔
      (q : G) ∈ d.toTypeRuSetup.HC := by
  change head.sixProjection d (d.ru2.six.coordinates q).toAdd = 0 ↔ _
  rw [head.sixProjection_coordinates]
  exact head.sectionData.coordinates_eq_one_iff q

theorem NaturalHead.finrank_sixProjection_kernel :
    Module.finrank (ZMod 2) (head.sixProjection d).ker = 2 := by
  have h := (head.sixProjection d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (head.sixProjection_surjective d),
    finrank_top, SL2FourNatural.finrank_vector] at h
  have hsix : Module.finrank (ZMod 2) SixSpace = 6 := by simp [SixSpace]
  omega

/-- The action on the literal HC/U kernel of the natural head projection. -/
def NaturalHead.kernelAction :
    Representation (ZMod 2) S5 (head.sixProjection d).ker where
  toFun g := ((d.ru2.sixAction g).comp (head.sixProjection d).ker.subtype).codRestrict _ (by
    intro v
    change head.sixProjection d (d.ru2.sixAction g v) = 0
    rw [head.sixProjection_equivariant, v.property, map_zero])
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change d.ru2.sixAction 1 v = v
    rw [map_one, Module.End.one_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change d.ru2.sixAction (g * h) v = d.ru2.sixAction g (d.ru2.sixAction h v)
    rw [map_mul, Module.End.mul_apply]

theorem NaturalHead.kernelAction_apply (g : S5) (v : (head.sixProjection d).ker) :
    (head.kernelAction d g v : SixSpace) = d.ru2.sixAction g v := rfl

theorem six_commutator_mem_U_iff (h : d.toTypeRuSetup.H) (q : d.toTypeRuSetup.Q) :
    ⁅(h : G), (q : G)⁆ ∈ d.toTypeRuSetup.U ↔
      d.ru2.sixAction (d.ru2.quotientMap h) (d.ru2.six.coordinates q).toAdd =
        (d.ru2.six.coordinates q).toAdd := by
  let q' : d.toTypeRuSetup.Q := ⟨(h : G) * q * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.ru2.six.normalized h.property) q).mp q.property⟩
  have he := d.ru2.six.equivariant h q
  change (d.ru2.six.coordinates q').toAdd =
    d.ru2.sixAction (d.ru2.quotientMap h) (d.ru2.six.coordinates q).toAdd at he
  rw [← he]
  change ((q' * q⁻¹ : d.toTypeRuSetup.Q) : G) ∈ d.toTypeRuSetup.U ↔ _
  rw [← d.ru2.six.coordinates_eq_one_iff, map_mul, map_inv, mul_inv_eq_one]
  exact Multiplicative.toAdd.injective.eq_iff.symm

theorem NaturalHead.sixProjection_kernel_fixed
    (hfixed : ∀ q ∈ d.toTypeRuSetup.HC, ∀ k ∈ d.toTypeRuSetup.K,
      ⁅k, q⁆ ∈ d.toTypeRuSetup.U)
    (a : alternatingGroup (Fin 5)) (v : SixSpace) (hv : v ∈ (head.sixProjection d).ker) :
    d.ru2.sixAction a v = v := by
  obtain ⟨k, hk⟩ := d.toTypeRuSetup.alternatingMap_surjective a
  obtain ⟨q, hq⟩ := d.ru2.six.onto (Multiplicative.ofAdd v)
  have hq' : (d.ru2.six.coordinates q).toAdd = v := congrArg Multiplicative.toAdd hq
  have hqC : (q : G) ∈ d.toTypeRuSetup.HC :=
    (head.sixProjection_kernel_coordinates d q).mp (hq'.symm ▸ hv)
  have he := (six_commutator_mem_U_iff d (inclusion d.toTypeRuSetup.K_le_H k) q).mp
    (hfixed q hqC k k.property)
  rw [hq'] at he
  have hka := congrArg Subtype.val hk
  exact hka ▸ he

theorem NaturalHead.quaternion_moved_of_kernel_moved
    (B : Sylow 3 d.toTypeRuSetup.L₁) (cp : CentralProductData d.toTypeRuSetup B)
    (i : d.toTypeRuSetup.H)
    (hmoved : ∃ v ∈ (head.sixProjection d).ker,
      d.ru2.sixAction (d.ru2.quotientMap i) v ≠ v) :
    ∃ q ∈ HB d.toTypeRuSetup B, ⁅(i : G), q⁆ ∉ d.toTypeRuSetup.Z := by
  obtain ⟨v, hv, hvi⟩ := hmoved
  obtain ⟨q, hq⟩ := d.ru2.six.onto (Multiplicative.ofAdd v)
  have hq' : (d.ru2.six.coordinates q).toAdd = v := congrArg Multiplicative.toAdd hq
  have hqC := (head.sixProjection_kernel_coordinates d q).mp (hq'.symm ▸ hv)
  have himage :
      (d.toTypeRuSetup.HC.subgroupOf d.toTypeRuSetup.Q).map d.ru2.six.coordinates =
        ((HB d.toTypeRuSetup B).subgroupOf d.toTypeRuSetup.Q).map d.ru2.six.coordinates := by
    have hU : (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.Q).map
        d.ru2.six.coordinates = ⊥ := by
      rw [← d.ru2.six.kernel_eq]
      exact Subgroup.map_ker_self _
    rw [cp.product_eq, subgroupOf_sup (show HB d.toTypeRuSetup B ≤ d.toTypeRuSetup.Q from
      inf_le_left) d.ru2.six.kernel_le, Subgroup.map_sup, hU, sup_bot_eq]
  have hmem : d.ru2.six.coordinates q ∈
      ((HB d.toTypeRuSetup B).subgroupOf d.toTypeRuSetup.Q).map d.ru2.six.coordinates := by
    rw [← himage]
    exact mem_map.mpr ⟨q, hqC, rfl⟩
  obtain ⟨b, hb, hbe⟩ := hmem
  refine ⟨b, hb, ?_⟩
  intro hZ
  have he := (six_commutator_mem_U_iff d i b).mp (d.ru2.natural.kernel_le hZ)
  rw [hbe, hq'] at he
  exact hvi he

end CFSG.Quasithin.ChapterJ.Fusion.Outer
