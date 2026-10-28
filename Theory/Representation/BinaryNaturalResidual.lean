module
public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalResidual

/-!
# Point-residual generation in a specified binary natural action

For an actual conjugation action identified with the natural SL₃(2) action,
the point centralizer maps onto the corresponding matrix stabilizer. Finite
surjective transport identifies its two-residual image with the model residual.
Pulling back the model displacements proves that this embedded residual
generates the whole original factor by commutators.

Source: Aschbacher--Smith 10.1.1(3) and the natural-module supplement in the
proof of 10.2.11(3), printed pp.741,754.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryNaturalResidual
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
variable {G : Type*} [Group G] [Finite G]

/-- The literal two-residual of a point centralizer generates the natural
factor by commutators, for any specified surjective equivariant action. -/
theorem natural_factor_le_commutator
    (H A : Subgroup G) (hn : H ≤ normalizer (A : Set G))
    (f : H →* SL) (hf : Function.Surjective f) (e : A ≃* Model)
    (he : ∀ (h : H) (x : A),
      e ⟨h*x*(h : G)⁻¹, (mem_normalizer_iff.mp (hn h.property) x).mp x.property⟩ =
        slAut (f h) (e x))
    (a : A) (ha : a ≠ 1) :
    A ≤ ⁅A, (pResidual 2 (H ⊓ centralizer ({(a : G)} : Set G) : Subgroup G)).map
      (H ⊓ centralizer ({(a : G)} : Set G)).subtype⁆ := by
  let P := H ⊓ centralizer ({(a : G)} : Set G)
  let Q := MulAction.stabilizer SL (e a).toAdd
  have fix_iff (h : H) : f h ∈ Q ↔ (h : G) ∈ centralizer ({(a : G)} : Set G) := by
    constructor
    · intro hh
      have hh' : slAut (f h) (e a) = e a := by
        apply Multiplicative.toAdd.injective
        rw [slAut_apply]
        exact hh
      have hc := congrArg Subtype.val (e.injective ((he h a).trans hh'))
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc)
    · intro hh
      have hc : (⟨h*a*(h : G)⁻¹,
          (mem_normalizer_iff.mp (hn h.property) a).mp a.property⟩ : A) = a := by
        apply Subtype.ext
        change (h : G) * (a : G) * (h : G)⁻¹ = (a : G)
        rw [mem_centralizer_singleton_iff.mp hh, mul_inv_cancel_right]
      change (f h).val.mulVec (e a).toAdd = (e a).toAdd
      rw [← slAut_apply, ← he h a, hc]
  let fP : P →* Q :=
    (f.comp (inclusion inf_le_left)).codRestrict Q
      (fun x => (fix_iff (inclusion inf_le_left x)).mpr x.property.2)
  have hfP : Function.Surjective fP := by
    intro y
    obtain ⟨h,hh⟩ := hf y.val
    have hm : (h : G) ∈ centralizer ({(a : G)} : Set G) :=
      (fix_iff h).mp (hh ▸ y.property)
    exact ⟨⟨h,h.property,hm⟩, Subtype.ext hh⟩
  have hmap : (pResidual 2 P).map (Q.subtype.comp fP) = residual Q := by
    rw [← map_map, map_pResidual_of_surjective 2 fP hfP]
    rfl
  let R := (pResidual 2 P).map P.subtype
  let C := ⁅A,R⁆
  let D := (C.subgroupOf A).map e.toMonoidHom
  have htop : D = ⊤ := by
    apply point_residual_movement (e a) (fun h => ha (e.map_eq_one_iff.mp h))
    intro w g hg
    obtain ⟨h,hh,rfl⟩ := mem_map.mp (hmap.symm ▸ hg)
    obtain ⟨u,rfl⟩ := e.surjective w
    let k : H := inclusion inf_le_left h
    let u' : A := ⟨k*u*(k : G)⁻¹,
      (mem_normalizer_iff.mp (hn k.property) u).mp u.property⟩
    have hC : ((u * u'⁻¹ : A) : G) ∈ C := by
      have hm : (h : G) ∈ R := mem_map_of_mem P.subtype hh
      convert commutator_mem_commutator u.property hm using 1
      change (u : G) * ((h : G) * (u : G) * (h : G)⁻¹)⁻¹ = ⁅(u : G),(h : G)⁆
      simp only [commutatorElement_def]
      group
    refine ⟨u * u'⁻¹, hC, ?_⟩
    change e (u * u'⁻¹) = e u * (slAut (f k) (e u))⁻¹
    rw [map_mul, map_inv, he k u]
  intro x hx
  have hm : e ⟨x,hx⟩ ∈ D := htop ▸ mem_top _
  obtain ⟨y,hy,heq⟩ := mem_map.mp hm
  have hyx : y = ⟨x,hx⟩ := e.injective heq
  change (y : G) ∈ C at hy
  have hyx' : (y : G) = x := congrArg Subtype.val hyx
  change x ∈ C
  rwa [hyx'] at hy

end Representation.BinaryNaturalResidual
