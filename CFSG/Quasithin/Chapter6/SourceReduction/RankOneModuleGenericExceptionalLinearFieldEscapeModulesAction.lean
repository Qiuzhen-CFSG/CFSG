module
public import CFSG.Quasithin.ChapterG.Section02.CentralClosure
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryConjugationSection

/-!
# The literal reduced action on the centralizer span modulo the point

For the original G.2.1 setup, G.2.2 makes the image of U in N_G(V₁)/V₁
reduced and elementary. Its centralizer quotient therefore has trivial
two-core and acts faithfully. The coordinate map below is the original
quotient map on U, with kernel V₁ and the original conjugation action.
The projection kernel is C_H(U/V₁), expressed by its actual commutators.

The Chapter 12 application specializes H to C_G(z) and U to the span of
the cubic plane. No abelianness of U or irreducibility is needed. These
coordinates support the cubic-offender argument, not its missing bound.
Source: Aschbacher--Smith G.2.2 and 5.1.23, printed pp.332,645--646.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
open ChapterG.Section02
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

@[expose] def moduleSubgroup (_h : D.Hypothesis) : Subgroup (D.tilde D.H) :=
  (D.tilde D.U).subgroupOf (D.tilde D.H)

instance module_normal (h : D.Hypothesis) : (moduleSubgroup h).Normal :=
  h.tilde_U_reduced.normal
instance module_elementary (h : D.Hypothesis) : IsElementaryAbelian 2 (moduleSubgroup h) :=
  h.tilde_U_reduced.elementary

abbrev Actor (h : D.Hypothesis) :=
  (D.tilde D.H) ⧸ centralizer (moduleSubgroup h : Set (D.tilde D.H))

@[expose] noncomputable def representation (h : D.Hypothesis) :
    Representation (ZMod 2) (Actor h) (Additive (moduleSubgroup h)) :=
  Representation.NormalElementaryQuotient.representation (moduleSubgroup h)
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

theorem representation_faithful (h : D.Hypothesis) :
    Function.Injective (representation h) :=
  Representation.NormalElementaryQuotient.representation_injective _ _ _ _

theorem actor_core_eq_bot (h : D.Hypothesis) : pCore 2 (Actor h) = ⊥ :=
  h.tilde_U_reduced.quotient_pCore_eq_bot

@[expose] def tildeProjection (h : D.Hypothesis) : D.H →* D.tilde D.H where
  toFun x := ⟨QuotientGroup.mk' (D.V₁.subgroupOf D.G₁) ⟨x, h.H_le x.property⟩,
    ⟨⟨x, h.H_le x.property⟩, x.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (QuotientGroup.mk' (D.V₁.subgroupOf D.G₁))
    (⟨x, h.H_le x.property⟩ : D.G₁) ⟨y, h.H_le y.property⟩)

theorem tildeProjection_surjective (h : D.Hypothesis) :
    Function.Surjective (tildeProjection h) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

@[expose] def projection (h : D.Hypothesis) : D.H →* Actor h :=
  (QuotientGroup.mk' _).comp (tildeProjection h)

theorem projection_surjective (h : D.Hypothesis) : Function.Surjective (projection h) :=
  (QuotientGroup.mk'_surjective _).comp (tildeProjection_surjective h)

@[expose] def coordinates (h : D.Hypothesis) :
    D.U →* Multiplicative (Additive (moduleSubgroup h)) where
  toFun u := Multiplicative.ofAdd (Additive.ofMul
    ⟨tildeProjection h ⟨u, h.U_le_H u.property⟩,
      ⟨⟨u, h.H_le (h.U_le_H u.property)⟩, u.property, rfl⟩⟩)
  map_one' := rfl
  map_mul' x y := by
    apply congrArg Multiplicative.ofAdd
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply Subtype.ext
    exact (QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)).map_mul
      (⟨x, h.H_le (h.U_le_H x.property)⟩ : D.G₁)
      ⟨y, h.H_le (h.U_le_H y.property)⟩

theorem coordinates_surjective (h : D.Hypothesis) : Function.Surjective (coordinates h) := by
  intro v
  obtain ⟨u, hu, he⟩ := v.toAdd.toMul.property
  refine ⟨⟨u, hu⟩, ?_⟩
  apply congrArg Multiplicative.ofAdd
  apply congrArg Additive.ofMul
  apply Subtype.ext
  apply Subtype.ext
  change QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)
    ⟨u, h.H_le (h.U_le_H hu)⟩ = (v.toAdd.toMul.val : D.Tilde)
  exact he

theorem coordinates_kernel (h : D.Hypothesis) :
    (coordinates h).ker = D.V₁.subgroupOf D.U := by
  ext u
  change coordinates h u = 1 ↔ (u : G) ∈ D.V₁
  constructor
  · intro he
    have hh := congrArg (fun w : Multiplicative (Additive (moduleSubgroup h)) =>
      ((w.toAdd.toMul : D.tilde D.H) : D.Tilde)) he
    exact (QuotientGroup.eq_one_iff (N := D.V₁.subgroupOf D.G₁)
      (⟨u, h.H_le (h.U_le_H u.property)⟩ : D.G₁)).mp hh
  · intro hu
    apply congrArg Multiplicative.ofAdd
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := D.V₁.subgroupOf D.G₁)
      (⟨u, h.H_le (h.U_le_H u.property)⟩ : D.G₁)).mpr hu

/-- Literal coordinates retain the span, the point and conjugation by the original overgroup. -/
@[expose] def conjugationSection (h : D.Hypothesis) :
    Representation.BinaryConjugationSection D.H D.U D.V₁
      ((representation h).comp (projection h)) where
  section_le := h.U_le_H
  kernel_le := h.point_le.trans (le_conjugateSpanBy _ _)
  normalized := le_normalizer_conjugateSpanBy _ _
  coordinates := coordinates h
  onto := coordinates_surjective h
  kernel_eq := coordinates_kernel h
  equivariant a u := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change _ = ((representation h (QuotientGroup.mk' _ (tildeProjection h a))
      (coordinates h u).toAdd).toMul : D.tilde D.H)
    change _ = ((Representation.NormalElementaryQuotient.representation (moduleSubgroup h)
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (QuotientGroup.mk' _ (tildeProjection h a)) (coordinates h u).toAdd).toMul : D.tilde D.H)
    rw [Representation.NormalElementaryQuotient.representation_apply]
    apply Subtype.ext
    change QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)
      ((⟨a, h.H_le a.property⟩ : D.G₁) * ⟨u, h.H_le (h.U_le_H u.property)⟩ *
        (⟨a, h.H_le a.property⟩ : D.G₁)⁻¹) = _
    simp only [map_mul, map_inv]
    rfl

/-- The source pointwise section kernel, before any abelian-span assumption. -/
theorem projection_eq_one_iff (h : D.Hypothesis) (x : D.H) :
    projection h x = 1 ↔ ∀ u ∈ D.U, ⁅u, (x : G)⁆ ∈ D.V₁ := by
  rw [projection, MonoidHom.comp_apply, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  let q := QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)
  let xi : D.G₁ := ⟨x, h.H_le x.property⟩
  constructor
  · intro hc u hu
    let ui : D.G₁ := ⟨u, h.H_le (h.U_le_H hu)⟩
    let v : moduleSubgroup h :=
      ⟨tildeProjection h ⟨u, h.U_le_H hu⟩, ⟨ui, hu, rfl⟩⟩
    have hh : q ui * q xi = q xi * q ui :=
      congrArg Subtype.val (hc v v.property)
    have he : q ⁅ui, xi⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hh
    exact (QuotientGroup.eq_one_iff (N := D.V₁.subgroupOf D.G₁) ⁅ui, xi⁆).mp he
  · intro hc v hv
    obtain ⟨u, hu, he⟩ := hv
    apply Subtype.ext
    change (v : D.Tilde) * q xi = q xi * (v : D.Tilde)
    change q u = (v : D.Tilde) at he
    rw [← he]
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := D.V₁.subgroupOf D.G₁) ⁅u, xi⁆).mpr
      (hc u hu)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
