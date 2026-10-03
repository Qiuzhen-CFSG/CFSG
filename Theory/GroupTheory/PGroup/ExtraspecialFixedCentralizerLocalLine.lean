module

public import Theory.GroupTheory.PGroup.NormalExtraspecialDerivedCenter
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProduct

/-!
# Characteristic fixed-core lines from a local abelian quotient

Only the quotient of the element centralizer by its fixed core needs to be
abelian. If that fixed core is extraspecial, its center is the intersection
of the full centralizer's derived group and center. A central involution in
the core generates the resulting line. In particular a nonabelian fixed
core of order eight suffices. The line identity also transports through an
injective ambient homomorphism.

This is the local version of the calculation in Janko–Thompson,
Math. Z. 113 (1970), §4, case (c), printed p.392.
-/

namespace Subgroup

/-- An extraspecial fixed core and an abelian local quotient determine the line. -/
public theorem centralizer_derived_inf_center_line_of_local_quotient {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [H.Normal] (z t : P)
    (hz : orderOf z = 2) (hzc : z ∈ center P) (hzH : z ∈ H)
    [IsExtraspecial 2 (H.subgroupOf (centralizer ({t} : Set P)))]
    [IsMulCommutative ((centralizer ({t} : Set P)) ⧸
      H.subgroupOf (centralizer ({t} : Set P)))] :
    (_root_.commutator (centralizer ({t} : Set P)) ⊓
      center (centralizer ({t} : Set P))).map
      (centralizer ({t} : Set P)).subtype = zpowers z := by
  let E := centralizer ({t} : Set P)
  let D := H.subgroupOf E
  change (_root_.commutator E ⊓ center E).map E.subtype = zpowers z
  rw [derived_inf_center_eq_of_normal_extraspecial D]
  have hzE : z ∈ E := mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzc t).symm
  let zE : E := ⟨z, hzE⟩
  let zD : D := ⟨zE, hzH⟩
  have hzD : zD ∈ center D := by
    apply mem_center_iff.mpr
    intro d
    exact Subtype.ext (Subtype.ext (mem_center_iff.mp hzc d))
  have hle : zpowers z ≤ ((center D).map D.subtype).map E.subtype :=
    zpowers_le.mpr (mem_map_of_mem E.subtype (mem_map_of_mem D.subtype hzD))
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective E.subtype_injective,
    card_map_of_injective D.subtype_injective, IsExtraspecial.center_order_p 2 D,
    Nat.card_zpowers, hz]

end Subgroup

namespace Subgroup

/-- The derived-center line transports through an injective ambient map. -/
public theorem map_derived_inf_center_line {P G : Type*} [Group P] [Group G]
    (f : P →* G) (hf : Function.Injective f) (C : Subgroup P) (z : P)
    (hline : (_root_.commutator C ⊓ center C).map C.subtype = zpowers z) :
    (_root_.commutator (C.map f) ⊓ center (C.map f)).map (C.map f).subtype =
      zpowers (f z) := by
  let e := C.equivMapOfInjective f hf
  have hder : (_root_.commutator C).map e.toMonoidHom =
      _root_.commutator (C.map f) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hcen : (center C).map e.toMonoidHom = center (C.map f) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply mem_center_iff.mpr
      intro v
      obtain ⟨u, rfl⟩ := e.surjective v
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
        congrArg e (mem_center_iff.mp hx u)
    · intro hy
      refine ⟨e.symm y, mem_center_iff.mpr ?_, e.apply_symm_apply y⟩
      intro v
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hy (e v)
  have hcomp : (C.map f).subtype.comp e.toMonoidHom = f.comp C.subtype := rfl
  rw [← hder, ← hcen, ← map_inf _ _ _ e.injective, map_map, hcomp,
    ← map_map, hline, MonoidHom.map_zpowers]


/-- A nonabelian fixed eight determines the line when the local quotient is abelian. -/
public theorem centralizer_derived_inf_center_line_of_nonabelian_eight {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [H.Normal] (z t : P)
    (hz : orderOf z = 2) (hzc : z ∈ center P) (hzH : z ∈ H)
    (hcard : Nat.card (H ⊓ centralizer ({t} : Set P) : Subgroup P) = 8)
    (hnonab : ¬ IsMulCommutative (H ⊓ centralizer ({t} : Set P) : Subgroup P))
    [IsMulCommutative ((centralizer ({t} : Set P)) ⧸
      H.subgroupOf (centralizer ({t} : Set P)))] :
    (_root_.commutator (centralizer ({t} : Set P)) ⊓
      center (centralizer ({t} : Set P))).map
      (centralizer ({t} : Set P)).subtype = zpowers z := by
  let E := centralizer ({t} : Set P)
  let D := H.subgroupOf E
  let e : D ≃* (H ⊓ E : Subgroup P) :=
    (D.equivMapOfInjective E.subtype E.subtype_injective).trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype H E))
  have hDcard : Nat.card D = 8 := (Nat.card_congr e.toEquiv).trans hcard
  have hDnonab : ¬ IsMulCommutative D := by
    intro h
    let := h
    apply hnonab
    exact ⟨⟨fun a b => e.symm.injective (by
      simpa only [map_mul] using mul_comm' (e.symm a) (e.symm b))⟩⟩
  let : IsExtraspecial 2 D := IsExtraspecial.of_noncommutative_card_eight hDcard hDnonab
  exact centralizer_derived_inf_center_line_of_local_quotient H z t hz hzc hzH

end Subgroup
