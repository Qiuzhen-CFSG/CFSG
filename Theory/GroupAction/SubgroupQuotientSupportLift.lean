module

public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# Supports lifted through a subgroup quotient

The preimage of a subgroup of U/Z, included back into the ambient group,
lies in U, contains Z, has cardinality |support| times |Z|, and maps back
onto the original support. For a prescribed literal conjugation action,
lifting commutes with conjugation. Consequently any group preserving the
quotient support normalizes its ambient lift.

The cardinality proof uses the kernel relative-index identity. The
conjugation identity is proved on representatives, retaining the exact
supplied normality and action instances. These are source-neutral quotient
facts used for the four-element factor support in Stellmacher (9.5),
printed pp.52–53 of `refs/files/stellmacher-n-group.pdf`.
-/

open scoped commutatorElement

namespace Subgroup

variable {G : Type*} [Group G]

public theorem lift_support_basic (U Z : Subgroup G) (hZU : Z ≤ U)
    [hN : (Z.subgroupOf U).Normal] (B : Subgroup (U ⧸ Z.subgroupOf U)) :
    let q := QuotientGroup.mk' (Z.subgroupOf U)
    let L := (B.comap q).map U.subtype
    L ≤ U ∧ Z ≤ L ∧
      Nat.card L = Nat.card B * Nat.card Z ∧
      (L.subgroupOf U).map q = B := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let C := B.comap q
  let L := C.map U.subtype
  have hCL : L.subgroupOf U = C :=
    Subgroup.comap_map_eq_self_of_injective U.subtype_injective C
  have hZC : Z.subgroupOf U ≤ C := by
    intro point hpoint
    change q point ∈ B
    have hz : q point = 1 := (QuotientGroup.eq_one_iff _).mpr hpoint
    rw [hz]
    exact B.one_mem
  have hZL : Z ≤ L := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hZU]
    exact Subgroup.map_mono hZC
  have hmap : C.map q = B :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) B
  have hrelative : (Z.subgroupOf U).relIndex C = Nat.card B := by
    have hh := Subgroup.relIndex_ker C q
    rw [show q.ker = Z.subgroupOf U from QuotientGroup.ker_mk' _, hmap] at hh
    exact hh
  have hcardZ : Nat.card ((Z.subgroupOf U).subgroupOf C) = Nat.card Z :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv)
  have hcount := ((Z.subgroupOf U).subgroupOf C).index_mul_card
  change (Z.subgroupOf U).relIndex C *
    Nat.card ((Z.subgroupOf U).subgroupOf C) = Nat.card C at hcount
  rw [hrelative, hcardZ] at hcount
  refine ⟨Subgroup.map_subtype_le C, hZL, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective U.subtype_injective]
    exact hcount.symm
  · rw [hCL]
    exact hmap

end Subgroup

namespace Subgroup

variable {G : Type*} [Group G]

public theorem lift_support_conjugate
    (P U Z : Subgroup G) (hPU : P ≤ normalizer (U : Set G))
    [hN : (Z.subgroupOf U).Normal]
    (action : P →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : ∀ mover : P, ∀ point : U,
      action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩)
    (B : Subgroup (U ⧸ Z.subgroupOf U)) (mover : P) :
    let q := QuotientGroup.mk' (Z.subgroupOf U)
    ((B.comap q).map U.subtype).map (MulAut.conj (mover : G)).toMonoidHom =
      ((B.map (action mover).toMonoidHom).comap q).map U.subtype := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  ext point
  constructor
  · rintro ⟨source, ⟨lift, hlift, rfl⟩, rfl⟩
    let acted : U := ⟨(mover : G) * (lift : G) * (mover : G)⁻¹,
      (mem_normalizer_iff.mp (hPU mover.property) lift).mp lift.property⟩
    refine ⟨acted, ?_, rfl⟩
    change q acted ∈ B.map (action mover).toMonoidHom
    refine ⟨q lift, hlift, ?_⟩
    exact hact mover lift
  · rintro ⟨lift, ⟨image, himage, heq⟩, rfl⟩
    let unacted : U := ⟨(mover : G)⁻¹ * (lift : G) * (mover : G),
      by simpa only [coe_inv, inv_inv] using
        (mem_normalizer_iff.mp (hPU mover⁻¹.property) lift).mp lift.property⟩
    have hq : q unacted = image := by
      apply (action mover).injective
      rw [hact]
      change (action mover) image = q lift at heq
      change q ⟨(mover : G) * ((mover : G)⁻¹ * (lift : G) * (mover : G)) *
        (mover : G)⁻¹, _⟩ = _
      rw [heq]
      congr 1
      apply Subtype.ext
      group
    refine ⟨unacted, ⟨unacted, ?_, rfl⟩, ?_⟩
    · change q unacted ∈ B
      rw [hq]
      exact himage
    · change (mover : G) * ((mover : G)⁻¹ * (lift : G) * (mover : G)) *
        (mover : G)⁻¹ = lift
      group

public theorem lift_support_normalizes
    (P U Z E : Subgroup G) (hEP : E ≤ P)
    (hPU : P ≤ normalizer (U : Set G))
    [hN : (Z.subgroupOf U).Normal]
    (action : P →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : ∀ mover : P, ∀ point : U,
      action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩)
    (B : Subgroup (U ⧸ Z.subgroupOf U))
    (hB : ∀ mover : P, (mover : G) ∈ E →
      B.map (action mover).toMonoidHom = B) :
    E ≤ normalizer (((B.comap (QuotientGroup.mk' (Z.subgroupOf U))).map
      U.subtype : Subgroup G) : Set G) := by
  intro mover hmover
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hh := lift_support_conjugate P U Z hPU action hact B ⟨mover, hEP hmover⟩
  dsimp only at hh
  rw [hB ⟨mover, hEP hmover⟩ hmover] at hh
  exact hh

end Subgroup

