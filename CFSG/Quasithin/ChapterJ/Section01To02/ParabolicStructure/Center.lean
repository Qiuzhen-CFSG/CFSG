module

public import CFSG.Quasithin.ChapterJ.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Preliminaries
public import Theory.Representation.PSL3Two.NaturalSylowFixed

/-!
# The center and Sylow arrangement in J.2.1

Faithfulness of the natural Ru1 action gives C_G(V) = S, and the special
core then gives C_G(S) = V. The source Sylow choice implies S ≤ T, hence
Z(T) = C_V(T), before any use of T ≤ L. Coordinates embed this center
in the fixed space of the image Sylow on the natural binary three-space.
That space has at most two vectors; the nontrivial center of the two-group
T gives equality. The order and elementary-abelian preliminaries now yield
T ≤ L and the actual U ≃ E₃₂ identification in J.2.2(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas J.2.1 and J.2.2(2), printed p.432 (PDF p.443).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ
open Subgroup Representation
variable {G : Type*} [Group G]

/-- The faithful natural Ru1 action identifies the full centralizer of V. -/
theorem RuOne.centralizer_V {L V : Subgroup G} (r : RuOne L V) :
    centralizer (V : Set G) = L.pCoreIn 2 := by
  apply le_antisymm
  · intro x hx
    have hxL : x ∈ L := by
      rw [r.normalizer_eq]
      exact Subgroup.centralizer_le_normalizer _ hx
    have hf : BinaryLinearThree.W (r.quotientMap ⟨x, hxL⟩) = 1 := by
      apply LinearMap.ext
      intro v
      obtain ⟨a, ha⟩ := r.natural.onto (Multiplicative.ofAdd v)
      have he := r.natural.equivariant ⟨x, hxL⟩ a
      have hxa : x * (a : G) * x⁻¹ = a := by
        rw [← hx a a.property, mul_inv_cancel_right]
      have heq : (⟨x * (a : G) * x⁻¹, by rw [hxa]; exact a.property⟩ : V) = a := Subtype.ext hxa
      rw [heq, ha] at he
      exact he.symm
    have hk : (⟨x, hxL⟩ : L) ∈ r.quotientMap.ker := by
      apply BinaryLinearThree.natural_injective
      simpa only [map_one] using hf
    rw [r.quotient_kernel] at hk
    exact hk
  · intro x hx v hv
    rw [← r.center_eq] at hv
    obtain ⟨v, hv, rfl⟩ := hv
    exact (congrArg (fun a : L.pCoreIn 2 => (a : G))
      ((mem_center_iff.mp hv) ⟨x, hx⟩)).symm

/-- The center of the special core is contained in that core. -/
theorem RuOne.V_le_S {L V : Subgroup G} (r : RuOne L V) : V ≤ L.pCoreIn 2 := by
  rw [← r.center_eq]
  exact map_subtype_le _

/-- In the source-compatible Sylow arrangement the core lies in T. -/
theorem LocalSetup.S_le_T [Finite G] (d : LocalSetup G) :
    d.toTypeRuSetup.S ≤ (d.T : Subgroup G) := by
  have h := pCoreIn_le_sylow d.L d.sylowInL
  rw [← d.intersection_eq] at h
  exact h.trans inf_le_left

/-- The centralizer of the special core is precisely its center. -/
theorem RuOne.centralizer_S {L V : Subgroup G} (r : RuOne L V) :
    centralizer (L.pCoreIn 2 : Set G) = V := by
  apply le_antisymm
  · intro x hx
    have hxS : x ∈ L.pCoreIn 2 := by
      rw [← r.centralizer_V]
      exact centralizer_le r.V_le_S hx
    rw [← r.center_eq]
    refine mem_map.mpr ⟨⟨x, hxS⟩, ?_, rfl⟩
    exact mem_center_iff.mpr (fun s => Subtype.ext (hx s s.property))
  · intro x hx s hs
    rw [← r.center_eq] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    exact congrArg (fun a : L.pCoreIn 2 => (a : G)) ((mem_center_iff.mp hx) ⟨s, hs⟩)

/-- The center equality in J.2.1, proved before using T ≤ L. -/
theorem LocalSetup.center_eq [Finite G] (d : LocalSetup G) :
    d.toTypeRuSetup.Z = d.V ⊓ centralizer ((d.T : Subgroup G) : Set G) := by
  have hVS : d.V ≤ d.toTypeRuSetup.S := d.ru1.V_le_S
  have hVT := hVS.trans d.S_le_T
  apply le_antisymm
  · intro z hz
    obtain ⟨z, hz, rfl⟩ := hz
    have hzc : (z : G) ∈ centralizer ((d.T : Subgroup G) : Set G) :=
      fun t ht => congrArg (fun a : d.T => (a : G)) ((mem_center_iff.mp hz) ⟨t, ht⟩)
    refine ⟨?_, hzc⟩
    rw [← d.ru1.centralizer_S]
    exact centralizer_le d.S_le_T hzc
  · intro z hz
    refine mem_map.mpr ⟨⟨z, hVT hz.1⟩, ?_, rfl⟩
    exact mem_center_iff.mpr (fun t => Subtype.ext (hz.2 t t.property))


/-- The center-order assertion of J.2.1, without a T ≤ L premise. -/
theorem LocalSetup.card_Z [Finite G] (d : LocalSetup G) :
    Nat.card d.toTypeRuSetup.Z = 2 := by
  let P := d.sylowInL.mapSurjective d.ru1.quotient_surjective
  have hZV : d.toTypeRuSetup.Z ≤ d.V := d.center_eq.le.trans inf_le_left
  let f : d.toTypeRuSetup.Z →
      BinaryOffender.fixedSpace BinaryLinearThree.W (P : Subgroup BinaryLinearThree.Group) :=
    fun z => ⟨(d.ru1.natural.coordinates ⟨z, hZV z.property⟩).toAdd, by
      intro a
      obtain ⟨p, hp, hpa⟩ := a.property
      have hpT : (p : G) ∈ (d.T : Subgroup G) := by
        have hpm : (p : G) ∈ (d.sylowInL : Subgroup d.L).map d.L.subtype :=
          mem_map.mpr ⟨p, hp, rfl⟩
        rw [← d.intersection_eq] at hpm
        exact hpm.1
      have hzC := (d.center_eq.le z.property).2
      have he := d.ru1.natural.equivariant p ⟨z, hZV z.property⟩
      have heq : p.val * z.val * p.val⁻¹ = z.val := by
        rw [hzC p hpT, mul_inv_cancel_right]
      have hv : (⟨p.val * z.val * p.val⁻¹,
          by rw [heq]; exact hZV z.property⟩ : d.V) = ⟨z, hZV z.property⟩ :=
        Subtype.ext heq
      rw [hv] at he
      change BinaryLinearThree.W (a : BinaryLinearThree.Group) _ = _
      rw [← hpa]
      exact he.symm⟩
  have hi : Function.Injective f := by
    intro x y h
    have hinj : Function.Injective d.ru1.natural.coordinates := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [d.ru1.natural.kernel_eq, bot_subgroupOf]
    have hc := congrArg Subtype.val h
    have hxy := hinj (Multiplicative.toAdd.injective hc)
    have hexy := congrArg Subtype.val hxy
    exact Subtype.ext hexy
  have hu := (Nat.card_le_card_of_injective f hi).trans
    (BinaryLinearThree.card_sylow_natural_fixed_le_two P)
  have hVT := d.ru1.V_le_S.trans d.S_le_T
  have hTcard : 1 < Nat.card d.T := by
    have hv := card_le_of_le hVT
    rw [d.ru1.card_V] at hv
    omega
  let : Fintype d.T := Fintype.ofFinite d.T
  let : Nontrivial d.T := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_eq_fintype_card] using hTcard)
  let : Nontrivial (center d.T) := d.T.isPGroup'.center_nontrivial
  let : Fintype (center d.T) := Fintype.ofFinite (center d.T)
  have hl : 1 < Nat.card d.toTypeRuSetup.Z := by
    change 1 < Nat.card ((center d.T).map (d.T : Subgroup G).subtype)
    rw [card_map_of_injective (d.T : Subgroup G).subtype_injective,
      Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  omega

/-- J.2.1(1). -/
theorem LocalSetup.T_le_L [Finite G] (d : LocalSetup G) : (d.T : Subgroup G) ≤ d.L :=
  d.T_le_L_of_card_Z d.card_Z

/-- J.2.2(2): the literal elementary-abelian group of order 32. -/
theorem LocalSetup.equiv_U [Finite G] (d : LocalSetup G) :
    Nonempty (d.toTypeRuSetup.U ≃* Multiplicative (Fin 5 → ZMod 2)) :=
  d.toTypeRuSetup.equiv_U_of_card_Z d.card_Z

/-- The elementary-abelian instance used in the subsequent commutator argument. -/
theorem LocalSetup.elementary_U [Finite G] (d : LocalSetup G) :
    IsElementaryAbelian 2 d.toTypeRuSetup.U :=
  d.toTypeRuSetup.elementary_U_of_card_Z d.card_Z

end CFSG.Quasithin.ChapterJ