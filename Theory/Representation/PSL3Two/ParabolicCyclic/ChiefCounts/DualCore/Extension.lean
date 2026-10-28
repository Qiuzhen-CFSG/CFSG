module

public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags

/-!
# Noncentral chief counts in an extension

The invariant subspaces of a subrepresentation identify with the lower
interval of the ambient invariant-subspace lattice. Those of its literal
quotient identify with the upper interval. These identifications preserve
covers and displacement centrality. Lifting and concatenating complete flags
therefore adds their noncentral counts, without assuming a splitting.

The application in `DualCore` uses the exact Fano core sequence of
Aschbacher–Smith H.5.3(1–2) to establish the core count in 14.7.22(2).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts
variable {G M : Type*} [_root_.Group G] [AddCommGroup M] [Module (ZMod 2) M]
  {ρ : Representation (ZMod 2) G M} (K : Subrepresentation ρ)

private def subNode (U : Subrepresentation K.toRepresentation) : Subrepresentation ρ where
  toSubmodule := U.toSubmodule.map K.toSubmodule.subtype
  apply_mem_toSubmodule g _ hv := by
    obtain ⟨v, hv, rfl⟩ := hv
    exact ⟨K.toRepresentation g v, U.apply_mem_toSubmodule g hv, rfl⟩

private def subPull (U : Subrepresentation ρ) : Subrepresentation K.toRepresentation where
  toSubmodule := U.toSubmodule.comap K.toSubmodule.subtype
  apply_mem_toSubmodule g _ hv := U.apply_mem_toSubmodule g hv

private def subOrderIso : Subrepresentation K.toRepresentation ≃o Set.Iic K where
  toFun U := ⟨subNode K U, K.toSubmodule.map_subtype_le U.toSubmodule⟩
  invFun U := subPull K U.val
  left_inv U := Subrepresentation.toSubmodule_injective
    (Submodule.comap_map_eq_of_injective K.toSubmodule.subtype_injective U.toSubmodule)
  right_inv U := by
    apply Subtype.ext
    apply Subrepresentation.toSubmodule_injective
    exact (Submodule.map_comap_subtype _ _).trans (inf_eq_right.mpr U.property)
  map_rel_iff' := by
    intro U V
    exact Submodule.map_le_map_iff_of_injective K.toSubmodule.subtype_injective _ _

private def quotNode (U : Subrepresentation K.quotientRepresentation) : Subrepresentation ρ where
  toSubmodule := U.toSubmodule.comap K.toSubmodule.mkQ
  apply_mem_toSubmodule g _ hv := U.apply_mem_toSubmodule g hv

private def quotOrderIso : Subrepresentation K.quotientRepresentation ≃o Set.Ici K where
  toFun U := ⟨quotNode K U, K.toSubmodule.le_comap_mkQ U.toSubmodule⟩
  invFun U := K.quotientImage U.val
  left_inv U := Subrepresentation.toSubmodule_injective
    (Submodule.map_comap_eq_of_surjective K.toSubmodule.mkQ_surjective U.toSubmodule)
  right_inv U := by
    apply Subtype.ext
    apply Subrepresentation.toSubmodule_injective
    exact (Submodule.comap_map_mkQ _ _).trans (sup_eq_right.mpr U.property)
  map_rel_iff' := by
    intro U V
    exact Submodule.comap_le_comap_iff_of_surjective K.toSubmodule.mkQ_surjective

private theorem subNode_covBy {U V : Subrepresentation K.toRepresentation} (h : U ⋖ V) :
    subNode K U ⋖ subNode K V := by
  have hc := (apply_covBy_apply_iff (subOrderIso K)).mpr h
  refine ⟨hc.lt, ?_⟩
  intro P hUP hPV
  exact hc.2 (c := ⟨P, hPV.le.trans (subOrderIso K V).property⟩) hUP hPV

private theorem quotNode_covBy {U V : Subrepresentation K.quotientRepresentation} (h : U ⋖ V) :
    quotNode K U ⋖ quotNode K V := by
  have hc := (apply_covBy_apply_iff (quotOrderIso K)).mpr h
  refine ⟨hc.lt, ?_⟩
  intro P hUP hPV
  exact hc.2 (c := ⟨P, (quotOrderIso K U).property.trans hUP.le⟩) hUP hPV

private theorem central_subNode (U V : Subrepresentation K.toRepresentation) :
    Central (subNode K U) (subNode K V) ↔ Central U V := by
  constructor
  · intro h g v hv
    obtain ⟨w, hw, he⟩ := h g v.val ⟨v, hv, rfl⟩
    have he' : w = K.toRepresentation g v - v := Subtype.ext he
    exact he' ▸ hw
  · intro h g v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨K.toRepresentation g w - w, h g w hw, rfl⟩

private theorem central_quotNode (U V : Subrepresentation K.quotientRepresentation) :
    Central (quotNode K U) (quotNode K V) ↔ Central U V := by
  constructor
  · intro h g v hv
    obtain ⟨w, rfl⟩ := K.toSubmodule.mkQ_surjective v
    have hh := h g w hv
    change K.toSubmodule.mkQ (ρ g w - w) ∈ U at hh
    simpa only [Subrepresentation.quotientRepresentation_mk, map_sub] using hh
  · intro h g v hv
    change K.toSubmodule.mkQ (ρ g v - v) ∈ U
    simpa only [Subrepresentation.quotientRepresentation_mk, map_sub] using h g (K.toSubmodule.mkQ v) hv

private def subSeries (s : Series K.toRepresentation) : Series ρ :=
  ⟨s.length, fun i => subNode K (s i), fun i => subNode_covBy K (s.step i)⟩

private def quotSeries (s : Series K.quotientRepresentation) : Series ρ :=
  ⟨s.length, fun i => quotNode K (s i), fun i => quotNode_covBy K (s.step i)⟩

private theorem subSeries_count (s : Series K.toRepresentation) :
    (subSeries K s).count = s.count := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun i => not_congr (central_subNode K _ _)

private theorem quotSeries_count (s : Series K.quotientRepresentation) :
    (quotSeries K s).count = s.count := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun i => not_congr (central_quotNode K _ _)

/-- Lift a complete flag from a subrepresentation and a complete flag from its
literal quotient. Their concatenation adds the noncentral chief counts;
no splitting of the representation is required. -/
theorem HasCount.of_subrepresentation {a b : ℕ}
    (hK : HasCount K.toRepresentation a) (hQ : HasCount K.quotientRepresentation b) :
    HasCount ρ (a + b) := by
  obtain ⟨s, hs0, hs1, hsc⟩ := hK
  obtain ⟨t, ht0, ht1, htc⟩ := hQ
  have hst : (subSeries K s).last = (quotSeries K t).head := by
    change subNode K s.last = quotNode K t.head
    rw [hs1, ht0]
    apply Subrepresentation.toSubmodule_injective
    change Submodule.map K.toSubmodule.subtype ⊤ = Submodule.comap K.toSubmodule.mkQ ⊥
    rw [Submodule.map_subtype_top, Submodule.comap_bot, Submodule.ker_mkQ]
  refine ⟨(subSeries K s).smash (quotSeries K t) hst, ?_, ?_, ?_⟩
  · rw [RelSeries.head_smash]
    change subNode K s.head = ⊥
    rw [hs0]
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_bot _
  · rw [RelSeries.last_smash]
    change quotNode K t.last = ⊤
    rw [ht1]
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.comap_top _
  · rw [Series.count_smash, subSeries_count, quotSeries_count, hsc, htc]
end BinaryLinearThree.ParabolicCyclic.ChiefCounts
