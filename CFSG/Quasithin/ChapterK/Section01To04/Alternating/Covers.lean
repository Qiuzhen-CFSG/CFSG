module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Contracts
public import Theory.Alternating.OddCentralCovers
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# The actual alternating covers before representation recognition

The normal two-core acts trivially on an irreducible binary module, so
faithfulness kills it. The center is therefore odd. The existing Schur
cover calculation then gives the actual A₆/3.A₆ and A₇/3.A₇ isomorphisms.
The last alternative remains present: excluding FF actions alone does
not exclude the cubic-ratio-at-most-two branch.

The final theorem applies this reduction to the literal component and
action in `Input`. No representation catalogue or B.4.2 conclusion is used.
Source: Aschbacher–Smith, Chapter K introduction and K.1, pp.451–452;
GLS3 Theorem 5.2.3 for the Schur multipliers.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open GLS3.Chapter5.OddCentralCovers

namespace CFSG.Quasithin.ChapterK.Alternating

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- The original restricted action is faithful, so its normal two-core is trivial. -/
theorem component_twoCore_eq_bot (hf : Function.Injective ρ)
    (hi : IsIrreducible (ρ.comp L.subtype)) : pCore 2 L = ⊥ := by
  let := hi
  have hk := normal_p_subgroup_le_ker (ρ.comp L.subtype) (pCore 2 L) pCore_isPGroup
  have hfL : Function.Injective (ρ.comp L.subtype) := hf.comp L.subtype_injective
  have hker : (ρ.comp L.subtype).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr hfL
  exact bot_unique (hk.trans hker.le)

/-- Faithfulness and irreducibility, rather than a representation list, give odd center. -/
theorem component_center_odd (hf : Function.Injective ρ)
    (hi : IsIrreducible (ρ.comp L.subtype)) : Odd (Nat.card (center L)) := by
  have h := PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
    (component_twoCore_eq_bot ρ L hf hi) (center L) le_rfl
  exact Nat.not_even_iff_odd.mp (fun he => h (even_iff_two_dvd.mp he))

/-- The two genuine covers over the six-letter central quotient. -/
theorem six_cover_alternatives [IsQuasisimple L] (hf : Function.Injective ρ)
    (hi : IsIrreducible (ρ.comp L.subtype))
    (e : L ⧸ center L ≃* alternatingGroup (Fin 6)) :
    Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (L ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  rcases odd_center_alternatives 6 (by decide) e (component_center_odd ρ L hf hi)
      with hc | ⟨_, hc⟩
  · exact Or.inl ⟨alternatingEquivOfCenterCardOne 6 e hc⟩
  · exact Or.inr (triple_six_equiv_hexacode e hc)

/-- The seven-letter reduction retains the genuine triple cover for cubic exclusion. -/
theorem seven_cover_alternatives [IsQuasisimple L] (hf : Function.Injective ρ)
    (hi : IsIrreducible (ρ.comp L.subtype))
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7)) :
    Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
      (Nat.card (center L) = 3 ∧ Nonempty (L ≃* TripleSeven)) := by
  rcases odd_center_alternatives 7 (by decide) e (component_center_odd ρ L hf hi)
      with hc | ⟨_, hc⟩
  · exact Or.inl ⟨alternatingEquivOfCenterCardOne 7 e hc⟩
  · exact Or.inr ⟨hc, triple_seven_equiv e hc⟩

/-- Apply the cover reduction to K.1's actual F*(G) and its original action.
The representation recognition owner must still eliminate the last branch. -/
theorem Input.cover_alternatives {K : GroupClass} (h : Input ρ K L) :
    Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (L ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
      (Nat.card (center L) = 3 ∧ Nonempty (L ≃* TripleSeven)) := by
  let := h.quasisimple
  rcases h.quotient with h6 | h7
  · obtain ⟨e⟩ := h6
    rcases six_cover_alternatives ρ L h.faithful h.irreducible e with ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl ha))
  · obtain ⟨e⟩ := h7
    rcases seven_cover_alternatives ρ L h.faithful h.irreducible e with ha | ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inr ha))

end CFSG.Quasithin.ChapterK.Alternating
