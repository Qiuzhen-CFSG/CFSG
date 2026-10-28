module

public import CFSG.Quasithin.ChapterE.Section03.Offenders
public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# Internal fixed-space spans for Chapter 7

The subgroup W used in the equality argument is represented in the actual
ambient group. The binary submodule/subgroup correspondence identifies the
E.3.30 dual core with the H.10.1 span of nonidentity element fixed spaces.
Cardinality then identifies its subgroup quotient rank with the dimension
of the corresponding vector-space quotient. These bridges preserve the
literal induced normalizer action and the ambient inclusion of V.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
E.3.30–31, H.10.1 and 7.5.3–4, printed pp.237–238,392,700.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter7
open Subgroup Representation.BinaryOffender ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] (V : Subgroup G) [IsElementaryAbelian 2 V]

/-- The binary submodule/subgroup correspondence on the actual internal V. -/
noncomputable def moduleSubgroup : Submodule (ZMod 2) (Additive V) ≃o Subgroup V :=
  (AddSubgroup.toZModSubmodule 2).symm.trans AddSubgroup.toSubgroup'

/-- A binary subspace of V, mapped back into the original ambient group. -/
noncomputable def ambientSubmodule (U : Submodule (ZMod 2) (Additive V)) : Subgroup G :=
  (moduleSubgroup V U).map V.subtype

/-- Mapping a span to the ambient group preserves its generating family. -/
theorem ambientSubmodule_iSup {ι : Sort*} (U : ι → Submodule (ZMod 2) (Additive V)) :
    ambientSubmodule V (⨆ i, U i) = ⨆ i, ambientSubmodule V (U i) := by
  simp only [ambientSubmodule, (moduleSubgroup V).map_iSup, Subgroup.map_iSup]

/-- Every ambient image of a subspace stays inside V. -/
theorem ambientSubmodule_le (U : Submodule (ZMod 2) (Additive V)) :
    ambientSubmodule V U ≤ V := Subgroup.map_subtype_le _

private theorem fixedSpace_subgroup (I : Subgroup (Automizer V)) (p : I) :
    actionCentralizer ((Automizer V).subtype.comp I.subtype) (zpowers p) =
      moduleSubgroup V (fixedSpace (automizerRepresentation V) (zpowers (p : Automizer V))) := by
  ext v
  constructor
  · intro h
    change ∀ a : zpowers (p : Automizer V), automizerRepresentation V a.val (Additive.ofMul v) = _
    intro a
    have ha : (a : Automizer V) ∈ (zpowers p).map I.subtype := by
      simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype] using a.property
    obtain ⟨b, hb, he⟩ := ha
    change ((a : Automizer V) : MulAut V) v = v
    rw [← he]
    exact h b hb
  · intro h x hx
    change automizerRepresentation V (x : Automizer V) (Additive.ofMul v) = Additive.ofMul v
    exact h ⟨x, by simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype] using mem_map_of_mem I.subtype hx⟩

/-- E.3.30 at rank minus one agrees with the H.10.1 fixed-space span. -/
theorem automizerDualCore_eq_fixedSpaceSpan [Finite G]
    (I : Subgroup (Automizer V)) [IsElementaryAbelian 2 I] (hpos : 0 < rank I) :
    automizerDualCore V I (rank I - 1) =
      ambientSubmodule V (fixedSpaceSpan (automizerRepresentation V) I) := by
  rw [automizerDualCore, show rank I = Nat.log 2 (Nat.card I) from rfl,
    dualGeneratedCore_eq_involution_fixed _ hpos]
  simp only [Subgroup.map_iSup, fixedSpace_subgroup]
  simp only [fixedSpaceSpan, ambientSubmodule_iSup]
  apply le_antisymm
  · refine iSup_le fun p => iSup_le fun hp => ?_
    have hp1 : (p : Automizer V) ≠ 1 := by
      intro he
      have : p = 1 := Subtype.ext he
      simp [this] at hp
    exact le_iSup_of_le (p : Automizer V) (le_iSup_of_le p.property (le_iSup_of_le hp1 le_rfl))
  · refine iSup_le fun p => iSup_le fun hp => iSup_le fun hp1 => ?_
    have ho : orderOf (⟨p, hp⟩ : I) = 2 := orderOf_eq_prime
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 I) _)
      (fun he => hp1 (congrArg Subtype.val he))
    exact le_iSup_of_le (⟨p, hp⟩ : I) (le_iSup_of_le ho le_rfl)

/-- The ambient image has the same binary rank as the subspace. -/
theorem ambientSubmodule_log_card [Finite G]
    (U : Submodule (ZMod 2) (Additive V)) :
    Nat.log 2 (Nat.card (ambientSubmodule V U)) = Module.finrank (ZMod 2) U := by
  rw [ambientSubmodule, Subgroup.card_map_of_injective V.subtype_injective]
  have hc : Nat.card (moduleSubgroup V U) = Nat.card U := rfl
  rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.log_pow (by decide)]

/-- Binary rank of V is its vector-space dimension. -/
theorem log_card_eq_finrank [Finite G] :
    Nat.log 2 (Nat.card V) = Module.finrank (ZMod 2) (Additive V) := by
  have hc : Nat.card V = Nat.card (Additive V) := rfl
  rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.log_pow (by decide)]

/-- Actual subgroup quotient rank agrees with subspace quotient dimension. -/
theorem ambientSubmodule_corank [Finite G]
    (U : Submodule (ZMod 2) (Additive V)) :
    subgroupCorank V (ambientSubmodule V U) =
      Module.finrank (ZMod 2) (Additive V ⧸ U) := by
  rw [subgroupCorank, ← Subgroup.log_card_sub_log_card_eq_log_relIndex V _
    (ambientSubmodule_le V U), log_card_eq_finrank, ambientSubmodule_log_card]
  have h := U.finrank_quotient_add_finrank
  omega


variable [Finite G]

/-- The same subgroup W in the ambient group and in the actual automizer module. -/
noncomputable def offenderFixedSpan (g : G) : Subgroup G :=
  ambientSubmodule V (fixedSpaceSpan (automizerRepresentation V)
    (inducedAutomizer V (offenderNormalizer V g)))

omit [Finite G] in
/-- The offender fixed-space span lies in V. -/
theorem offenderFixedSpan_le (g : G) : offenderFixedSpan V g ≤ V :=
  ambientSubmodule_le V _

/-- The quotient by the offender span uses the literal automizer action. -/
theorem offenderFixedSpan_corank (g : G) :
    subgroupCorank V (offenderFixedSpan V g) =
      Module.finrank (ZMod 2) (Additive V ⧸ fixedSpaceSpan (automizerRepresentation V)
        (inducedAutomizer V (offenderNormalizer V g))) :=
  ambientSubmodule_corank V _

omit [Finite G] in
/-- Fixed vectors of an induced action give precisely the relative centralizer. -/
theorem ambientSubmodule_fixedSpace (V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hA : A ≤ normalizer (V : Set G)) :
    ambientSubmodule V (fixedSpace (automizerRepresentation V) (inducedAutomizer V A)) =
      V ⊓ centralizer (A : Set G) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, (mem_fixedSpace_inducedAutomizer V A hA (Additive.ofMul x)).mp hx⟩
  · rintro ⟨hv, hc⟩
    exact ⟨⟨v, hv⟩, (mem_fixedSpace_inducedAutomizer V A hA _).mpr hc, rfl⟩


end CFSG.Quasithin.Chapter7
