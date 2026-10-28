module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.GroupTheory.PerfectNormalizerLift
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField
public import Theory.SpecificGroups.PSL3Three.InnerFourGeneration

/-!
# Inner four-group fixed spaces in degree twelve

Two conjugates of any inner four-group generate the component. The concrete
SL₃(3) statement is transported through the actual coefficient-field and
central-quotient isomorphisms. A central involution would be trivial by
faithfulness and binary irreducibility, so the four-group embeds in the
quotient. Perfectness lifts generation without any assumption on the Schur
multiplier. The two conjugate fixed spaces have zero intersection and equal
dimension, giving the bound six in dimension twelve.

This proves the inner premise of `TwelveFixedSpaces.source_bounds_of_local_calculations`.
It uses neither a cubic-ratio bound nor absolute irreducibility on the component.
Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.2,
manuscript pp.9--10; the generation argument replaces the source's local
C₂ × S₃ calculation.
-/

public section
set_option backward.isDefEq.respectTransparency false

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces
variable {G V S : Type*} [Group G] [Group S] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem lift_two_conjugates
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [Group.IsPerfect L]
    [IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ)
    (e : L ⧸ center L ≃* S)
    (hgen : ∀ B : Subgroup S, IsElementaryAbelian 2 B → Nat.card B = 4 →
      ∃ s : S, B ⊔ B.map (MulAut.conj s).toMonoidHom = ⊤)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hAL : A ≤ L) (hr : rank A = 2) :
    ∃ l : L, L ≤ A ⊔ A.map (MulAut.conj (l : G)).toMonoidHom := by
  let : IsElementaryAbelian 2 A := hA.2
  let C := A.subgroupOf L
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf hAL
  let q : L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hqsur : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker ≤ center L := by
    intro x hx
    have he : QuotientGroup.mk' (center L) x = 1 := by
      apply e.injective
      exact (show e (QuotientGroup.mk' (center L) x) = 1 from hx).trans (map_one e).symm
    rw [← QuotientGroup.ker_mk' (center L)]
    exact he
  have hCinj : Function.Injective (q.comp C.subtype) := by
    apply (q.comp C.subtype).ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ L hf
    · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) ((x : L) : G) x.property
    · have hz : (x : L) ∈ center L := hker hx
      intro y hy
      exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)
  let B := C.map q
  let f : C →* B := (q.comp C.subtype).codRestrict B
    (fun c => mem_map_of_mem q c.property)
  have hCB : Nonempty (C ≃* B) := by
    refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩⟩
    · intro x y he
      exact hCinj (congrArg Subtype.val he)
    · rintro ⟨b, c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have hcard : Nat.card B = 4 := by
    rw [← Nat.card_congr hCB.some.toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv, hA.card_eq_two_pow_rank, hr]
    decide
  obtain ⟨s, hs⟩ := hgen B (IsElementaryAbelian.map q) hcard
  obtain ⟨l, hl⟩ := hqsur s
  let J := C ⊔ C.map (MulAut.conj l).toMonoidHom
  have hmap : (C.map (MulAut.conj l).toMonoidHom).map q =
      B.map (MulAut.conj s).toMonoidHom := by
    rw [map_map, map_map]
    apply congrArg (fun f : L →* S => C.map f)
    apply MonoidHom.ext
    intro x
    change q (l * x * l⁻¹) = s * q x * s⁻¹
    rw [map_mul, map_mul, map_inv, hl]
  have hJ : J = ⊤ := by
    apply top_unique
    apply le_of_map_le_of_perfect q hker ⊤ J
    change (⊤ : Subgroup L).map q ≤ (C ⊔ C.map (MulAut.conj l).toMonoidHom).map q
    rw [Subgroup.map_sup, hmap, hs]
    exact le_top
  refine ⟨l, ?_⟩
  have hsub : (C.map (MulAut.conj l).toMonoidHom).map L.subtype =
      A.map (MulAut.conj (l : G)).toMonoidHom := by
    have hcomp : L.subtype.comp (MulAut.conj l).toMonoidHom =
        (MulAut.conj (l : G)).toMonoidHom.comp L.subtype := by
      apply MonoidHom.ext
      intro x
      rfl
    rw [map_map, hcomp, ← map_map, map_subgroupOf_eq_of_le hAL]
  have hm := congrArg (Subgroup.map L.subtype) hJ
  rw [show J = C ⊔ C.map (MulAut.conj l).toMonoidHom from rfl, Subgroup.map_sup,
    hsub, map_subgroupOf_eq_of_le hAL, ← MonoidHom.range_eq_map, L.range_subtype] at hm
  exact hm.ge

omit [Finite G] in
private theorem dimension_of_two_conjugates
    (ρ : Representation (ZMod 2) G V) (L A : Subgroup G)
    (hfix : fixedSpace ρ L = ⊥) (g : G)
    (hgen : L ≤ A ⊔ A.map (MulAut.conj g).toMonoidHom) :
    2 * Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ Module.finrank (ZMod 2) V := by
  let B := A.map (MulAut.conj g).toMonoidHom
  have hi : fixedSpace ρ A ⊓ fixedSpace ρ B = ⊥ := by
    change invariants (ρ.comp A.subtype) ⊓ invariants (ρ.comp B.subtype) = ⊥
    rw [← ρ.invariants_comp_sup A B]
    apply le_bot_iff.mp
    rw [← hfix]
    exact ρ.invariants_comp_subtype_antitone hgen
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ A) (fixedSpace ρ B)
  rw [hi, finrank_bot, add_zero] at hd
  have hle := Submodule.finrank_le (fixedSpace ρ A ⊔ fixedSpace ρ B)
  have he := (fixedSpaceConjEquiv ρ A g).finrank_eq
  change Module.finrank (ZMod 2) (fixedSpace ρ A) =
    Module.finrank (ZMod 2) (fixedSpace ρ B) at he
  omega


variable (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h
omit [FiniteDimensional (ZMod 2) V] in
/-- Two inner conjugates of an inner four-group generate the actual component.
The central kernel is retained; no multiplier calculation is needed. -/
theorem source_two_conjugates_inner_four
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 3)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hAL : A ≤ generalizedFitting G)
    (hr : rank A = 2) :
    ∃ l : generalizedFitting G,
      generalizedFitting G ≤ A ⊔ A.map (MulAut.conj (l : G)).toMonoidHom := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  obtain ⟨F, hF, hfin, hc, ⟨f⟩⟩ := hm
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)
  let eSL : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Matrix.PSL3Three.SL :=
    f.trans ((Atlas.fieldEquivPSL 3 e).trans Matrix.PSL3Three.equiv.symm)
  apply lift_two_conjugates ρ (generalizedFitting G) h.faithful eSL ?_ A hA hAL hr
  intro B hB hcard
  let := hB
  exact Matrix.PSL3Three.InnerFourGeneration.exists_conjugate_sup_eq_top B hcard

/-- The inner four-group clause in the degree-twelve fixed-space calculation
of GM02 Proposition 4.2, under the original binary source hypotheses. -/
theorem source_inner_four_fixedSpace_le_six
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 3)
    (hd : Module.finrank (ZMod 2) V = 12)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hAL : A ≤ generalizedFitting G)
    (hr : rank A = 2) : Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 6 := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  let : Nontrivial (generalizedFitting G) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
  obtain ⟨l, hl⟩ := source_two_conjugates_inner_four ρ h hm A hA hAL hr
  have hb := dimension_of_two_conjugates ρ (generalizedFitting G) A
    (fixedSpace_eq_bot_of_faithful_irreducible_on ρ (generalizedFitting G)
      h.faithful h.irreducible) (l : G) hl
  omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces
