module
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeCovers
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeSymplectic
public import CFSG.Quasithin.ChapterG.Section11.WholeG2
public import CFSG.Quasithin.ChapterG.Section11.WholeAlternating
public import CFSG.Quasithin.ChapterG.Section11.WholeSporadic

/-!
# Three small carriers remaining for a large whole component

Apply the literal G.9 carrier list, excluding central covers, nonbinary
linear and symplectic groups, nonbinary G2, and the sporadic rows.
The remaining component is A7, A8 or G2(2) derived, with an actual
isomorphism. Recognition and the original HS markings discharge these
three rows in the source consumer; no strict-intersection data are used.
Source: Aschbacher--Smith G.9.3, G.11.7, 14.3.24, pp.354,368,1000.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section11.LargeWhole
open Section09 Section09.DefiningCharacteristic Chapter1.Section02.LocalModels

/-- Each remaining carrier is tied to the original whole component. -/
inductive SmallCarrier (L : Type*) [Group L] : Prop
  | seven (e : Nonempty (L ≃* alternatingGroup (Fin 7)))
  | eight (e : Nonempty (L ≃* alternatingGroup (Fin 8)))
  | binary_g2 (e : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))))

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X L : Subgroup G}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple ρ X L L
      (finrank (ZMod 2) (Additive X)))

include h h9

private theorem not_five (hw : LowRankWitness ρ v X) (hd : 6 ≤ finrank (ZMod 2) V)
    (e : L ≃* alternatingGroup (Fin 5)) : False := by
  let k := GaloisField 2 2
  have hc : Nat.card k = 4 := by
    change Nat.card (GaloisField 2 2) = 4
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact WholeRankOne.not_projective_binary_rank_one h h9 hw hd
    (n := 2) (by decide) ⟨k,inferInstance,inferInstance,hc,⟨e.trans f.symm⟩⟩

private theorem alternating_cases (hw : LowRankWitness ρ v X)
    (hd : 6 ≤ finrank (ZMod 2) V) {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 8)
    (e : L ≃* alternatingGroup (Fin n)) : SmallCarrier L := by
  have hn' : n=5 ∨ n=6 ∨ n=7 ∨ n=8 := by omega
  rcases hn' with rfl | rfl | rfl | rfl
  · exact (not_five h h9 hw hd e).elim
  · exact (WholeAlternating.not_six h9 hd e).elim
  · exact .seven ⟨e⟩
  · exact .eight ⟨e⟩

private theorem not_odd_two (hw : LowRankWitness ρ v X)
    (hd : 6 ≤ finrank (ZMod 2) V) {p a : ℕ}
    (hp : p.Prime) (ho : Odd p) (ha : 0<a)
    (model : ClassicalGroup.IsPSL L 2 (p^a)) : False := by
  let : IsQuasisimple L := h9.component.2
  rcases Section07.OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h9.faithful.comp L.subtype_injective)
    hp ho ha model h9.single_component_degree_bound with hb | ht | he
  · exact WholeRankOne.not_projective_binary_rank_one h h9 hw hd (n := 2) (by decide) hb
  · exact WholeLinearThree.not_binary_model h9 (selfDual h) (n := 1) (by decide)
      (.inl (by simpa using ht))
  · exact WholeAlternating.not_six h9 hd (he.some.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))

omit h in
private theorem odd_three {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (model : Section07.OddCharacteristic.IsLinearUnitaryThree L p) : SmallCarrier L := by
  let : IsQuasisimple L := h9.component.2
  let : IsIrreducible (ρ.comp L.subtype) := h9.irreducible
  obtain ⟨e,_⟩ := Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h9.faithful.comp L.subtype_injective)
    hp ho model h9.single_component_degree_bound
  exact .binary_g2 e

private theorem rank_two (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hd : 6 ≤ finrank (ZMod 2) V)
    (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X))
    (model : WholeComponentCandidates.RankTwo L) : SmallCarrier L := by
  rcases model with ⟨n,hn,hm⟩ | ⟨n,hn,hm⟩ | ⟨n,hn,hm⟩ | he | he
  · exact (WholeLinearThree.not_binary_model h9 (selfDual h) hn (.inl hm)).elim
  · exact (not_nonbinary_symplectic h hS hlarge h9 hn hm).elim
  · exact (WholeG2.not_nonbinary_model h h9 hw hn hm).elim
  · exact (WholeAlternating.not_six h9 hd (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).elim
  · exact .binary_g2 he

omit h h9 [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem binary_four (model : ClassicalGroup.IsPSL L 4 2) : SmallCarrier L := by
  obtain ⟨k,_,_,hc,⟨e⟩⟩ := model
  let : Fintype k := Fintype.ofFinite k
  let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hc)
  exact .eight ⟨(e.trans (Atlas.fieldEquivPSL 4 a)).trans
    Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm⟩

/-- The original large-actor and relative Sylow hypotheses leave exactly
these three small component carriers. All covering-center alternatives are excluded. -/
theorem single_small_carrier (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hd : 6 ≤ finrank (ZMod 2) V)
    (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X)) :
    IsSimpleGroup L ∧ SmallCarrier L := by
  rcases WholeComponentCandidates.single_component_candidates h h9 hw hd hlarge with
    ⟨hi,hm⟩ | ⟨hc,hm⟩
  · refine ⟨hi,?_⟩
    rcases hm with ⟨n,hn,e⟩ | ⟨p,a,hp,ho,ha,_,hm⟩ | ⟨p,hp,ho,u,hm⟩ | hm | hm | hm | hm
    · exact alternating_cases h h9 hw hd hn e.some
    · exact (not_odd_two h h9 hw hd hp ho (by rcases ha with rfl | rfl <;> decide) hm).elim
    · apply odd_three h9 hp ho
      cases u with
      | false => exact .inl hm
      | true => exact .inr (.inr (.inl hm))
    · exact rank_two h h9 hw hS hd hlarge hm
    · exact binary_four hm
    · exact (WholeSporadic.not_mathieu_twenty_two h h9 hw hm.some).elim
    · exact (WholeSporadic.not_janko_two h h9 hS hm.some).elim
  · exact (not_single_cover h h9 hlarge
      ((Nat.card_congr hc.some.toEquiv).trans (by simp)) hm).elim
end CFSG.Quasithin.ChapterG.Section11.LargeWhole
