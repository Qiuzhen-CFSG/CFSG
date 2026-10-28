module
public import CFSG.Quasithin.ChapterG.Section11.WholeRankOne
public import CFSG.Quasithin.ChapterG.Section10.Reducible.Solvable
public import CFSG.Quasithin.ChapterG.Section11.WholeG2
public import CFSG.Quasithin.ChapterG.Section11.WholeLinearThree
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.SourceModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.TitsFrobenius
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentModels
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentEvenExclusions
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.Representation.CentralCoverSelfDualFlag
public import Theory.LinearAlgebra.AlternatingFinrank
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.NormalThree

/-!
# Surviving single-component carriers of the original strict action

The full known-simple catalogue is applied to the actual irreducible component.
Self-duality eliminates binary SL₃ and SL₅; even dimension eliminates M₂₄.
The low-displacement witness removes the Bender families and nonbinary G₂.
Moved-plane nontransitivity excludes every central three-cover.
The remaining odd-characteristic models are identified with their actual small
binary carriers, and the other sporadic and twisted rows are excluded by G.9.

The result is a necessary list of literal component isomorphisms. It does not
recognize the remaining modules or assert the final strict contradiction.
`StrictWholeModels` applies it to the original source quotient.
Source: Aschbacher--Smith G.9.3 and G.11.7, printed pp.353--356,366--368.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section11.WholeModels
open Section09 Section09.DefiningCharacteristic Chapter1.Section02.LocalModels

/-- The remaining whole-component carriers, each linked by an actual model
isomorphism. This is a necessary reduction, not an exhaustive action classifier. -/
inductive Remaining (L : Type*) [Group L] : Prop
  | alternating (n : ℕ) (hn : 6 ≤ n ∧ n ≤ 8) (e : Nonempty (L ≃* alternatingGroup (Fin n)))
  | symplectic (n : ℕ) (hn : 2 ≤ n) (model : ClassicalGroup.IsPSp L 2 (2^n))
  | binary_g2 (e : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | mathieu_twelve (e : Nonempty (L ≃* Sporadic.Mathieu.M12))
  | mathieu_twenty_two (e : Nonempty (L ≃* Sporadic.Mathieu.M22))
  | janko_two (e : Nonempty (L ≃* Sporadic.LeechRelated.J2.Carrier))

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X L : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Section10.Hypothesis ρ B v W X X₀)
  (h9 : ComponentHypothesis KnownSimple.IsKnownSimple ρ X L L
    (finrank (ZMod 2) (Additive X)))
  (hw : LowRankWitness ρ v X) (hd : 6 ≤ finrank (ZMod 2) V)

include h in
private theorem selfDual : Nonempty (Representation.Equiv (ρ.comp L.subtype) (Representation.dual (ρ.comp L.subtype))) := by
  refine ⟨BinaryCoverSocle.selfDualOfPairing (ρ.comp L.subtype) B
    (LinearMap.ker_eq_bot.mp h.nondegenerate.ker_eq_bot) ?_⟩
  intro g u w
  change B (ρ (g:G) u) w = B u (ρ ((g:G)⁻¹) w)
  have hh := h.preserves (g : G) u (ρ (g : G)⁻¹ w)
  simpa only [← Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    using hh

include h h9 in
private theorem not_linear_three {n : ℕ} (hn : 0<n)
    (model : ClassicalGroup.IsPSL L 3 (2^n) ∨ IsSL L 3 (2^n)) : False :=
  WholeLinearThree.not_binary_model h9 (selfDual h) hn model

include h h9 hw hd in
private theorem not_five (e : L ≃* alternatingGroup (Fin 5)) : False := by
  let k := GaloisField 2 2
  have hc : Nat.card k = 4 := by
    change Nat.card (GaloisField 2 2) = 4
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact WholeRankOne.not_projective_binary_rank_one h h9 hw hd (n := 2) (by decide)
    ⟨k,inferInstance,inferInstance,hc,⟨e.trans f.symm⟩⟩

include h h9 hw hd in
private theorem alternating {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 8)
    (e : L ≃* alternatingGroup (Fin n)) : Remaining L := by
  by_cases he : n=5
  · subst n
    exact (not_five h h9 hw hd e).elim
  · exact .alternating n (by omega) ⟨e⟩

include h h9 in
private theorem binary_linear {n : ℕ} (hn : n=4 ∨ n=5)
    (model : ClassicalGroup.IsPSL L n 2) : Remaining L := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : Fintype k := Fintype.ofFinite k
  let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hcard)
  rcases hn with rfl | rfl
  · exact .alternating 8 (by decide)
      ⟨(e.trans (Atlas.fieldEquivPSL 4 a)).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm⟩
  · exact (BinaryLinearRecognition.not_five_of_selfDual h9 (selfDual h)
      (e.trans (Atlas.fieldEquivPSL 5 a))).elim

include h h9 hw hd in
private theorem odd_two {p a : ℕ} (hp : p.Prime) (ho : Odd p) (ha : 0<a)
    (model : ClassicalGroup.IsPSL L 2 (p^a)) : Remaining L := by
  let : IsQuasisimple L := h9.component.2
  rcases Section07.OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h9.faithful.comp L.subtype_injective) hp ho ha model
    h9.single_component_degree_bound with hb | ht | he
  · exact (WholeRankOne.not_projective_binary_rank_one h h9 hw hd (n := 2) (by decide) hb).elim
  · exact (not_linear_three h h9 (n := 1) (by decide) (Or.inl (by simpa using ht))).elim
  · exact .alternating 6 (by decide) ⟨he.some.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp))⟩

include h9 in
private theorem odd_three {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (model : Section07.OddCharacteristic.IsLinearUnitaryThree L p) : Remaining L := by
  let : IsQuasisimple L := h9.component.2
  let : IsIrreducible (ρ.comp L.subtype) := h9.irreducible
  obtain ⟨e,_⟩ := Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h9.faithful.comp L.subtype_injective) hp ho model h9.single_component_degree_bound
  exact .binary_g2 e

include h h9 hw in
private theorem rank_two (model : RankTwoTheoremC L) : Remaining L := by
  cases model with
  | linear n hn hm => exact (not_linear_three h h9 hn (Or.inl hm)).elim
  | symplectic n hn hm => exact .symplectic n hn hm
  | g2 n hn hm => exact (WholeG2.not_nonbinary_model h h9 hw hn hm).elim
  | triality n hn hm => exact (TwistedExclusions.not_triality_positive_exponent h9 hn hm).elim
  | ree k hk hm =>
    obtain ⟨d,e⟩ := hm
    exact (TwistedExclusions.not_ree_of_local_block h9 hk d e.some).elim
  | symplectic_derived e => exact .alternating 6 (by decide) ⟨e.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩
  | g2_derived e => exact .binary_g2 e
  | tits e => exact (TwistedExclusions.not_tits_of_source_component h9 e.some).elim

private theorem simple_center_eq_bot {S : Type*} [Group S] [IsSimpleGroup S] [Group.IsPerfect S] :
    center S = ⊥ := by
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp ht)).elim

include h h9 hw hd in
private theorem simple_models (hsimple : IsSimpleGroup L) (model : TheoremCModel L) :
    Remaining L := by
  let : IsSimpleGroup L := hsimple
  let : IsQuasisimple L := h9.component.2
  let q : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq simple_center_eq_bot).trans QuotientGroup.quotientBot
  cases model with
  | alternating n hn e => exact alternating h h9 hw hd hn e.some
  | linear_odd p a hp ho ha _ hm =>
      exact odd_two h h9 hw hd hp ho (by rcases ha with rfl | rfl <;> decide) hm
  | three_odd p hp ho unitary hm =>
    apply odd_three h9 hp ho
    cases unitary with
    | false => exact Or.inl hm
    | true => exact Or.inr (Or.inr (Or.inl hm))
  | rank_one hm => exact (WholeRankOne.not_bender_model h h9 hw hd hm).elim
  | rank_two hm => exact rank_two h h9 hw hm
  | binary_linear n hn hm => exact binary_linear h h9 hn hm
  | sporadic name hne e =>
    cases name with
    | m11 => exact (h9.not_m11_central_quotient (q.trans e.some)).elim
    | m12 => exact .mathieu_twelve e
    | m22 => exact .mathieu_twenty_two e
    | m23 => exact (h9.not_m23 e.some).elim
    | m24 => exact (h9.not_m24_of_even_degree
        (AlternatingForm.even_finrank B h.alternating h.nondegenerate) e.some).elim
    | j2 => exact .janko_two e
    | j3 => exact (hne rfl).elim
    | j4 => exact (h9.not_janko_four e.some).elim
    | hs => exact (h9.not_higman_sims e.some).elim
    | he => exact (h9.not_held e.some).elim
    | ru => exact (h9.not_rudvalis e.some).elim
  | janko_one e => exact (h9.not_j1_central_quotient (q.trans e.some)).elim

include h hd in
/-- The center of a normal component cannot have order three: its actual
ambient image would force transitivity on the strict moved plane. -/
theorem not_center_three [L.Normal] (hc : Nat.card (center L)=3)
    (a : G) (ha : a^2=1) (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a)=2)
    (hnt : ¬ RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a)) : False := by
  let : IsIrreducible ρ := by
    by_contra hred
    have := (h.reducible_degree_and_solvable hred).1
    omega
  let Z := (center L).map L.subtype
  let : Z.Normal := inferInstanceAs ((center L).map L.subtype).Normal
  have hz : Nat.card Z=3 := by
    change Nat.card ((center L).map L.subtype) = 3
    rw [card_map_of_injective L.subtype_injective,hc]
  exact hnt (RankTwo.stabilizerTransitive_of_irreducible_normal_subgroup_three
    ρ h.faithful Z hz a (by omega) (by simpa only [pow_two] using ha) hr)

include h h9 hw hd in
/-- A normal whole component of the original marked action is simple and
belongs to the reduced carrier list. The strict moved-plane condition
excludes every central three-cover in the original catalogue. -/
theorem remaining_single_component
    (a : G) (ha : a^2=1) (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a)=2)
    (hnt : ¬ RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a)) :
    IsSimpleGroup L ∧ Remaining L := by
  rcases h9.single_component_models with ⟨hi,hm⟩ | ⟨hc,_⟩
  · exact ⟨hi,simple_models h h9 hw hd hi hm⟩
  · let := h9.normal_H
    exact (not_center_three h hd ((Nat.card_congr hc.some.toEquiv).trans (by simp))
      a ha hr hnt).elim

end CFSG.Quasithin.ChapterG.Section11.WholeModels
