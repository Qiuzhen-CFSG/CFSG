module
public import CFSG.Quasithin.ChapterG.Section11.WholeRankOne
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentModels
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentEvenExclusions
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.SourceModels
public import Theory.Mathieu.SmallModuleRanks.M12

/-!
# Remaining carriers for a single whole component

Apply the genuine G.9 carrier catalogue to the original irreducible component.
The low-rank witness excludes Bender groups. The preserved alternating form
supplies even degree and self-duality of this same component action, excluding
M₂₃, M₂₄ and binary SL₅. The half-degree bound also excludes M₁₂ using its inner rank three and
outer index two. The established degree bounds remove the other large
sporadics, J₁, triality, Ree, Tits and the triple A₇ cover. All surviving rows
retain actual model isomorphisms, including the central quotient of a cover.

The original HS consumer is in SourceAction.CatalogueReduction. This is a
carrier reduction; the remaining module identifications and the two-component
branch still require proof. Source: Aschbacher--Smith G.9.3 and G.11.7,
printed pp.353--356,366--368.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section11.WholeComponentCandidates
open Chapter1.Section02 ClassificationModels

/-- The rank-two defining-characteristic carriers not yet eliminated here. -/
@[expose] def RankTwo (D : Type*) [Group D] : Prop :=
  (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL D 3 (2^f)) ∨
  (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp D 2 (2^f)) ∨
  (∃ f : ℕ, 2 ≤ f ∧ IsG2At D (2^f)) ∨
  Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
  Nonempty (D ≃* commutator (Atlas.G2.Model (ZMod 2)))

/-- Remaining simple carriers, each connected to the literal component. -/
@[expose] def Simple (D : Type*) [Group D] : Prop :=
  (∃ n : ℕ, (5 ≤ n ∧ n ≤ 8) ∧ LocalModels.IsAlternating D n) ∨
  (∃ p e : ℕ, p.Prime ∧ Odd p ∧ (e = 1 ∨ e = 2) ∧ 4 ≤ p^e ∧
    ClassicalGroup.IsPSL D 2 (p^e)) ∨
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool, LocalModels.IsPSLSign D unitary 3 p) ∨
  RankTwo D ∨ ClassicalGroup.IsPSL D 4 2 ∨
  Nonempty (D ≃* Sporadic.Mathieu.M22) ∨
  Nonempty (D ≃* Sporadic.LeechRelated.J2.Carrier)

/-- Remaining central-three covers; both the cover and its quotient are literal. -/
@[expose] def Cover (D : Type*) [Group D] : Prop :=
  (∃ unitary : Bool, ∃ q : ℕ, LocalModels.CoverParameter unitary q ∧
    LocalModels.IsSLSign D unitary 3 q) ∨
  LocalModels.IsAlternatingCover D 6 ∨ LocalModels.IsM22Cover D

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X J : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

private def selfDual (h : Section10.Hypothesis ρ B v W X X₀) :
    Representation.Equiv (ρ.comp J.subtype) (Representation.dual (ρ.comp J.subtype)) := {
  toLinearEquiv := B.toDual h.nondegenerate
  isIntertwining' a := by
    ext w z
    change B (ρ (a:G) w) z = B w (ρ ((a:G)⁻¹) z)
    have hh := h.preserves (a:G) w (ρ ((a:G)⁻¹) z)
    simpa only [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,
      Module.End.one_apply] using hh }

private def simpleQuotient [IsSimpleGroup J] [Group.IsPerfect J] :
    (J ⧸ center J) ≃* J := by
  have hz : center J = ⊥ := by
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp ht)).elim
  exact (QuotientGroup.quotientMulEquivOfEq hz).trans (QuotientGroup.quotientBot)

private theorem rankTwo_cases
    (h9 : Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X J J
      (finrank (ZMod 2) (Additive X)))
    (hm : LocalModels.RankTwoTheoremC J) : RankTwo J := by
  cases hm with
  | linear f hf e => exact .inl ⟨f,hf,e⟩
  | symplectic f hf e => exact .inr (.inl ⟨f,hf,e⟩)
  | g2 f hf e => exact .inr (.inr (.inl ⟨f,hf,e⟩))
  | symplectic_derived e => exact .inr (.inr (.inr (.inl e)))
  | g2_derived e => exact .inr (.inr (.inr (.inr e)))
  | triality f hf e =>
    exact (Section09.DefiningCharacteristic.TwistedExclusions.not_triality_positive_exponent h9
      (by omega) e).elim
  | ree m hm e =>
    obtain ⟨d,⟨e⟩⟩ := e
    exact (Section09.DefiningCharacteristic.TwistedExclusions.not_ree_of_local_block h9 hm d e).elim
  | tits e =>
    exact (Section09.DefiningCharacteristic.TwistedExclusions.not_tits_of_source_component h9 e.some).elim

private theorem not_mathieu_twelve
    (h9 : Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X J J
      (finrank (ZMod 2) (Additive X)))
    (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X))
    (e : J ≃* Sporadic.Mathieu.M12) : False := by
  open Sporadic.Mathieu M12ExceptionalExtension in
  have hr : primeRank 2 (MulAut M12) ≤ 4 := by
    let : M12ExceptionalExtension.inner.Normal := normal_of_index_eq_two inner_index
    have hq : primeRank 2 (Carrier ⧸ M12ExceptionalExtension.inner) ≤ 1 := by
      apply primeRank_le_of_prime_pow_not_dvd
      rw [← index_eq_card,inner_index]
      decide
    have hk : primeRank 2 M12ExceptionalExtension.inner ≤ 3 := by
      rw [← primeRank_equiv 2 innerModel.equiv]
      exact m12_twoRank_le_three
    have hb := primeRank_le_ker_add (p := 2) (QuotientGroup.mk' M12ExceptionalExtension.inner)
    rw [QuotientGroup.ker_mk'] at hb
    rw [← primeRank_equiv 2 automorphismEquiv]
    omega
  let : IsIrreducible (ρ.comp J.subtype) := h9.irreducible
  have hm := h9.toSetup.rank_le_automorphisms (L := J) (by
    rw [normalizer_eq_top_iff.mpr h9.normal_H]; exact le_top)
  rw [primeRank_equiv 2 (MulAut.congr e)] at hm
  have hd := Section07.MathieuRecognition.ten_le_finrank_of_m12
    (ρ.comp J.subtype) (h9.faithful.comp J.subtype_injective) e
  omega

/-- The original single whole component has one of these literal remaining
carriers. No strict-D hypotheses or classification conclusion are assumed. -/
theorem single_component_candidates
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X J J
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (hd : 6 ≤ finrank (ZMod 2) V)
    (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X)) :
    (IsSimpleGroup J ∧ Simple J) ∨
      (Nonempty (center J ≃* Multiplicative (ZMod 3)) ∧ Cover J) := by
  have heven := AlternatingForm.even_finrank B h.alternating h.nondegenerate
  rcases h9.single_component_models with ⟨hi,hm⟩ | ⟨hz,hm⟩
  · let := hi
    let : Group.IsPerfect J := h9.component.2.toIsPerfect
    have hq := simpleQuotient (J := J)
    left
    refine ⟨hi,?_⟩
    cases hm with
    | alternating n hn e => exact .inl ⟨n,hn,e⟩
    | linear_odd p e hp ho he hn iso => exact .inr (.inl ⟨p,e,hp,ho,he,hn,iso⟩)
    | three_odd p hp ho u iso => exact .inr (.inr (.inl ⟨p,hp,ho,u,iso⟩))
    | rank_one iso => exact (WholeRankOne.not_bender_model h h9 hw hd iso).elim
    | rank_two iso => exact .inr (.inr (.inr (.inl (rankTwo_cases h9 iso))))
    | binary_linear n hn iso =>
      rcases hn with rfl | rfl
      · exact .inr (.inr (.inr (.inr (.inl iso))))
      · obtain ⟨F,_,_,hc,⟨e⟩⟩ := iso
        let : Fintype F := Fintype.ofFinite F
        let e2 : F ≃+* ZMod 2 :=
          FiniteField.ringEquivOfCardEq (by simpa [← Nat.card_eq_fintype_card] using hc)
        have ep : J ≃* PSL(5,ZMod 2) := e.trans (Atlas.fieldEquivPSL 5 e2)
        exact (h9.not_even_models heven ⟨selfDual h⟩ (.inr (.inr ⟨ep⟩))).elim
    | janko_one iso => exact (h9.not_j1_central_quotient (hq.trans iso.some)).elim
    | sporadic name hne iso =>
      cases name with
      | m11 => exact (h9.not_m11_central_quotient (hq.trans iso.some)).elim
      | m12 => exact (not_mathieu_twelve h9 hlarge iso.some).elim
      | m22 => exact .inr (.inr (.inr (.inr (.inr (.inl iso)))))
      | j2 => exact .inr (.inr (.inr (.inr (.inr (.inr iso)))))
      | m23 => exact (h9.not_m23 iso.some).elim
      | m24 => exact (h9.not_m24_of_even_degree heven iso.some).elim
      | j3 => exact (hne rfl).elim
      | j4 => exact (h9.not_janko_four iso.some).elim
      | hs => exact (h9.not_higman_sims iso.some).elim
      | he => exact (h9.not_held iso.some).elim
      | ru => exact (h9.not_rudvalis iso.some).elim
  · right
    refine ⟨hz,?_⟩
    cases hm with
    | classical u q hq iso => exact .inl ⟨u,q,hq,iso⟩
    | alternating_six iso => exact .inr (.inl iso)
    | mathieu iso => exact .inr (.inr iso)
    | alternating_seven iso =>
      have hc : Nat.card (center J) = 3 := by
        rw [Nat.card_congr hz.some.toEquiv]
        exact Nat.card_zmod 3
      exact (h9.not_triple_alternating_seven iso.2.2.some hc).elim

/-- Either the original orbit is a single component with one of the remaining
carriers, or it has two distinct components with the original action comparison. -/
@[expose] def Alternatives (ρ : Representation (ZMod 2) G V) (J H : Subgroup G) : Prop :=
  (H = J ∧ ((IsSimpleGroup J ∧ Simple J) ∨
    (Nonempty (center J ≃* Multiplicative (ZMod 3)) ∧ Cover J))) ∨
  ∃ J₂ : Subgroup G, IsComponent G J₂ ∧ J₂ ≠ J ∧ H = J ⊔ J₂ ∧
    (Section09.Quasiequivalent (ρ.comp J.subtype) (ρ.comp J₂.subtype) ∨
      Section09.Quasiequivalent (ρ.comp J.subtype) (Representation.dual (ρ.comp J₂.subtype)))

/-- Apply the single-component sieve to the literal normal component orbit;
the unresolved pair is retained with distinct components and actual intertwiners. -/
theorem component_candidates {H : Subgroup G}
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X J H
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (hd : 6 ≤ finrank (ZMod 2) V)
    (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X)) :
    Alternatives ρ J H := by
  by_cases he : H = J
  · exact .inl ⟨he,single_component_candidates h (he ▸ h9) hw hd hlarge⟩
  · rcases h9.components with heq | ⟨J₂,hJ₂,heq,hcomp⟩
    · exact (he heq).elim
    · refine .inr ⟨J₂,hJ₂,?_,heq,hcomp⟩
      intro hsame
      exact he (by simpa only [hsame,sup_idem] using heq)

end CFSG.Quasithin.ChapterG.Section11.WholeComponentCandidates
