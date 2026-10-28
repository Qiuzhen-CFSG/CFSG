module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Inner
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Outer.Geometry
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Outer.SchurLinear
public import Theory.Representation.SchurDisplacement.FixedCentralizer

/-!
# Degree selection for outer PSL₂ actors

Split according to the action of A on the actual layer Schur algebra. When
every element is Schur-linear, the tensor displacement and even highest-weight
repetition argument in `Outer.SchurLinear` gives dimension exactly `2*r`.

Otherwise choose an actor t moving the Schur algebra. It is outer and displaces
at least half of V. If the elementary actor has rank one, the ratio-two
bound gives dimension at most four. Otherwise its inner intersection is
nontrivial. The group L ∩ C_G(t) acts faithfully on C_V(t), since the kernel
is a normal two-subgroup and that centralizer has trivial two-core. Thus
C_V(A) is strictly smaller than C_V(t), giving
  dim(V) + 2 ≤ 2*fixedCodim(A) ≤ 4*rank(A) ≤ 2*r + 4.

The two branches give the degree window for the original outer actor, with
no additional recognition, degree, or tensor-displacement premise.

Source: Guralnick--Malle, Classification of 2F-modules II, §3.5 and
Proposition 4.1(2--3), manuscript pp.20--22; Aschbacher--Smith, K.3.1,
printed pp.451,453--454.
-/

public section
open scoped MatrixGroups IsMulCommutative
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
namespace CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
  (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))

include h e

/-- If an actor moves the actual layer Schur field, its fixed space and the
half-degree centralizer bound give the required degree window. Cubicity and
an assumed ambient rank bound are unnecessary for this branch. -/
theorem psl2_degree_window_of_schurMoving_actor {r : ℕ} (hr : 2 ≤ r)
    (hc : Nat.card K = 2 ^ r) {A : Subgroup G} (hA : IsElementaryTwo A)
    (hd : fixedCodim ρ A ≤ 2 * rank A)
    (hs : ∃ t ∈ A, ¬ IsSchurLinear ρ L t) :
    Module.finrank (ZMod 2) V ≤ 2 * (r + 1) := by
  obtain ⟨t, htA, htS⟩ := hs
  let : L.Normal := h.layer_normal
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  let : IsElementaryAbelian 2 A := hA.2
  have htL : t ∉ L := fun ht => htS (isSchurLinear_of_mem ρ L ht)
  have hAL : ¬ A ≤ L := fun hAL => htL (hAL htA)
  have ht : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
  have hn : t ∈ normalizer (L : Set G) := by rw [normalizer_eq_top]; trivial
  obtain ⟨hR, hlarge⟩ := h.psl2_outer_actor_rank e hr hc hA hAL
  by_cases hsmall : rank A ≤ 1
  · have hdisp := finrank_le_twice_displacement_of_not_isSchurLinear ρ L t hn htS
    have hhalf : Module.finrank (ZMod 2) V ≤ 2 * fixedCodim ρ (zpowers t) := by
      simpa only [fixedCodim_zpowers_eq_displacement_rank, Module.End.one_eq_id] using hdisp
    have hfix : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
      intro v hv a
      exact hv ⟨a, (zpowers_le.mpr htA) a.property⟩
    have hdim := Submodule.finrank_mono hfix
    have h1 := fixedCodim_add_finrank ρ A
    have h2 := fixedCodim_add_finrank ρ (zpowers t)
    omega
  · obtain ⟨b, hb, hb1⟩ := (A ⊓ L).bot_or_exists_ne_one.resolve_left (hlarge (by omega))
    have hbC : b ∈ L ⊓ centralizer {t} := by
      refine ⟨hb.2, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mul_comm (⟨b, hb.1⟩ : A) ⟨t, htA⟩)
    have hstrict := finrank_add_two_le_twice_fixedCodim_of_schurMoving ρ L
      h.faithful t ht hn htS (L ⊓ centralizer {t}) inf_le_right
      (h.psl2_outer_centralizer_twoCore_eq_bot e hr hc t ht htL) htA hb.1 hbC hb1
    omega

/-- The even-degree outer-actor estimate for Chapter K, on the original
ambient representation. The Schur-linear and Schur-moving branches exhaust
the action on the actual layer endomorphism algebra. -/
theorem psl2_degree_window_of_outer_actor {r : ℕ} (hr : 2 ≤ r)
    (hc : Nat.card K = 2 ^ r) (heven : Even r)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hC : IsCubic ρ A)
    (hd : fixedCodim ρ A ≤ 2 * rank A) (hR : rank A ≤ r) (hAL : ¬ A ≤ L) :
    Module.finrank (ZMod 2) V ≤ 2 * (r + 1) := by
  classical
  by_cases hlin : ∀ t ∈ A, IsSchurLinear ρ L t
  · exact h.psl2_degree_window_of_schurLinear_actor e hr hc heven hA hC hd hR hAL hlin
  · push Not at hlin
    exact h.psl2_degree_window_of_schurMoving_actor e hr hc hA hd hlin

end CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
