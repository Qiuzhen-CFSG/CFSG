module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.Reduction
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Extracting the inner involution in an outer elementary actor

Since L is the generalized Fitting subgroup, an ambient element induces an
inner automorphism on L exactly when it belongs to L. If an elementary
subgroup meets L trivially, it embeds into the actual cyclic outer group
of Sp4 and has rank at most one. Otherwise its nontrivial intersection
supplies an inner involution commuting with every outer member.

For an actor with fixed codimension at most twice its rank, a displacement
bound of three excludes rank one. A half-degree bound for the common fixed
space of the resulting pair then gives binary degree at most 12r+4.
The two tensor estimates remain explicit; this is a reduction, not their
proof or the completed source support-selection theorem.

Source: Guralnick--Malle, Classification of 2F-modules II, Section 3.5,
Proposition 6.2(2--3); Aschbacher--Smith K.3.4, printed pp.456--457.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur

variable {G V H : Type*} [Group G] [Finite G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Conjugation on the actual component, transported by its marked isomorphism. -/
def componentAction [L.Normal] (d : L ≃* H) : G →* MulAut H :=
  (MulAut.congr d).toMonoidHom.comp MulAut.conjNormal

omit [FiniteDimensional (ZMod 2) V] in
/-- Self-centralization of the generalized Fitting subgroup detects inner actors. -/
theorem componentAction_mem_inner_iff {K : GroupClass}
    (h : SourceHypothesis K ρ L) [L.Normal] (d : L ≃* H) (g : G) :
    componentAction d g ∈ MulAut.innerSubgroup H ↔ g ∈ L := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (MulAut.congr_inner_iff d (MulAut.conjNormal g)).mp ⟨x, hx.symm⟩
    have hg : g ∈ (MulAut.innerSubgroup L).comap MulAut.conjNormal := ⟨y, hy.symm⟩
    rw [MulAut.conjNormal_comap_innerSubgroup] at hg
    have hc : centralizer (L : Set G) ≤ L := by
      simpa only [h.fitting] using centralizer_generalizedFitting_le G
    exact (sup_le le_rfl hc) hg
  · intro hg
    refine ⟨d ⟨g, hg⟩, ?_⟩
    change MulAut.conj (d ⟨g, hg⟩) = MulAut.congr d (MulAut.conjNormal g)
    rw [← MulAut.congr_conj]
    exact congrArg (MulAut.congr d)
      (MulAut.conjNormal_val (h := (⟨g, hg⟩ : L))).symm

omit [FiniteDimensional (ZMod 2) V] in
/-- Trivial component intersection embeds the elementary actor into the cyclic outer group. -/
theorem rank_le_one_of_inf_component_eq_bot {K : GroupClass}
    (h : SourceHypothesis K ρ L) [L.Normal] (d : L ≃* H)
    [Finite H] [IsCyclic (MulAut.Outer H)]
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAL : A ⊓ L = ⊥) :
    rank A ≤ 1 := by
  classical
  let : IsElementaryAbelian 2 A := hA
  let f : A →* MulAut.Outer H :=
    (QuotientGroup.mk' (MulAut.innerSubgroup H)).comp ((componentAction d).comp A.subtype)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro a ha
    have hi : componentAction d (a : G) ∈ MulAut.innerSubgroup H :=
      (QuotientGroup.eq_one_iff _).mp ha
    have hal : (a : G) ∈ A ⊓ L :=
      ⟨a.property, (componentAction_mem_inner_iff h d a).mp hi⟩
    rw [hAL, mem_bot] at hal
    exact Subtype.ext hal
  let : IsCyclic A := isCyclic_of_injective f hf
  let := Fintype.ofFinite A
  have hcard : Nat.card A ≤ 2 := by
    have he : Finset.univ.filter (fun a : A => a ^ 2 = 1) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro a _
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a
    have hc := IsCyclic.card_pow_eq_one_le (α := A) (by decide : 0 < 2)
    rw [he] at hc
    simpa only [Nat.card_eq_fintype_card, Finset.card_univ] using hc
  have hh := Nat.log_mono_right (b := 2) hcard
  exact hh

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- Rank greater than one forces a nontrivial inner involution in the actual actor. -/
theorem source_inner_involution_of_rank_gt_one {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ center L ≃* Sp F) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hrank : 1 < rank A) :
    ∃ u ∈ A, u ∈ L ∧ u ≠ 1 ∧ u ^ 2 = 1 := by
  let : L.Normal := h.fitting ▸ inferInstance
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  let : IsQuasisimple L := h.quasisimple
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let : IsElementaryAbelian 2 A := hA
  let d := coverEquiv (ρ.comp L.subtype) (h.faithful.comp Subtype.val_injective) e
  let := ExceptionalGraph.outer_isCyclic_of_card hF hr
    SemilinearClassification.inner_field_of_preservesDiagram
  have hne : A ⊓ L ≠ ⊥ := by
    intro hz
    have hh := rank_le_one_of_inf_component_eq_bot h d A hA hz
    omega
  obtain ⟨u, hu, hune⟩ := (A ⊓ L).bot_or_exists_ne_one.resolve_left hne
  exact ⟨u, hu.1, hu.2, hune, elemPow_eq_one_of_isElementaryAbelian u hu.1⟩

/-- An outer elementary actor of rank greater than one supplies a commuting outer/inner pair. -/
theorem source_outer_inner_pair_of_rank_gt_one {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ center L ≃* Sp F) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hnot : ¬ A ≤ L) (hrank : 1 < rank A) :
    ∃ t ∈ A, ∃ u ∈ A, t ∉ L ∧ t ^ 2 = 1 ∧
      u ∈ L ∧ u ≠ 1 ∧ u ^ 2 = 1 ∧ Commute t u := by
  let : IsElementaryAbelian 2 A := hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨t, ht, htn⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨u, hu, huL, hune, hu2⟩ :=
    source_inner_involution_of_rank_gt_one h hr hF e A hA hrank
  refine ⟨t, ht, u, hu, htn, elemPow_eq_one_of_isElementaryAbelian t ht,
    huL, hune, hu2, ?_⟩
  exact congrArg Subtype.val (mul_comm (⟨t, ht⟩ : A) ⟨u, hu⟩)

/-- Codimension of the common fixed space of two literal ambient operators. -/
noncomputable def pairFixedCodim (ρ : Representation (ZMod 2) G V) (t u : G) : ℕ :=
  Module.finrank (ZMod 2) (V ⧸ ((ρ t - 1).ker ⊓ (ρ u - 1).ker))

omit [Finite G] in
/-- Subgroup invariants are contained in the common fixed space of any two members. -/
theorem pairFixedCodim_le (A : Subgroup G) {t u : G} (ht : t ∈ A) (hu : u ∈ A) :
    pairFixedCodim ρ t u ≤ fixedCodim ρ A := by
  have hle : fixedSpace ρ A ≤ (ρ t - 1).ker ⊓ (ρ u - 1).ker := by
    intro v hv
    exact ⟨sub_eq_zero.mpr (hv ⟨t, ht⟩), sub_eq_zero.mpr (hv ⟨u, hu⟩)⟩
  have hh := Submodule.finrank_mono hle
  have hpair := ((ρ t - 1).ker ⊓ (ρ u - 1).ker).finrank_quotient_add_finrank
  have hfixed := (fixedSpace ρ A).finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) (V ⧸ _) ≤ Module.finrank (ZMod 2) (V ⧸ _)
  omega

/-- The ambient numerical reduction. The single-actor and common-fixed-space
estimates must still be proved on the actual module; neither follows from
Schur-linearity alone. No graph-cocycle descent or sharp rank bound is used. -/
theorem degree_le_of_outer_estimates {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ center L ≃* Sp F) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hnot : ¬ A ≤ L)
    (hrank : rank A ≤ 3*r+1) (hcodim : fixedCodim ρ A ≤ 2 * rank A)
    (hlinear : ∀ a ∈ A, IsSchurLinear ρ L a)
    (hsingle : ∀ t ∈ A, t ∉ L → t ^ 2 = 1 → IsSchurLinear ρ L t →
      3 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)))
    (hpair : ∀ t ∈ A, ∀ u ∈ A, t ∉ L → t ^ 2 = 1 → u ∈ L → u ≠ 1 →
      u ^ 2 = 1 → Commute t u → IsSchurLinear ρ L t →
      Module.finrank (ZMod 2) V ≤ 2 * pairFixedCodim ρ t u) :
    Module.finrank (ZMod 2) V ≤ 12*r+4 := by
  let : IsElementaryAbelian 2 A := hA
  have hrank' : 1 < rank A := by
    by_contra! hn
    obtain ⟨t, ht, htL⟩ := SetLike.not_le_iff_exists.mp hnot
    have hl := hsingle t ht htL (elemPow_eq_one_of_isElementaryAbelian t ht) (hlinear t ht)
    have hu := displacement_finrank_le_fixedSpace_codim ρ A ht
    change Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ fixedCodim ρ A at hu
    omega
  obtain ⟨t, ht, u, hu, htL, ht2, huL, hune, hu2, htu⟩ :=
    source_outer_inner_pair_of_rank_gt_one h hr hF e A hA hnot hrank'
  have hp := hpair t ht u hu htL ht2 huL hune hu2 htu (hlinear t ht)
  have hh := pairFixedCodim_le (ρ := ρ) A ht hu
  omega

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
