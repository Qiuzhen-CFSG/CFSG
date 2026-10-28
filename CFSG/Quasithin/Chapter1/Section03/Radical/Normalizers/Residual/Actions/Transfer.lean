module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Frattini
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Transfer
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Omega

/-!
# Residual action transfer and commutator generation

The relative Frattini factorization compares the actions of L and
Y = N_L(O₂(Ξ_p(L)T))^∞. For a different odd factor, only the section
centralizer inside L must act trivially. The Sylow and omega comparisons
use the actual quotient equivalences.

The image of [X,Y] in X/O₂,Φ(X) is invariant. Irreducibility makes it
bottom or top; the bottom case would make every cyclic subgroup invariant,
contrary to the noncyclic odd quotient. Frattini nongeneration then gives
[X,Y]O₂(X) = X. Since X is two-perfect, its two-group quotient by [X,Y]
is trivial. This proves generation without assuming X ≤ Y.

The action and cross-prime kernel premises below remain explicit. Their
source assembly must discharge them before claiming Proposition 1.3.8.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed pp.512–513.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.ChapterA.Section04

namespace CFSG.Quasithin.Chapter1.RadicalNormalizers

private theorem isCyclic_of_all_subgroups_trivial
    {V : Type*} [Group V]
    (h : ∀ A : Subgroup V, A = ⊥ ∨ A = ⊤) : IsCyclic V := by
  classical
  by_cases hs : Subsingleton V
  · let := hs
    infer_instance
  · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    rcases h (zpowers v) with hb | ht
    · exact (hv (Subgroup.mem_bot.mp (hb ▸ mem_zpowers v))).elim
    · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨v, ht⟩

private theorem commutator_eq_of_xiFrattini_irreducible
    {G : Type*} [Group G] [Finite G] (X S : Subgroup G)
    (hn : S ≤ normalizer (X : Set G)) (hX : IsPPerfect 2 X)
    (hnc : ¬ IsCyclic (XiFrattiniQuotient X))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : S, ∀ a ∈ A, xiFrattiniAction S X hn s a ∈ A) →
        A = ⊥ ∨ A = ⊤) : ⁅X,S⁆ = X := by
  let D := ⁅X,S⁆.subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  let f := (QuotientGroup.mk' (frattini (XiQuotient X))).comp q
  let _ := conjMulDistribMulActionOfLeNormalizer S X hn
  have he (s : S) (x : X) :
      xiFrattiniAction S X hn s (f x) = f (s • x) := by
    simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk, f, q]
    rfl
  have hstable : ∀ s : S, ∀ a ∈ D.map f, xiFrattiniAction S X hn s a ∈ D.map f := by
    rintro s a ⟨x, hx, rfl⟩
    refine ⟨s • x, ?_, (he s x).symm⟩
    exact (mem_normalizer_iff.mp (normalizer_commutator_ge_right X S s.property) x).mp hx
  have himage : D.map f = ⊤ := by
    rcases hirr (D.map f) hstable with hb | ht
    · have hfix (s : S) (a : XiFrattiniQuotient X) : xiFrattiniAction S X hn s a = a := by
        obtain ⟨x, rfl⟩ := ((QuotientGroup.mk'_surjective _).comp
          (QuotientGroup.mk'_surjective _)) a
        change xiFrattiniAction S X hn s (f x) = f x
        rw [he]
        have hd : (s • x) * x⁻¹ ∈ D := by
          change ⁅(s : G), (x : G)⁆ ∈ ⁅X,S⁆
          rw [commutator_comm]
          exact commutator_mem_commutator s.property x.property
        have hz : f ((s • x) * x⁻¹) = 1 :=
          Subgroup.mem_bot.mp (hb ▸ mem_map_of_mem f hd)
        rw [map_mul, map_inv] at hz
        exact mul_inv_eq_one.mp hz
      exact (hnc (isCyclic_of_all_subgroups_trivial (fun A =>
        hirr A (by intro s a ha; rw [hfix]; exact ha)))).elim
    · exact ht
  have hqimage : D.map q = ⊤ := by
    apply frattini_nongenerating
    have hm := congrArg (comap (QuotientGroup.mk' (frattini (XiQuotient X)))) himage
    rw [← map_map, comap_map_eq, QuotientGroup.ker_mk', comap_top] at hm
    exact hm
  have hsup : D ⊔ pCore 2 X = ⊤ := by
    have hm := congrArg (comap q) hqimage
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hm
  let : D.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left X S)
  have hD : D = ⊤ := hX D inferInstance
    (isPGroup_quotient_of_sup_eq_top D (pCore 2 X) pCore_isPGroup hsup)
  have hm := congrArg (map X.subtype) hD
  simpa only [D, map_subgroupOf_eq_of_le (le_normalizer_iff_commutator_le_left.mp hn),
    ← MonoidHom.range_eq_map, range_subtype] using hm

variable {G : Type*} [Group G] [Finite G]

/-- Irreducibility and the genuine odd quotient shape force commutator generation.
No containment of the radical factor in Y is assumed. -/
theorem XiP_commutator_of_Y_irreducible (p q : ℕ) [Fact q.Prime] (L T : Subgroup G)
    (hq : XiOddQuotient q (XiQuotient (XiP q L)))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ y : normalizerResidual L (radicalCore p L T), ∀ a ∈ A,
        xiFrattiniAction _ _ (Y_normalizes_XiP p q L T) y a ∈ A) →
        A = ⊥ ∨ A = ⊤) :
    ⁅XiP q L, normalizerResidual L (radicalCore p L T)⁆ = XiP q L := by
  exact commutator_eq_of_xiFrattini_irreducible _ _ (Y_normalizes_XiP p q L T)
    (XiP_isPPerfect q L) (OddInvolutionFrattini.noncyclic_frattini_quotient hq.not_isCyclic) hirr

/-- The residual cover transfers irreducibility on any odd factor when the
section centralizer inside L lies in that action's kernel. -/
theorem Y_irreducible_of_relative_kernel (p q : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G))
    (hker : (twoSectionCentralizer (XiP p L) (L ⊔ T)).subgroupOf L ≤
      (xiFrattiniAction L (XiP q L) (XiP_invariant q L.le_normalizer)).ker)
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ l : L, ∀ a ∈ A,
        xiFrattiniAction L (XiP q L) (XiP_invariant q L.le_normalizer) l a ∈ A) →
        A = ⊥ ∨ A = ⊤) :
    ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ y : normalizerResidual L (radicalCore p L T), ∀ a ∈ A,
        xiFrattiniAction _ _ (Y_normalizes_XiP p q L T) y a ∈ A) →
        A = ⊥ ∨ A = ⊤ := by
  intro A hA
  apply hirr A
  intro l a ha
  let f := xiFrattiniAction L (XiP q L) (XiP_invariant q L.le_normalizer)
  have hl : f l ∈ f.range := ⟨l, rfl⟩
  rw [Y_covers_L_action p L T hL hT f hker] at hl
  obtain ⟨y, hy, he⟩ := hl
  have hh := hA ⟨y, hy⟩ a ha
  change f y a ∈ A at hh
  rwa [he] at hh

/-- The actual Sylow-complement equivalence transfers the source normalizer
action back to the L-action on the radical Frattini section. -/
theorem L_irreducible_of_normalizer_irreducible
    (q : ℕ) [Fact q.Prime] (ho : Odd q) (L : Subgroup G)
    (P : Sylow q (XiP q L))
    (hirr : let P₀ := (P : Subgroup (XiP q L)).map (XiP q L).subtype
      ∀ A : Subgroup (P₀ ⧸ frattini P₀),
        (∀ l : (L ⊓ normalizer P₀ : Subgroup G), ∀ a ∈ A,
          frattiniConjugationAction (L ⊓ normalizer P₀) P₀ inf_le_right l a ∈ A) →
          A = ⊥ ∨ A = ⊤) :
    ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ l : L, ∀ a ∈ A,
        xiFrattiniAction L (XiP q L) (XiP_invariant q L.le_normalizer) l a ∈ A) →
        A = ⊥ ∨ A = ⊤ := by
  intro A hA
  let e := RadicalActions.sylowFrattiniEquiv ho (XiP_quotient_isPGroup q ho L) P
  have hpre := hirr (A.comap e.toMonoidHom) (by
    intro l a ha
    change e (frattiniConjugationAction _ _ inf_le_right l a) ∈ A
    rw [RadicalActions.sylowFrattiniEquiv_equivariant (XiP_invariant q L.le_normalizer)]
    exact hA ⟨l, l.property.1⟩ (e a) ha)
  rcases hpre with hb | ht
  · left
    have hm := congrArg (map e.toMonoidHom) hb
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective A,
      Subgroup.map_bot] using hm
  · right
    have hm := congrArg (map e.toMonoidHom) ht
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective A,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm

/-- Conditional assembly of both residual action conclusions. The source owner
must establish the L-action and the relative kernel inclusion. -/
theorem XiP_Y_actions_of_relative_kernel
    (p q : ℕ) [Fact q.Prime] (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G))
    (hq : XiOddQuotient q (XiQuotient (XiP q L)))
    (hker : (twoSectionCentralizer (XiP p L) (L ⊔ T)).subgroupOf L ≤
      (xiFrattiniAction L (XiP q L) (XiP_invariant q L.le_normalizer)).ker)
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ l : L, ∀ a ∈ A,
        xiFrattiniAction L (XiP q L) (XiP_invariant q L.le_normalizer) l a ∈ A) →
        A = ⊥ ∨ A = ⊤) :
    ⁅XiP q L, normalizerResidual L (radicalCore p L T)⁆ = XiP q L ∧
    ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ y : normalizerResidual L (radicalCore p L T), ∀ a ∈ A,
        xiFrattiniAction _ _ (Y_normalizes_XiP p q L T) y a ∈ A) →
        A = ⊥ ∨ A = ⊤ := by
  have hi := Y_irreducible_of_relative_kernel p q L T hL hT hker hirr
  exact ⟨XiP_commutator_of_Y_irreducible p q L T hq hi, hi⟩

/-- For the defining prime p, the Frattini factorization discharges the kernel
comparison and leaves only the earlier L-action to supply. -/
theorem XiP_Y_actions_of_L_irreducible
    (p : ℕ) [Fact p.Prime] (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T) (hT : T ≤ normalizer (L : Set G))
    (hq : XiOddQuotient p (XiQuotient (XiP p L)))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ l : L, ∀ a ∈ A,
        xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer) l a ∈ A) →
        A = ⊥ ∨ A = ⊤) :
    ⁅XiP p L, normalizerResidual L (radicalCore p L T)⁆ = XiP p L ∧
    ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ y : normalizerResidual L (radicalCore p L T), ∀ a ∈ A,
        xiFrattiniAction _ _ (Y_normalizes_XiP p p L T) y a ∈ A) →
        A = ⊥ ∨ A = ⊤ := by
  have hi := Y_irreducible_of_L_irreducible p L T hL hT hirr
  exact ⟨XiP_commutator_of_Y_irreducible p p L T hq hi, hi⟩

omit [Finite G] in
/-- The defining section centralizer inside L kills the actual p-Frattini action. -/
theorem sectionCentralizer_le_L_frattiniAction_ker (p : ℕ) (L T : Subgroup G)
    (hT : T ≤ normalizer (L : Set G)) :
    (twoSectionCentralizer (XiP p L) (L ⊔ T)).subgroupOf L ≤
      (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)).ker := by
  intro l hl
  have hh : localXiQuotientAction p L T hT ⟨l, (show L ≤ L ⊔ T from le_sup_left) l.property⟩ = 1 :=
    sectionCentralizer_le_action_ker p L T hT hl
  have hf := congrArg (quotientAut (frattini (XiQuotient (XiP p L)))) hh
  rw [map_one] at hf
  change xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer) l = 1
  apply MulEquiv.ext
  intro a
  exact DFunLike.congr_fun hf a

open RadicalActions

/-- The actual two-core quotient and omega coordinates transfer component
irreducibility to the L-action, retaining the omega layer. -/
theorem L_irreducible_of_omega_irreducible
    (p : ℕ) [Fact p.Prime] (ho : Odd p) (L : Subgroup G)
    (hirr : ∀ A : Subgroup (omegaCore p (XiQuotient L) ⧸ frattini (omegaCore p (XiQuotient L))),
      (∀ k : XiQuotient L, ∀ a ∈ A, omegaFrattiniAction p (XiQuotient L) k a ∈ A) →
        A = ⊥ ∨ A = ⊤) :
    ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ l : L, ∀ a ∈ A,
        xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer) l a ∈ A) →
        A = ⊥ ∨ A = ⊤ := by
  intro A hA
  let e := xiPFrattiniEquivCore ho L
  have hi := hirr (A.map e.toMonoidHom) (by
    intro k a ha
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) k
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer) l b,
      hA l b hb, xiPFrattiniEquivCore_equivariant ho L l b⟩)
  rcases hi with hb | ht
  · exact Or.inl ((A.map_eq_bot_iff_of_injective e.injective).mp hb)
  · right
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective e.toMonoidHom e.surjective]
    exact ht

end CFSG.Quasithin.Chapter1.RadicalNormalizers
