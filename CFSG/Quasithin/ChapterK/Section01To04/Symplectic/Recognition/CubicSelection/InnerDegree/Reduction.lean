module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree.Setup
public import Theory.Representation.BinaryOffender.TwoWeightMaximizer
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Inner cubic actors: the parabolic reduction of the degree bound

The exponent-two maximizer in a containing radical is invariant under the
radical's full normalizer. Once the concrete invariant-subgroup classification
identifies it as a full root or radical, conjugate generation gives binary
degree at most 10r or 12r respectively. The original actor need not remain
cubic after replacement. The argument needs no tensor fixed-space formula.

This module proves the representation-theoretic implication and its literal
source applications. Elementary placement, invariant-subgroup classification,
and the two conjugate-generation assertions remain explicit group-theoretic
premises. They must be discharged before asserting the unconditional inner
degree estimate. In particular these conditional theorems do not complete
K.3.4 or the inner degree task.

The source application uses the original central quotient map followed by e,
through `coverEquiv`. Rank and fixed codimension are preserved on restriction
and transport. The last theorem consumes the actual `TensorParameters` with
`sourceDerivedEquiv` and applies the existing degree gap.

Source: Guralnick--Malle, *Classification of 2F-modules II*, Lemma 2.1 and
Proposition 6.2 part 1A, author manuscript pp.5--6,38--39; Aschbacher--Smith,
K.3.4, printed pp.451,456--457. Shared subgroups and cardinalities are in
`InnerDegree.Setup`; reusable offender maximization is in `TwoWeightMaximizer`.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem finrank_le_twelve_mul_of_geometry
    (ρ : Representation (ZMod 2) (Sp F) V) {r : ℕ} (hF : Nat.card F = 2 ^ r)
    (hfix : fixedSpace ρ ⊤ = ⊥)
    (hnormal : ∀ (i : Bool) (B : Subgroup (Sp F)), B ≤ radical i → B ≠ ⊥ →
      normalizer (radical (F := F) i : Set (Sp F)) ≤ normalizer (B : Set (Sp F)) →
      B = centralRoot i ∨ B = radical i)
    (hroot : ∀ i : Bool, ∃ c : Fin 5 → Sp F,
      (⨆ j, (centralRoot i).map (MulAut.conj (c j)).toMonoidHom) = ⊤)
    (hrad : ∀ i : Bool, ∃ c : Fin 2 → Sp F,
      (⨆ j, (radical i).map (MulAut.conj (c j)).toMonoidHom) = ⊤)
    (A : Subgroup (Sp F)) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim ρ A ≤ 2 * rank A)
    (hplace : ∃ (g : Sp F) (i : Bool), A.map (MulAut.conj g).toMonoidHom ≤ radical i) :
    Module.finrank (ZMod 2) V ≤ 12 * r := by
  obtain ⟨g, i, hplace⟩ := hplace
  have hc : fixedCodim ρ (A.map (MulAut.conj g).toMonoidHom) ≤
      2 * rank (A.map (MulAut.conj g).toMonoidHom) := by
    rwa [fixedCodim_map_conj, rank_map_conj]
  obtain ⟨B, hBU, hB, hBN, hV⟩ :=
    TwoWeight.exists_normalized_offender ρ (radical i) hplace (hA.map_conj g) hc
  rcases hnormal i B hBU hB hBN with hrootB | hradB
  · obtain ⟨c, hc⟩ := hroot i
    rw [hrootB] at hV
    have hd := TwoWeight.finrank_le_of_conjugates ρ hfix hV
      (by rw [card_centralRoot, hF] : Nat.card (centralRoot i) ≤ 2 ^ r) c hc
    omega
  · obtain ⟨c, hc⟩ := hrad i
    rw [hradB] at hV
    have hd := TwoWeight.finrank_le_of_conjugates ρ hfix hV
      (by rw [card_radical, hF, ← pow_mul, Nat.mul_comm r 3] :
        Nat.card (radical i) ≤ 2 ^ (3 * r)) c hc
    omega

variable {G : Type*} [Group G] [Finite G]
  {ρG : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The original component action satisfies the degree bound once the intrinsic parabolic geometry is supplied. No tensor degree assumption is used. -/
theorem source_inner_degree_of_geometry {K : GroupClass}
    (h : SourceHypothesis K ρG L) {r : ℕ} (hF : Nat.card F = 2 ^ r)
    (e : L ⧸ center L ≃* Sp F)
    (hplace : ∀ A : Subgroup (Sp F), IsElementaryTwo A →
      ∃ (g : Sp F) (i : Bool), A.map (MulAut.conj g).toMonoidHom ≤ radical i)
    (hnormal : ∀ (i : Bool) (B : Subgroup (Sp F)), B ≤ radical i → B ≠ ⊥ →
      normalizer (radical (F := F) i : Set (Sp F)) ≤ normalizer (B : Set (Sp F)) →
      B = centralRoot i ∨ B = radical i)
    (hroot : ∀ i : Bool, ∃ c : Fin 5 → Sp F,
      (⨆ j, (centralRoot i).map (MulAut.conj (c j)).toMonoidHom) = ⊤)
    (hrad : ∀ i : Bool, ∃ c : Fin 2 → Sp F,
      (⨆ j, (radical i).map (MulAut.conj (c j)).toMonoidHom) = ⊤)
    (A : Subgroup L) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim (ρG.comp L.subtype) A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 12 * r := by
  let : Theory.GroupTheory.IsQuasisimple L := h.quasisimple
  let : IsIrreducible (ρG.comp L.subtype) := h.irreducible
  let d := coverEquiv (ρG.comp L.subtype) (h.faithful.comp Subtype.val_injective) e
  let σ : Representation (ZMod 2) (Sp F) V := (ρG.comp L.subtype).comp d.symm.toMonoidHom
  have hf : Function.Injective σ :=
    (h.faithful.comp Subtype.val_injective).comp d.symm.injective
  have hi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff d.symm.toMonoidHom d.symm.surjective _).mpr h.irreducible
  let : IsSimpleGroup (L ⧸ center L) := Theory.GroupTheory.IsQuasisimple.simple
  let : IsSimpleGroup (Sp F) := e.symm.isSimpleGroup
  have hfix : fixedSpace σ ⊤ = ⊥ := by
    have he : fixedSpace σ ⊤ = σ.invariants := by
      ext v
      exact ⟨fun hv x => hv ⟨x, mem_top x⟩, fun hv x => hv x⟩
    rw [he, invariants_eq_bot_of_faithful_irreducible σ hf hi]
  let B := A.map d.toMonoidHom
  have hB : IsElementaryTwo B := by
    let : IsElementaryAbelian 2 A := hA.2
    exact ⟨fun hz => hA.1 ((map_eq_bot_iff_of_injective A d.injective).mp hz),
      IsElementaryAbelian.map _⟩
  have hrank : rank B = rank A := rank_map_injective d.toMonoidHom d.injective A
  have hcod : fixedCodim σ B = fixedCodim (ρG.comp L.subtype) A := by
    have hm : B.map d.symm.toMonoidHom = A := by
      dsimp only [B]
      rw [map_map]
      simp
    unfold fixedCodim
    rw [fixedSpace_comp_map, hm]
  exact finrank_le_twelve_mul_of_geometry σ hF hfix hnormal hroot hrad B hB
    (by rwa [hcod, hrank]) (hplace B hB)

/-- Restrict an actual ambient actor A ≤ L and preserve its original rank and fixed codimension before applying the parabolic argument. -/
theorem source_ambient_inner_degree_of_geometry {K : GroupClass}
    (h : SourceHypothesis K ρG L) {r : ℕ} (hF : Nat.card F = 2 ^ r)
    (e : L ⧸ center L ≃* Sp F)
    (hplace : ∀ A : Subgroup (Sp F), IsElementaryTwo A →
      ∃ (g : Sp F) (i : Bool), A.map (MulAut.conj g).toMonoidHom ≤ radical i)
    (hnormal : ∀ (i : Bool) (B : Subgroup (Sp F)), B ≤ radical i → B ≠ ⊥ →
      normalizer (radical (F := F) i : Set (Sp F)) ≤ normalizer (B : Set (Sp F)) →
      B = centralRoot i ∨ B = radical i)
    (hroot : ∀ i : Bool, ∃ c : Fin 5 → Sp F,
      (⨆ j, (centralRoot i).map (MulAut.conj (c j)).toMonoidHom) = ⊤)
    (hrad : ∀ i : Bool, ∃ c : Fin 2 → Sp F,
      (⨆ j, (radical i).map (MulAut.conj (c j)).toMonoidHom) = ⊤)
    (A : Subgroup G) (hAL : A ≤ L) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim ρG A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 12 * r := by
  let : IsElementaryAbelian 2 A := hA.2
  have hAE : IsElementaryTwo (A.subgroupOf L) := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAL⟩
    intro hz
    apply hA.1
    rw [← map_subgroupOf_eq_of_le hAL, hz, Subgroup.map_bot]
  apply source_inner_degree_of_geometry h hF e hplace hnormal hroot hrad _ hAE
  rwa [fixedCodim_subgroupOf ρG hAL, rank_subgroupOf hAL]

omit [CharP F 2] in
/-- Literal application to the supplied periodic tensor parameters. This remains conditional on the displayed intrinsic group geometry. -/
theorem source_inner_selection_of_geometry [Algebra (ZMod 2) F] {K : GroupClass}
    (h : SourceHypothesis K ρG L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2 ^ r)
    (e : L ⧸ center L ≃* Sp F)
    (P : @TensorParameters F L V _ _ _ _ _ _ _ (ρG.comp L.subtype) h.irreducible
      (sourceDerivedEquiv h hr hF e) r)
    (hplace : ∀ A : Subgroup (Sp F), IsElementaryTwo A →
      ∃ (g : Sp F) (i : Bool), A.map (MulAut.conj g).toMonoidHom ≤ radical i)
    (hnormal : ∀ (i : Bool) (B : Subgroup (Sp F)), B ≤ radical i → B ≠ ⊥ →
      normalizer (radical (F := F) i : Set (Sp F)) ≤ normalizer (B : Set (Sp F)) →
      B = centralRoot i ∨ B = radical i)
    (hroot : ∀ i : Bool, ∃ c : Fin 5 → Sp F,
      (⨆ j, (centralRoot i).map (MulAut.conj (c j)).toMonoidHom) = ⊤)
    (hrad : ∀ i : Bool, ∃ c : Fin 2 → Sp F,
      (⨆ j, (radical i).map (MulAut.conj (c j)).toMonoidHom) = ⊤)
    (A : Subgroup G) (hAL : A ≤ L) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim ρG A ≤ 2 * rank A) :
    letI := h.irreducible
    P.factors = 1 ∧ (P.blocks = 1 ∨ P.blocks = 2) := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let : IsIrreducible (ρG.comp L.subtype) := h.irreducible
  have hd := source_ambient_inner_degree_of_geometry h hF e hplace hnormal hroot hrad
    A hAL hA hcodim
  apply P.selection_of_degree_lt
  omega

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree
