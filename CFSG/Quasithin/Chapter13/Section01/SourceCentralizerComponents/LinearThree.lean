module
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.RootScalars.OddActors
public import Theory.GroupAction.NormalizerFrattiniRestriction
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.Basic
public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Source

/-!
# Excluding the marked PSL₃ row in the original centralizer sieve

Let A=O₂(X) and suppose X lies in a component marked as PSL₃ over a binary
field, with A marked as the full unipotent radical and a Sylow odd complement
P in the Borel. The actual normalizer of X preserves Z(A). The scalar action
and odd centralizer calculation force P to be cyclic, contrary to its Ξ odd
quotient. Frattini factorization supplies the needed complement irreducibility
from the original full action on X/O₂,Φ(X).

The canonical-radical application uses the same full centralizer action as
`source_centralizer_structure`; its odd quotient is supplied by the proved
`maximal_radical_structure`. The component-model sieve must still construct
X≤K and the exact full-unipotent marking. Borel placement follows from
normalization of the two-core. The SL₃ central cover and other
component rows are separate obligations.

Source: Aschbacher–Smith, proof of 13.1.12, final paragraph, printed p.875.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.RootScalars
open Matrix.PSL3.CartanActions Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem relative_center_subgroupOf {A K : Subgroup G} (hAK : A ≤ K) :
    ((center A).map A.subtype).subgroupOf K =
      (center (A.subgroupOf K)).map (A.subgroupOf K).subtype := by
  apply map_injective K.subtype_injective
  rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hAK),
    map_subgroup_center_eq _ K.subtype_injective,
    map_subgroupOf_eq_of_le hAK]

/-- The PSL₃ row with the literal two-core marked as the full unipotent radical
cannot occur for the original noncyclic irreducible odd actor. -/
theorem source_linearThree_twoCore_row_excluded
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] (hF : Nat.card F = 2 ^ n) (ho : Odd p)
    (X K P : Subgroup G) (hPX : P ≤ X) (hXK : X ≤ K)
    (e : K ≃* PSL(3,F))
    (hB : (P.subgroupOf K).map e.toMonoidHom ≤ borel F)
    (hA : ((X.pCoreIn 2).subgroupOf K).map e.toMonoidHom = unipotent F)
    (hP : XiOddQuotient p P)
    (hirr : IsNormalizerFrattiniIrreducible (P.subgroupOf (normalizer (X : Set G)))) :
    False := by
  let A := X.pCoreIn 2
  let R := (center A).map A.subtype
  have hAK : A ≤ K := (pCoreIn_le 2 X).trans hXK
  have hRK : R ≤ K := (map_subtype_le _).trans hAK
  have hMR : normalizer (X : Set G) ≤ normalizer (R : Set G) :=
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X)).trans
      (normalizer_le_normalizer_characteristic_image A (center A))
  have hR : (R.subgroupOf K).map e.toMonoidHom = projectiveCenter F := by
    rw [relative_center_subgroupOf hAK,map_subgroup_center_eq _ e.injective,hA]
    exact (projectiveCenter_eq_mapped_center F).symm
  exact hP.not_isCyclic (isCyclic_of_irreducible_borel_actor F hF ho
    (normalizer (X : Set G)) K P R (hPX.trans X.le_normalizer) (hPX.trans hXK)
    hRK hMR e hB hR hP.isPGroup hirr)

/-- The original full Ξ-action supplies irreducibility for its actual Sylow
complement, so the marked projective-linear row is impossible. -/
theorem source_Xi_linearThree_twoCore_row_excluded
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] (hF : Nat.card F = 2 ^ n) (ho : Odd p)
    (X M K : Subgroup G) (hXM : X ≤ M) (hn : M ≤ normalizer (X : Set G))
    (hq : XiOddQuotient p (XiQuotient X))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : M, ∀ a ∈ A, xiFrattiniAction M X hn s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hXK : X ≤ K) (e : K ≃* PSL(3,F)) (P : Sylow p X)
    (hB : (((P : Subgroup X).map X.subtype).subgroupOf K).map e.toMonoidHom ≤ borel F)
    (hA : ((X.pCoreIn 2).subgroupOf K).map e.toMonoidHom = unipotent F) : False := by
  let P₀ := (P : Subgroup X).map X.subtype
  have hPX : P₀ ≤ X := map_subtype_le _
  have hP : XiOddQuotient p P₀ :=
    hq.of_mulEquiv (RadicalActions.ambientSylowQuotientEquiv ho hq.isPGroup P).symm
  have hi : IsNormalizerFrattiniIrreducible (P₀.subgroupOf (normalizer (X : Set G))) :=
    normalizerFrattiniIrreducible_subgroupOf P₀ (M ⊓ normalizer (P₀ : Set G))
      (normalizer (X : Set G)) (hPX.trans X.le_normalizer) (inf_le_left.trans hn)
      inf_le_right (RadicalActions.normalizer_irreducible hn
        ((pCoreIn_le 2 X).trans hXM) hirr ho hq.isPGroup P)
  exact source_linearThree_twoCore_row_excluded F hF ho X K P₀ hPX hXK e hB hA hP hi

/-- At the actual source centralizer, the canonical Ξ radical rules out the
PSL₃ component marking with its full unipotent two-core. -/
theorem source_centralizer_linearThree_row_excluded
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G)
    (hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
        ∀ a ∈ A, xiFrattiniAction
          (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
          (XiP_invariant p inf_le_left) s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (K : Subgroup G) (hXK : XiP p L ≤ K)
    (e : K ≃* PSL(3,F)) (P : Sylow p (XiP p L))
    (hB : (((P : Subgroup (XiP p L)).map (XiP p L).subtype).subgroupOf K).map
      e.toMonoidHom ≤ borel F)
    (hA : (((XiP p L).pCoreIn 2).subgroupOf K).map e.toMonoidHom = unipotent F) :
    False := by
  have hq := (RadicalConjugateRigidity.maximal_radical_structure hG T hL hn ho hd).1
  exact source_Xi_linearThree_twoCore_row_excluded F hF ho (XiP p L)
    (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) K hXMu
    (XiP_invariant p inf_le_left) hq hirr hXK e P hB hA

/-- Marking the actual two-core as the full unipotent radical already places
the whole odd actor in the Borel, so no separate placement is needed. -/
theorem source_Xi_linearThree_unipotent_row_excluded
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] (hF : Nat.card F = 2 ^ n) (ho : Odd p)
    (X M K : Subgroup G) (hXM : X ≤ M) (hn : M ≤ normalizer (X : Set G))
    (hq : XiOddQuotient p (XiQuotient X))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : M, ∀ a ∈ A, xiFrattiniAction M X hn s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hXK : X ≤ K) (e : K ≃* PSL(3,F))
    (hA : ((X.pCoreIn 2).subgroupOf K).map e.toMonoidHom = unipotent F) : False := by
  have hnF : 0 < n := by
    have hc := Finite.one_lt_card (α := F)
    rw [hF] at hc
    by_contra h
    have hz : n = 0 := by omega
    simp [hz] at hc
  have hXA : X ≤ normalizer (X.pCoreIn 2 : Set G) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hnK : X.subgroupOf K ≤ normalizer ((X.pCoreIn 2).subgroupOf K : Set K) :=
    (comap_mono hXA).trans ((X.pCoreIn 2).le_normalizer_comap K.subtype)
  have hXB : (X.subgroupOf K).map e.toMonoidHom ≤ borel F := by
    have h := (map_mono (f := e.toMonoidHom) hnK).trans
      (((X.pCoreIn 2).subgroupOf K).le_normalizer_map e.toMonoidHom)
    rwa [hA,normalizer_unipotent F hnF hF] at h
  let P : Sylow p X := default
  exact source_Xi_linearThree_twoCore_row_excluded F hF ho X M K hXM hn hq hirr
    hXK e P ((map_mono (subgroupOf_mono K (map_subtype_le _))).trans hXB) hA

/-- The same elimination at the actual involution centralizer, with only the
model identification and the full-unipotent two-core equality remaining. -/
theorem source_centralizer_linearThree_unipotent_row_excluded
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G)
    (hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
        ∀ a ∈ A, xiFrattiniAction
          (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
          (XiP_invariant p inf_le_left) s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (K : Subgroup G) (hXK : XiP p L ≤ K)
    (e : K ≃* PSL(3,F))
    (hA : (((XiP p L).pCoreIn 2).subgroupOf K).map e.toMonoidHom = unipotent F) :
    False := by
  have hq := (RadicalConjugateRigidity.maximal_radical_structure hG T hL hn ho hd).1
  exact source_Xi_linearThree_unipotent_row_excluded F hF ho (XiP p L)
    (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) K hXMu
    (XiP_invariant p inf_le_left) hq hirr hXK e hA


end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
