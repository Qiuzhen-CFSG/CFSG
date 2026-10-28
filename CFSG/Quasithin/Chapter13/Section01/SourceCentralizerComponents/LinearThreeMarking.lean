module
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.UnipotentCore
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.LinearThree
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.Containment
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Constructing and consuming the PSL₃ unipotent marking

A Sylow two-subgroup of the component normalizing the canonical radical
places that radical in a Borel subgroup. Its noncyclic odd complement moves
both simple roots, so the literal two-core equals the full unipotent group.
This constructs the marking required by the scalar-action exclusion.

At the original involution centralizer, irreducibility of the actual
component-normalizer actor supplies X ≤ K; the original A/C results discharge
the model inputs to that containment theorem. The local centralizer Sylow
upgrade and subnormal intersection supply the required component Sylow.
Thus the final theorem assumes neither containment nor a marking equality.

This excludes the concrete PSL₃ row for n ≥ 2 in the irreducible branch.
It does not identify a two-core quotient with the full component, nor discard
central covers. Their recognition and the SL₃ row remain separate inputs to
the complete source component sieve.

Source: Aschbacher–Smith, proof of 13.1.12, printed pp.874–875.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- A genuine Sylow subgroup normalizing the canonical odd radical constructs
the full-unipotent marking needed by the PSL₃ exclusion. -/
theorem source_Xi_exists_linearThree_unipotent_marking
    (F : Type*) [Field F] [Finite F]
    {n p : ℕ} [Fact p.Prime] (hnF : 2 ≤ n) (hF : Nat.card F = 2^n) (ho : Odd p)
    (X K : Subgroup G) (hXK : X ≤ K) (e : K ≃* PSL(3,F))
    (hq : XiOddQuotient p (XiQuotient X))
    (S : Sylow 2 K) (hSX : (S : Subgroup K).map K.subtype ≤ normalizer (X : Set G)) :
    ∃ f : K ≃* PSL(3,F), ((X.pCoreIn 2).subgroupOf K).map f.toMonoidHom = unipotent F := by
  let P : Sylow p X := default
  let P₀ := (P : Subgroup X).map X.subtype
  have hPX : P₀ ≤ X := map_subtype_le _
  have hPK : P₀ ≤ K := hPX.trans hXK
  have hP : XiOddQuotient p P₀ :=
    hq.of_mulEquiv (RadicalActions.ambientSylowQuotientEquiv ho hq.isPGroup P).symm
  let Y := X.subgroupOf K
  let Q := P₀.subgroupOf K
  let : Group.IsSolvable X := by
    let : Group.IsNilpotent (XiQuotient X) := hq.isPGroup.isNilpotent
    let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
    exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr
      ⟨inferInstance,inferInstance⟩
  let : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hXK).toMonoidHom) (subgroupOfEquivOfLe hXK).injective
  have hSY : (S : Subgroup K) ≤ normalizer (Y : Set K) := by
    intro s hs
    exact X.le_normalizer_comap K.subtype (hSX (mem_map_of_mem K.subtype hs))
  have hQnc : ¬ IsCyclic Q := fun hc =>
    hP.not_isCyclic ((subgroupOfEquivOfLe hPK).isCyclic.mp hc)
  obtain ⟨f,hf⟩ := UnipotentCore.exists_unipotent_marking F hnF hF ho e S Y Q
    (subgroupOf_mono K hPX) hP.isPGroup.comap_subtype hQnc hSY
  have hc : Y.pCoreIn 2 = (X.pCoreIn 2).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_pCoreIn_of_injective 2 Y K.subtype K.subtype_injective]
    change (X.subgroupOf K |>.map K.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le hXK,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hXK)]
  exact ⟨f,hc ▸ hf⟩

/-- The original full Xi action excludes the PSL₃ row once its actual
component containment and Sylow normalization are available; no unipotent
or Borel marking equality remains as an input. -/
theorem source_Xi_linearThree_row_excluded_of_sylow
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] (hnF : 2 ≤ n) (hF : Nat.card F = 2^n) (ho : Odd p)
    (X M K : Subgroup G) (hXM : X ≤ M) (hn : M ≤ normalizer (X : Set G))
    (hq : XiOddQuotient p (XiQuotient X))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : M, ∀ a ∈ A, xiFrattiniAction M X hn s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hXK : X ≤ K) (e : K ≃* PSL(3,F)) (S : Sylow 2 K)
    (hSX : (S : Subgroup K).map K.subtype ≤ normalizer (X : Set G)) : False := by
  obtain ⟨f,hf⟩ := source_Xi_exists_linearThree_unipotent_marking F hnF hF ho X K hXK e hq S hSX
  exact source_Xi_linearThree_unipotent_row_excluded F hF ho X M K hXM hn hq hirr hXK f hf

/-- At the literal source centralizer, the actual component Sylow constructs
and discharges the full-unipotent marking. -/
theorem source_centralizer_linearThree_row_excluded_of_sylow
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
    {n : ℕ} (hnF : 2 ≤ n) (hF : Nat.card F = 2^n)
    (K : Subgroup G) (hXK : XiP p L ≤ K) (e : K ≃* PSL(3,F))
    (S : Sylow 2 K)
    (hSX : (S : Subgroup K).map K.subtype ≤ normalizer (XiP p L : Set G)) : False := by
  have hq := (RadicalConjugateRigidity.maximal_radical_structure hG T hL hn ho hd).1
  exact source_Xi_linearThree_row_excluded_of_sylow F hnF hF ho (XiP p L)
    (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) K hXMu
    (XiP_invariant p inf_le_left) hq hirr hXK e S hSX

/-- In the irreducible component-normalizer branch of the original sieve,
the actual source Sylow subgroup constructs both component containment and
the full-unipotent marking. The original A/C theorems are discharged. -/
theorem source_centralizer_linearThree_irreducible_row_excluded
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G) (hu : orderOf u = 2)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)))
    (hindex : ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2)
    (hcentral : ∀ g : G,
      (T : Subgroup G) ≤ centralizer ({g * u * g⁻¹} : Set G) →
        centralizer ({g * u * g⁻¹} : Set G) ≤ normalizer (L : Set G))
    (hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
    (K : Subgroup G) (hK : K ∈ cComponentsIn (centralizer ({u} : Set G)))
    (hQK : IsQuasisimple (XiQuotient K))
    (hXnK : XiP p L ≤ normalizer (K : Set G)) (hmove : ⁅K,XiP p L⁆ = K)
    (hirrK : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ s : ((normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) ⊓
          normalizer (K : Set G) : Subgroup G), ∀ a ∈ A,
        xiFrattiniAction
          ((normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) ⊓ normalizer (K : Set G))
          (XiP p L) (inf_le_left.trans (XiP_invariant p inf_le_left)) s a ∈ A) →
            A=⊥ ∨ A=⊤)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hnF : 2 ≤ n) (hF : Nat.card F = 2^n) (e : K ≃* PSL(3,F)) : False := by
  have hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
        ∀ a ∈ A, xiFrattiniAction
          (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
          (XiP_invariant p inf_le_left) s a ∈ A) → A=⊥ ∨ A=⊤ := by
    intro A hA
    apply hirrK A
    intro s a ha
    exact hA ⟨s,s.property.1⟩ a ha
  have hXK := source_XiP_le_component_of_normalizer_irreducible
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hG T hL hn ho hd u hu hXMu K hK hQK hXnK hmove hirrK
  have hS := SourceCentralizerSylow.source_centralizer_sylow hG T hL hn ho hd
    u hTM hlocal hindex hcentral hXMu hirr
  obtain ⟨S,hSmap,_⟩ := component_sylow_normalizes_radical
    (centralizer ({u} : Set G)) (XiP p L) K
    ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) hK hS
    (XiP_invariant p (inf_le_left.trans hTM))
  apply source_centralizer_linearThree_row_excluded_of_sylow hG T hL hn ho hd
    u hXMu hirr F hnF hF K hXK e S
  rw [hSmap]
  exact inf_le_left.trans (XiP_invariant p (inf_le_left.trans hTM))

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
