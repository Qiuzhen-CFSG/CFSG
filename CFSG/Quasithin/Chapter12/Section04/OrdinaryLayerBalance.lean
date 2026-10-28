module

public import CFSG.Quasithin.ChapterI.Section03.OrdinaryBalance
public import CFSG.Quasithin.Chapter12.Section04
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The ordinary-layer balance step of 12.4.8

In the source H = C_G(U₀), with U₀ a nontrivial hyperplane of U, and the
ordinary seed K is a component of C_G(U) = C_H(U). The preceding A.1.29
argument gives [K,O(H)] = 1. The genuine GLS II 5.22 orbit theorem places
the seed in a U-orbit of two-components; odd-core centralization makes the
selected component ordinary, and every conjugate then lies in E(H).

This module proves that deduction with the original centralizer inclusions,
seed and subtype maps. It retains the universal S₂ and GLS 5.22 inputs,
owned by qt-i03-two-schreier and qt-i-03-l-balance (using
qt-i03-two-layer-balance). The preceding A.1.29 odd-core centralization
remains an explicit source premise for qt-12-04-centralizer-bound, using
qt-a-01-rank-actions. It is not inferred just from a p-group action lemma.
There is no B₂ or projected-component quasisimplicity input.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 12.4.8, printed p.815, and GLS II, Proposition 5.22.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section04.OrdinaryLayerBalance
open Subgroup Theory.GroupTheory
universe u

/-- The orbit clause of the genuine universal GLS 5.22 theorem under S₂.
Its input is any two-component of the literal centralizer. The source
assembly must supply this theorem; no local orbit certificate is assumed. -/
def TwoComponentOrbit522 : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], HasTwoSchreier H →
    ∀ P : Subgroup H, IsPGroup 2 P →
      ∀ D : Subgroup (centralizer (P : Set H)), D.IsTwoComponent →
        ∃ J : Subgroup H, J.IsTwoComponent ∧
          componentOrbit (D.map (centralizer (P : Set H)).subtype) (oddELayer H) =
            componentOrbit J P

/-- Centralizing the actual odd core makes the GLS orbit ordinary, so its
ordinary seed lies in the ambient ordinary layer. No rank or B₂ assertion
about a quotient projection is needed. -/
theorem ordinary_seed_le_layer_of_gls522
    (source522 : TwoComponentOrbit522.{u})
    {H : Type u} [Group H] [Finite H] (hS2 : HasTwoSchreier H)
    (P D : Subgroup H) (hP : IsPGroup 2 P)
    (hD : IsComponentIn D (centralizer (P : Set H)))
    (hodd : D ≤ centralizer (pPrimeCore 2 H : Set H)) :
    D ≤ componentLayer H := by
  obtain ⟨J, hJ, he⟩ := source522 H hS2 P hP (D.subgroupOf (centralizer (P : Set H)))
    (ChapterI.Balance.ordinary_isTwoComponent hD.2)
  rw [map_subgroupOf_eq_of_le hD.1] at he
  have hJo : IsComponent H J :=
    ChapterI.Balance.pumpup_component_of_centralizes_oddCore P D J hJ he hodd
  have hOrbit : componentOrbit J P ≤ componentLayer H :=
    iSup_le fun p => le_sSup (hJo.map_conj p)
  exact (le_componentOrbit D (oddELayer H)).trans (he.le.trans hOrbit)

private theorem centralizer_sqtk
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (U₀ : Subgroup G) (hne : U₀ ≠ ⊥) (hp : IsPGroup 2 U₀) :
    IsSQTK CFSG.KnownSimple.IsKnownSimple (centralizer (U₀ : Set G)) := by
  have hN : IsSQTK CFSG.KnownSimple.IsKnownSimple (normalizer (U₀ : Set G)) :=
    hG.twoLocal_sqtk ⟨U₀, hne, hp, rfl⟩
  let f := inclusion (centralizer_le_normalizer (U₀ : Set G))
  exact ⟨hN.stronglyQuasithin.of_injective f (inclusion_injective _),
    hN.isKGroup.of_injective f (inclusion_injective _)⟩

/-- The actual source application on printed p.815. The SQTK centralizer
and the seed's inclusion in its embedded ordinary layer are constructed.
The preceding A.1.29 conclusion is expressed using the original odd-core
subtype map. U may be any abelian two-subgroup, in particular the source
hyperplane of the elementary abelian natural module. -/
theorem source_12_4_8_seed_layer_and_sqtk
    (sourceS2 : ChapterI.OrdinaryBalance.SimpleSylowFixerSolvability.{u})
    (source522 : TwoComponentOrbit522.{u})
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (U U₀ K : Subgroup G) [IsMulCommutative U]
    (hU : IsPGroup 2 U) (hU₀U : U₀ ≤ U) (hU₀ : U₀ ≠ ⊥)
    (hK : IsComponentIn K (centralizer (U : Set G)))
    (hodd : K ≤ centralizer
      (((pPrimeCore 2 (centralizer (U₀ : Set G))).map
        (centralizer (U₀ : Set G)).subtype) : Set G)) :
    IsSQTK CFSG.KnownSimple.IsKnownSimple (centralizer (U₀ : Set G)) ∧
      K ≤ (componentLayer (centralizer (U₀ : Set G))).map
        (centralizer (U₀ : Set G)).subtype := by
  let H := centralizer (U₀ : Set G)
  have hUH : U ≤ H := (le_centralizer U).trans (centralizer_le hU₀U)
  have hKH : K ≤ H := hK.1.trans (centralizer_le hU₀U)
  let P := U.subgroupOf H
  let D := K.subgroupOf H
  have hP : IsPGroup 2 P := hU.of_equiv (subgroupOfEquivOfLe hUH).symm
  have hDC : D ≤ centralizer (P : Set H) := by
    intro x hx y hy
    exact Subtype.ext (hK.1 hx (y : G) hy)
  let f : centralizer (P : Set H) →* centralizer (U : Set G) :=
    { toFun := fun x => ⟨((x : H) : G), by
        intro y hy
        exact congrArg Subtype.val (x.property ⟨y, hUH hy⟩ hy)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hD : IsComponentIn D (centralizer (P : Set H)) := by
    refine ⟨hDC, ?_, ?_⟩
    · exact hK.2.1.comap f
    · let : IsQuasisimple K := hK.quasisimple
      let : IsQuasisimple D := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKH).symm
      exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hDC).symm
  have hDO : D ≤ centralizer (pPrimeCore 2 H : Set H) := by
    intro x hx y hy
    exact Subtype.ext (hodd hx (y : G) (mem_map_of_mem H.subtype hy))
  have hDL : D ≤ componentLayer H := ordinary_seed_le_layer_of_gls522 source522
    (ChapterI.OrdinaryBalance.hasTwoSchreier_of_simpleSylowFixer sourceS2 H) P D hP hD hDO
  refine ⟨centralizer_sqtk hG U₀ hU₀ (hU.to_le hU₀U), ?_⟩
  have hm := map_mono (f := H.subtype) hDL
  change (K.subgroupOf H).map H.subtype ≤ (componentLayer H).map H.subtype at hm
  rwa [map_subgroupOf_eq_of_le hKH] at hm

end CFSG.Quasithin.Chapter12.Section04.OrdinaryLayerBalance
