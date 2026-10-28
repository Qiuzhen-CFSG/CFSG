module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Geometry
public import CFSG.Quasithin.Chapter14.Section06.SourceOddCoreReduction
public import Theory.GroupTheory.CComponent.TwoRadical

/-!
# The radical and genuine component quotients in the terminal source branch

Assume original 14.6.18: every solvable member of H(T) lies in M.
For a solvable normal subgroup X of an outside H, a nontrivial O²(X)
would give a solvable outside overgroup O²(X)T by 14.6.1(4). Therefore
X is a two-group. This identifies the whole solvable radical with O₂(H),
and the subnormal radical calculus makes K/O₂(K) simple for every actual
C-component K of H. All normality here is relative to H.

The final consumers specialize to the original H=Mc, retaining the full
rank-two hypotheses. The component model list and diagram action of
14.6.20 are not assumed or asserted by these preparation lemmas.

Source: Aschbacher--Smith, 14.6.18--19, printed p.1037.
The input 14.6.18 is owned by qt-e-14625-source.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)

include hG hempty hM hunique hmany hcard e hab hsolv

/-- A solvable subgroup normal in an outside H lies in its actual two-core. -/
theorem source_solvable_normal_le_core
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (X : Subgroup G) (hXH : X ≤ H) (hHX : H ≤ normalizer (X : Set G))
    (hs : Group.IsSolvable X) : X ≤ H.pCoreIn 2 := by
  let := hs
  let R := (pResidual 2 X).map X.subtype
  have hr : pResidual 2 X = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ X.subtype_injective).mp
    by_contra hne
    have hHR : H ≤ normalizer (R : Set G) :=
      hHX.trans (normalizer_le_normalizer_characteristic_image X (pResidual 2 X))
    have hout := source_lemma_14_6_1_4 hG T hempty hM hunique hmany hcard e hab H hH
      R ((map_subtype_le _).trans hXH) hHR (isPPerfect_embedded_pResidual 2 X) hne
    let : Group.IsSolvable R := Group.isSolvable_of_surjective
      (f := (equivMapOfInjective (pResidual 2 X) X.subtype X.subtype_injective).toMonoidHom)
      (equivMapOfInjective (pResidual 2 X) X.subtype X.subtype_injective).surjective
    let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
    have hRT : Group.IsSolvable (R ⊔ (T : Subgroup G) : Subgroup G) :=
      Group.isSolvable_sup_of_normalizes R (T : Subgroup G) (hH.1.2.trans hHR)
    exact hout.2 (hsolv _ hout.1 hRT)
  have hXp : IsPGroup 2 X := (isPGroup_quotient_pResidual (G := X) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 X)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk',hr])
  exact le_pCoreIn_of_normalizes hXp hXH hHX

/-- The solvable radical of each outside H is exactly O₂(H). -/
theorem source_radical_eq_core
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    solvableRadical H = pCore 2 H := by
  let X := (solvableRadical H).map H.subtype
  have hHX : H ≤ normalizer (X : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (solvableRadical H).le_normalizer_map H.subtype
  have hs : Group.IsSolvable X := Group.isSolvable_of_surjective
    (f := (equivMapOfInjective (solvableRadical H) H.subtype H.subtype_injective).toMonoidHom)
    (equivMapOfInjective (solvableRadical H) H.subtype H.subtype_injective).surjective
  have hle := source_solvable_normal_le_core hG T hempty hM hunique hmany hcard e hab hsolv
    H hH X (map_subtype_le _) hHX hs
  apply le_antisymm ((map_le_map_iff_of_injective H.subtype_injective).mp hle)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  exact le_solvableRadical _ inferInstance inferInstance

/-- Original 14.6.19(1), expressed on the literal two-core quotient. -/
theorem source_quotient_oddCore_eq_bot
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    pPrimeCore 2 (H ⧸ pCore 2 H) = ⊥ := by
  by_contra hn
  obtain ⟨J,_,hJ,hs⟩ := source_solvable_minimal_outside_of_oddCore
    hG T hempty hM hunique hmany hcard e hab H hH hn
  exact hJ.1.2 (hsolv J hJ.1.1 hs)

/-- Original 14.6.19(2): the original component carrier has simple quotient.
This is not yet the F.9.18 model identification. -/
theorem source_component_quotient_simple
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    IsSimpleGroup (K ⧸ pCore 2 K) := by
  let := hK.isSimpleGroup_quotient_twoCore_of_radical_eq
    (source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv H hH)
  let f := subgroupOfEquivOfLe hKH
  exact (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm.isSimpleGroup

/-- The terminal group is nonsolvable and has an actual relative C-component. -/
theorem terminal_exists_component :
    ¬ Group.IsSolvable Mc ∧ ∃ K : Subgroup G, K ≤ Mc ∧
      (K.subgroupOf Mc).IsCComponent ∧ IsSimpleGroup (K ⧸ pCore 2 K) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hn : ¬ Group.IsSolvable Mc := fun hs => hout.2 (hsolv Mc hout.1 hs)
  obtain ⟨A,hA⟩ := exists_isCComponent_of_not_isSolvable hn
  let K := A.map Mc.subtype
  have hK : (K.subgroupOf Mc).IsCComponent := by
    have he : K.subgroupOf Mc = A := comap_map_eq_self_of_injective Mc.subtype_injective A
    exact he ▸ hA
  exact ⟨hn,K,map_subtype_le A,hK,
    source_component_quotient_simple hG T hempty hM hunique hmany hcard e hab hsolv
      Mc hout K (map_subtype_le A) hK⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
