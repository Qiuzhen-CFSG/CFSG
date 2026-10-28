module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairNatural
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree.ProductCalculation
public import Theory.SpecificGroups.SymmetricFive.SylowNormalizer
/-!
# The cubic obstruction for the native symmetric-five pair

The actual Sylow in the marked S₅ product is the product of its projections.
Both are self-normalizing. Independent Sylow normalization and exchange of
the two axes force the three-part of the invariant subgroup to be a square,
contradicting Sylow three-order three. All maps are transported through the
literal marked quotient-action coordinates.

Source: Aschbacher–Smith 13.6.14, printed p.929.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open SourceInduction
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}
private theorem sylow_eq_prod {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (S : Sylow 2 (A × B)) :
    (S : Subgroup (A × B)) = ((S : Subgroup _).map (MonoidHom.fst A B)).prod
      ((S : Subgroup _).map (MonoidHom.snd A B)) := by
  let S₁ := S.mapSurjective (show Function.Surjective (MonoidHom.fst A B) from fun g => ⟨(g,1),rfl⟩)
  let S₂ := S.mapSurjective (show Function.Surjective (MonoidHom.snd A B) from fun g => ⟨(1,g),rfl⟩)
  change (S : Subgroup _) = (S₁ : Subgroup A).prod (S₂ : Subgroup B)
  apply Eq.symm
  apply S.is_maximal'
  · obtain ⟨a,ha⟩ := S₁.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := S₂.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a+b)
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,ha,hb,pow_add]
  · intro x hx
    exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩

 theorem source_symmetric_pair_cubic_excluded (d : SourceTwoFactorCase ρ)
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (S : Sylow 2 D) (W : Subgroup D)
    (hSW : (S : Subgroup D) ≤ normalizer (W : Set D))
    (a : MulAut D) (hfirst : d.first.map a.toMonoidHom = d.second)
    (hsecond : d.second.map a.toMonoidHom = d.first)
    (hW : W.map a.toMonoidHom = W)
    (hthree : ∀ R : Sylow 3 W, Nat.card R = 3) : False := by
  let E := Equiv.Perm (Fin 5)
  let e : D ≃* E × E := c.action.groupEquiv
  let U := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let P := U.mapSurjective (f := MonoidHom.fst E E) (fun g => ⟨(g,1),rfl⟩)
  let Q := U.mapSurjective (f := MonoidHom.snd E E) (fun g => ⟨(1,g),rfl⟩)
  let X := W.map e.toMonoidHom
  let b : MulAut (E × E) := e.symm.trans (a.trans e)
  have hbe : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact congrArg e (congrArg a (e.symm_apply_apply x))
  have hX : X.map b.toMonoidHom = X := by
    change (W.map e.toMonoidHom).map b.toMonoidHom = _
    rw [map_map,hbe,← map_map,hW]
  have haxis (A B : Subgroup D) (hA : A = ((⊤ : Subgroup E).prod (⊥ : Subgroup E)).map e.symm.toMonoidHom)
      (hB : B = ((⊥ : Subgroup E).prod (⊤ : Subgroup E)).map e.symm.toMonoidHom)
      (hAB : A.map a.toMonoidHom = B) :
      ((⊤ : Subgroup E).prod (⊥ : Subgroup E)).map b.toMonoidHom =
        (⊥ : Subgroup E).prod (⊤ : Subgroup E) := by
    apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
    rw [map_map]
    have hb : e.symm.toMonoidHom.comp b.toMonoidHom = a.toMonoidHom.comp e.symm.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply _
    rw [hb,← map_map,← hA,← hB,hAB]
  have hf := haxis d.first d.second c.first_eq.symm c.second_eq.symm hfirst
  have hs : ((⊥ : Subgroup E).prod (⊤ : Subgroup E)).map b.toMonoidHom =
      (⊤ : Subgroup E).prod (⊥ : Subgroup E) := by
    apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
    rw [map_map]
    have hb : e.symm.toMonoidHom.comp b.toMonoidHom = a.toMonoidHom.comp e.symm.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply _
    rw [hb,← map_map,c.second_eq,c.first_eq,hsecond]
  have hn : (P : Subgroup E).prod Q ≤ normalizer (X : Set (E × E)) := by
    change ((U : Subgroup _).map (MonoidHom.fst E E)).prod
      ((U : Subgroup _).map (MonoidHom.snd E E)) ≤ _
    rw [← sylow_eq_prod U]
    change (S : Subgroup D).map e.toMonoidHom ≤ normalizer (W.map e.toMonoidHom : Set (E × E))
    rw [← map_equiv_normalizer_eq]
    exact map_mono hSW
  have hxthree (R : Sylow 3 X) : Nat.card R = 3 := by
    let ew := W.equivMapOfInjective e.toMonoidHom e.injective
    have hh := hthree (R.mapSurjective (f := ew.symm.toMonoidHom) ew.symm.surjective)
    change Nat.card ((R : Subgroup X).map ew.symm.toMonoidHom) = 3 at hh
    rwa [card_map_of_injective ew.symm.injective] at hh
  exact Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree.ProductCalculation.not_sylow_three_card_eq_three P Q
    (Theory.SpecificGroups.SymmetricFive.SylowNormalizer.sylow_normalizer_eq_self P)
    (Theory.SpecificGroups.SymmetricFive.SylowNormalizer.sylow_normalizer_eq_self Q)
    X hn b hf hs hX hxthree
end CFSG.Quasithin.ChapterB
