module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.ModelNormalizers
public import Theory.SpecificGroups.SL3.QuinticRadical
public import Theory.SpecificGroups.SymplecticFour.RadicalParabolics.Exact
public import Theory.SpecificGroups.G2Even.RadicalNormalizers

/-!
# Full inner Sylow normalizers in the surviving radical normalizers

For SL₃(q), Sp₄(q), and G₂(q), the concrete radical-normalizer theorem
identifies a nontrivial two-radical normalizer with a parabolic or Borel.
Each contains a full inner Sylow normalizer. Transport to the literal
component image retains its central cover and the original field size.
The trivial radical is included separately. This supplies the model
normalizer required by the 11.4.2 Hall actor construction once its radical
image is placed in the component.

Source: Aschbacher--Smith 11.4.2, printed p.777, using Asc81b 8.2(7).
Imported G₂ calculations retain LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall

private theorem exists_sylow_normalizer_of_equiv
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (U : Subgroup A)
    (h : ∃ S : Sylow 2 B, normalizer (S : Set B) ≤ normalizer (U.map e.toMonoidHom : Set B)) :
    ∃ P : Sylow 2 A, normalizer (P : Set A) ≤ normalizer (U : Set A) := by
  obtain ⟨S,hS⟩ := h
  let P := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨P,?_⟩
  have he : (P : Subgroup A).map e.toMonoidHom = S := by
    change ((S : Subgroup B).map e.symm.toMonoidHom).map e.toMonoidHom = _
    have hc : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by
      ext x; exact e.apply_symm_apply x
    rw [map_map,hc,map_id]
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  change (normalizer ((P : Subgroup A) : Set A)).map e.toMonoidHom ≤ _
  rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq,he]
  exact hS

private theorem sp4_exists_sylow_normalizer
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (R : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) (hR : R.IsPRadical 2) :
    ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      normalizer (S : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) ≤
        normalizer (R : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) := by
  open Theory.SpecificGroups.SymplecticFour in
    obtain ⟨g,hg⟩ := radical_normalizer_eq_parabolic_or_borel R hR
  let e := MulAut.conj g
  apply exists_sylow_normalizer_of_equiv e R
  refine ⟨Theory.SpecificGroups.SymplecticFour.unipotentSylow hF hn,?_⟩
  rw [← map_equiv_normalizer_eq R e]
  change normalizer (Theory.SpecificGroups.SymplecticFour.unipotent (F := F) : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) ≤ _
  rw [← Theory.SpecificGroups.SymplecticFour.borel_eq_normalizer_unipotent]
  rcases hg with hp | hp | hb
  · rw [hp]; exact inf_le_left
  · rw [hp]; exact inf_le_right
  · rw [hb]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- Every radical core in a surviving component image has a normalizer
containing a full inner Sylow normalizer. The zero core is allowed. -/
theorem rankTwo_exists_sylow_normalizer
    (hm : RankTwoModel E) (U : Subgroup ((component E).map (projection E)))
    (hU : (normalizer (U : Set ((component E).map (projection E)))).pCoreIn 2 = U) :
    ∃ P : Sylow 2 ((component E).map (projection E)),
      normalizer (P : Set ((component E).map (projection E))) ≤
        normalizer (U : Set ((component E).map (projection E))) := by
  by_cases hb : U = ⊥
  · exact ⟨default,by rw [hb,normalizer_eq_top (⊥ : Subgroup _)]; exact le_top⟩
  have hr : U.IsPRadical 2 := ⟨hb,hU⟩
  rcases hm with hm | hm | hm
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let _ : Field F := hF
    let _ : Finite F := hfin
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    apply exists_sylow_normalizer_of_equiv e U
    exact Matrix.SL3.QuinticRadical.exists_sylow_normalizer_le F
      E.input.nonbinary hcard _ (hr.map_equiv e)
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let _ : Field F := hF
    let _ : Finite F := hfin
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    apply exists_sylow_normalizer_of_equiv e U
    exact sp4_exists_sylow_normalizer hcard E.input.field.degree_pos _ (hr.map_equiv e)
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let _ : Field F := hF
    let _ : Finite F := hfin
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    apply exists_sylow_normalizer_of_equiv e U
    exact Atlas.G2.exists_sylow_normalizer_le_radical_normalizer _ (hr.map_equiv e)

/-- The concrete radical normalizer has the required rank at each prime
dividing q−1, with no separately supplied Sylow or torus marking. -/
theorem rankTwo_radical_normalizer_rank
    (hm : RankTwoModel E) (U : Subgroup ((component E).map (projection E)))
    (hU : (normalizer (U : Set ((component E).map (projection E)))).pCoreIn 2 = U)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hd : p ∣ 2 ^ E.input.field.degree - 1) :
    2 ≤ primeRank p (normalizer (U : Set ((component E).map (projection E)))) := by
  obtain ⟨P,hP⟩ := rankTwo_exists_sylow_normalizer E hm U hU
  have hr := primeRank_mono p hP
  rwa [rankTwo_sylow_normalizer_primeRank E hm P hp hd] at hr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
