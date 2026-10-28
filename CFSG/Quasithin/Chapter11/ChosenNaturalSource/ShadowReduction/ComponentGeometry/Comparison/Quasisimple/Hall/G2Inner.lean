module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.InnerRadical
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.OuterOrder
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.GroupTheory.FiniteParabolicTransfer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.CartanFixed

/-!
# Inner placement and the Hall contradiction in odd-degree G₂

The literal component image in KzT/C(VK) is the generalized Fitting
subgroup. For a G₂(q) image it is centerless, so the quotient embeds in
its actual outer automorphism group. Its index divides the original
field degree and is a power of two. Odd degree therefore makes the
whole action quotient inner, in particular the original R₁ image.
The proved radical-normalizer construction now supplies the odd actor.

If the original chosen module is also G₂, the exact 11.1.5 alternative
places N_G(R₁) in N_G(L): both exceptional block types are excluded by
actual quotient comparisons. The G₂ prime-residual formula puts the
constructed actor inside L, giving the original Cartan contradiction.
This branch needs neither an omega-center inequality nor the SL₃
cubic-containment clause. Classification.lean applies it to the full
source component sieve; other image rows and even degrees remain.

Earlier-source and maximality premises keep their existing producers;
final discharge remains with qt-d-1222-shadow-component-comparison and
qt-d-1222-shadow-components. Source: Aschbacher--Smith 11.4.2, printed
p.777, using 11.0.4 and 11.1.5. Imported G₂ calculations retain
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open Classification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

private theorem g2_componentImage_center
    (hm : ClassificationModels.IsG2At (componentImage E) (2 ^ E.input.field.degree)) :
    center (componentImage E) = ⊥ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ E.input.field.degree from
      Nat.pow_lt_pow_right (by decide) E.input.nonbinary)
  apply bot_unique
  intro a ha
  have he : e a ∈ center (Atlas.G2.Model F) := (centerCongr e ⟨a,ha⟩).property
  rw [Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq,mem_bot] at he
  exact e.map_eq_one_iff.mp he

/-- The actual component outer group has order dividing the original field degree. -/
theorem g2_outer_card_dvd_degree
    (hm : ClassificationModels.IsG2At (componentImage E) (2 ^ E.input.field.degree)) :
    Nat.card (MulAut.Outer (componentImage E)) ∣ E.input.field.degree := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ E.input.field.degree from
      Nat.pow_lt_pow_right (by decide) E.input.nonbinary)
  rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
  exact (Atlas.G2.LieAutomorphismExtensions.outer_card_dvd_fieldAut hq).trans
    (dvd_of_eq (FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF))

/-- The quotient by the actual G₂ component embeds in its outer group. -/
theorem g2_componentImage_index_dvd_degree
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hm : ClassificationModels.IsG2At (componentImage E) (2 ^ E.input.field.degree)) :
    (componentImage E).index ∣ E.input.field.degree := by
  let := componentImage_normal E h
  have hF := (action_structure E h hf hne hstar hcent).2.1
  have hc : centralizer (componentImage E : Set (ActionQuotient E)) ≤ componentImage E := by
    rw [show componentImage E = generalizedFitting (ActionQuotient E) from hF]
    exact centralizer_generalizedFitting_le _
  have hz : centralizer (componentImage E : Set (ActionQuotient E)) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxz : (⟨x,hc hx⟩ : componentImage E) ∈ center (componentImage E) := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (hx k k.property)
    rw [g2_componentImage_center E hm,mem_bot] at hxz
    exact congrArg Subtype.val hxz
  exact (card_dvd_of_injective (MulAut.outerAction (componentImage E))
    (MulAut.outerAction_injective _ hz)).trans (g2_outer_card_dvd_degree E hm)

/-- The original action quotient is entirely inner in odd field degree. -/
theorem g2_componentImage_eq_top_of_odd_degree
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hm : ClassificationModels.IsG2At (componentImage E) (2 ^ E.input.field.degree))
    (ho : Odd E.input.field.degree) : componentImage E = ⊤ := by
  let := componentImage_normal E h
  have hd := g2_componentImage_index_dvd_degree E h hf hne hstar hcent hm
  obtain ⟨k,hk⟩ := (quotient_componentImage_isTwoGroup E h).exists_card_eq
  apply Subgroup.index_eq_one.mp
  exact Nat.eq_one_of_dvd_coprimes (ho.coprime_two_right.pow_right k) hd (dvd_of_eq hk)


/-- In particular the literal R₁ image is inner, with no placement premise. -/
theorem g2_radical_image_le_component_of_odd_degree
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hm : ClassificationModels.IsG2At (componentImage E) (2 ^ E.input.field.degree))
    (ho : Odd E.input.field.degree) :
    (radical E).map (projection E) ≤ componentImage E := by
  rw [g2_componentImage_eq_top_of_odd_degree E h hf hne hstar hcent hm ho]
  exact le_top

variable {E}

/-- The odd-degree G₂ image gives the Hall contradiction in the first branch of 11.1.5. -/
theorem ofFlag_eq_of_odd_g2_of_normalizer_le
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : ClassificationModels.IsG2At (componentImage (ofFlag S f X z H))
      (2 ^ S.field.degree)) (ho : Odd S.field.degree)
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ normalizer (L : Set G), orderOf y = 3 → y ∈ L) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hi := g2_radical_image_le_component_of_odd_degree (ofFlag S f X z H)
    h hf hne hstar hcent hm ho
  obtain ⟨p,Y,hp,hodd,hd,hYK,hYR,_,hrY⟩ := exists_odd_actor_of_inner_radical
    (ofFlag S f X z H) h hf hne hstar hcent (.inr (.inr hm)) hi
  let : Fact p.Prime := ⟨hp⟩
  have hYM := hYR.trans hNM
  rw [← primeRank_intersection_eq_of_source S c Y hYM hodd hd
    (fun hs y hy h3 => hcubic hs y (hYM hy) h3)] at hrY
  exact ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132
    (Y ⊓ L) (inf_le_left.trans hYK) inf_le_right hodd hrY

open Representation CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- For an original G₂ natural module, 11.1.5 and 11.0.4 discharge all Hall placement premises. -/
theorem ofFlag_g2_eq_of_odd_g2
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : ClassificationModels.IsG2At (componentImage (ofFlag S f X z H))
      (2 ^ S.field.degree)) (ho : Odd S.field.degree)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  have hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G) := by
    rcases hradical with hn | hb
    · exact hn
    · exact (LocalGeometry.Normalizers.PointCohomology.PointGeometry.no_g2_block_marking
        D S m hb.2.1).elim
  by_contra hne
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hi := g2_radical_image_le_component_of_odd_degree (ofFlag S f X z H)
    h hf hne hstar hcent hm ho
  obtain ⟨p,Y,hp,hodd,hd,hYK,hYR,hY,hrY⟩ := exists_odd_actor_of_inner_radical
    (ofFlag S f X z H) h hf hne hstar hcent (.inr (.inr hm)) hi
  let : Fact p.Prime := ⟨hp⟩
  have hYM := hYR.trans hNM
  have hYL : Y ≤ L := by
    rw [LocalGeometry.Preliminary.g2_prime_residual D S m hp
      (hd.trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2))]
    have hres : (Y.subgroupOf (normalizer (L : Set G))).map
        (normalizer (L : Set G)).subtype ≤
        (primeToResidual p (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype :=
      map_mono (le_primeToResidual_of_isPGroup
      (hY.comap_subtype : IsPGroup p (Y.subgroupOf (normalizer (L : Set G)))))
      (f := (normalizer (L : Set G)).subtype)
    rwa [map_subgroupOf_eq_of_le hYM] at hres
  exact ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132
    Y hYK hYL hodd hrY

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
