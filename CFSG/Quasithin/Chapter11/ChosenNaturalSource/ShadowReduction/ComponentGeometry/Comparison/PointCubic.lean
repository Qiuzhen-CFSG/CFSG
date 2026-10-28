module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.FieldFour
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality

/-!
# Point-fixed cubic containment in the original component comparison

The nonzero source point generates the fixed-free Irr⁺ seed under L.
Consequently N_G(L) intersect C_G(z) preserves V. The Hall actor constructed
inside Kz centralizes z, so whenever it lies in N_G(L), its cubic elements
satisfy the proved seed-stabilizer form of 11.0.4. This closes the original
SL₃(4) comparison even if V differs from its full normalizer orbit. Larger
fields use the existing noncubic actor argument.

The chosen-flag assembly discharges maximality, point quasisimplicity,
the full image catalogue, inner radical placement and actor choices under
the retained earlier-source inputs. Combining the three original natural
actions leaves only the escaping-normalizer block alternative, including
its actual block marking, V=V_M, C_T(L)=1 and V₁=Ω₁Z(R₁).

The block-center contradiction remains with
qt-d-1222-shadow-component-comparison. The normalized-module implication
retains qt-d-1222-normalized-nonff as producer; 3.2.5 retains qt-baumann-fsu.
The earlier geometry and final discharge stay with qt-d-1222-shadow-components.
This proves neither general cubic containment nor unconditional 11.4.2.
Source: Aschbacher--Smith 11.4.2, printed pp.776--777, using A.1.40--41,
11.0.4 and 11.1.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
open CFSG.Quasithin.ChapterB.QuasisimpleSource Overcomponent.EmbeddingProof
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

include D in
omit [Finite G] in
/-- With zero component fixed space, every nonidentity point of the
original Irr⁺ seed generates that seed under the original component. -/
theorem point_span_eq_seed
    (hf : V ⊓ centralizer (L : Set G) = ⊥) {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    conjugateSpanBy (zpowers z) L = V := by
  have hle := conjugateSpanBy_le (zpowers_le.mpr hz) D.normalizes
  have himage : ReducedNormal.subspaceImage (L ⊔ (T : Subgroup G)) D.space = V := D.image_eq
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer
    (L ⊔ (T : Subgroup G)) L le_sup_left D.irrPlus.isIrrPlus
    (conjugateSpanBy (zpowers z) L) (himage.symm ▸ hle)
    (le_normalizer_conjugateSpanBy _ _) with he | hc
  · exact he.trans himage
  · exact (hz1 (mem_bot.mp (hf ▸ (show z ∈ V ⊓ centralizer (L : Set G) from
      ⟨hz, hc (le_conjugateSpanBy _ _ (mem_zpowers z))⟩)))).elim

include D in
omit [Finite G] in
/-- A component normalizer fixing a generating point preserves its
chosen seed, even when the whole component normalizer moves that seed. -/
theorem point_centralizer_normalizes_seed
    (hf : V ⊓ centralizer (L : Set G) = ⊥) {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    normalizer (L : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (V : Set G) := by
  rw [← point_span_eq_seed (D := D) hf hz hz1]
  apply normalizes_conjugateSpanBy _ _ _ ?_ inf_le_left
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer (zpowers z : Set G))
  rw [zpowers_eq_closure,centralizer_closure]
  exact inf_le_right


/-- A cubic in N_G(L) fixing the original nonzero point preserves its
entire chosen seed, so the proved seed-stabilizer cubic theorem applies. -/
theorem sl3_point_cubic_mem
    (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    {z y : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hyM : y ∈ normalizer (L : Set G)) (hyz : y ∈ centralizer ({z} : Set G))
    (hy3 : orderOf y = 3) : y ∈ L :=
  LocalGeometry.Preliminary.sl3_orderThree_mem_of_normalizes_seed D S m heven hyM
    (point_centralizer_normalizes_seed (D := D) hf hz hz1 ⟨hyM,hyz⟩) hy3

/-- The actual point-fixed Hall actor closes the SL₃ comparison even
when the full normalizer does not preserve the chosen module. -/
theorem ofFlag_sl3_eq_of_maximal_of_normalizer
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  let := ofFlag_point_quasisimple_of_maximal S f X z H h hlinear h1132 hcent hline hXR e hne hstar
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hc := ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl
  have hm := Quasisimple.Classification.ofFlag_rankTwo_of_componentAlternative
    S f X z H h hne hstar hlinear h1132 hcent hline hXR hc e
  by_cases hfour : S.field.degree = 2
  · have hi := Quasisimple.Hall.rankTwo_radical_image_le_component (ofFlag S f X z H)
      h hf hne hstar hcent (f.invariant 0) e hm
    obtain ⟨p,Y,hp,ho,hd,hYK,hYR,_,hrY⟩ := Quasisimple.Hall.exists_odd_actor_of_inner_radical
      (ofFlag S f X z H) h hf hne hstar hcent hm hi
    let : Fact p.Prime := ⟨hp⟩
    have hYM := hYR.trans hNM
    have heven : Even S.field.degree := hfour ▸ (by decide : Even 2)
    have hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2^S.field.degree) →
        ∀ y ∈ Y, orderOf y = 3 → y ∈ L := by
      intro _ y hy h3
      exact sl3_point_cubic_mem S m heven hf ((ofFlag S f X z H).V₁_le h.point_mem)
        h.point_ne_one (hYM hy) (h.point_component.1 (hYK hy)) h3
    rw [← Quasisimple.Hall.primeRank_intersection_eq_of_source S c Y hYM ho hd hcubic] at hrY
    exact Quasisimple.Hall.ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132
      (Y ⊓ L) (inf_le_left.trans hYK) inf_le_right ho hrY
  · exact hne (Quasisimple.Hall.ofFlag_eq_of_rankTwo_of_normalizer_of_not_fieldFour
      S f X z H h hstar hlinear h1132 hcent e hm hfour hNM)

/-- Maximality and all component-image comparisons are discharged for
the original SL₃ action, including the noninvariant SL₃(4) branch. -/
theorem ofFlag_sl3_eq_of_normalizer_of_normalized_source
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (h325 : ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W), D.Source325Alternatives)
    (hpositive : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W),
        IsFFModule D.sourceOrbitNormalizerRepresentation ∨
          Chapter7.NormalizedSource.OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hs := ofFlag_point_mem_LStar_of_normalized_source S f X z H h hne hlinear h1132 e hcent
    h325 hpositive
  exact hne (ofFlag_sl3_eq_of_maximal_of_normalizer S f X z H h hlinear h1132 hcent hline hXR e
    hs m hNM)

/-- Every original natural action now closes when its actual radical
normalizer lies in N_G(L); no cubic or invariant-seed hypothesis remains. -/
theorem ofFlag_eq_of_normalizer_of_normalized_source
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (h325 : ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W), D.Source325Alternatives)
    (hpositive : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W),
        IsFFModule D.sourceOrbitNormalizerRepresentation ∨
          Chapter7.NormalizedSource.OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent)
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  cases c with
  | sl3 m =>
    exact ofFlag_sl3_eq_of_normalizer_of_normalized_source S f X z H h hlinear h1132
      hcent hline hXR e h325 hpositive m hNM
  | sp4 m =>
    exact ofFlag_sp4_eq_of_normalizer_of_normalized_source S f X z H h hlinear h1132
      hcent hline hXR e h325 hpositive m hNM
  | g2 m =>
    exact ofFlag_g2_eq_of_normalized_source S f X z H h hlinear h1132
      hcent hline hXR e h325 hpositive m (.inl hNM)

/-- The remaining comparison is exactly the escaping-normalizer block
alternative, with every original block clause retained. -/
theorem ofFlag_eq_or_block_of_normalized_source
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (h325 : ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W), D.Source325Alternatives)
    (hpositive : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W),
        IsFFModule D.sourceOrbitNormalizerRepresentation ∨
          Chapter7.NormalizedSource.OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K ∨
      ((ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) ∧
        V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
        (ofFlag S f X z H).V₁ = omegaOneAmbient
          ((center (ofFlag S f X z H).R₁).map (ofFlag S f X z H).R₁.subtype) ∧
        ¬ normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) := by
  by_cases hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)
  · exact .inl (ofFlag_eq_of_normalizer_of_normalized_source S f X z H h hlinear h1132
      hcent hline hXR e h325 hpositive hNM)
  · obtain ⟨hv,hb,ht,hz⟩ := hradical.resolve_left hNM
    exact .inr ⟨hb,hv,ht,hz,hNM⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
