module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.NoncubicHall

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.SourceModules

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicSeed

/-!
# Field-four comparison and the remaining original block cases

The complete nonquasisimple theorem makes every strict maximal point
component quasisimple, at field four as well as at larger fields. The
proved proper-overcomponent comparison supplies maximality from the exact
preceding 3.2.5 and normalized FF-or-orthogonal implications. Applying the
full image sieve and the literal radical-image Hall actor then proves the
original G₂ comparison in every field. The Sp₄ comparison also closes in
every field when N_G(R₁) lies in N_G(L); no cubic input is required.

For an invariant original SL₃ seed, the checked cubic-containment theorem
handles field four, while the noncubic argument handles larger fields.
The actual chosen-flag consumer therefore leaves exactly an SL₃(4) action
with V different from its normalizer orbit and N_G(R₁) ≤ N_G(L), or the
original escaping-normalizer block alternative. Every block clause is
retained: the actual block marking, V=V_M, C_T(L)=1, and V₁=Ω₁Z(R₁).
The symplectic specialization identifies its block as Sp₄(4), by comparing
the literal two-core quotient markings and Sylow orders.

The block-center contradiction and noninvariant SL₃(4) branch remain with
qt-d-1222-shadow-component-comparison. The preceding normalized-module
implication remains with qt-d-1222-normalized-nonff, and 3.2.5 with
qt-baumann-fsu. Earlier geometry, the original seed quotient marking and
final earlier-source discharge remain with qt-d-1222-shadow-components.
No unconditional 11.4.2 or completion of these inputs is asserted here.
Source: Aschbacher--Smith 11.4.2, printed pp.776--777, using 11.0.4,
11.1.5, 3.2.5 and 7.0.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
open CFSG.Quasithin.ChapterB.QuasisimpleSource Overcomponent.EmbeddingProof
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The complete nonquasisimple comparison forces quasisimplicity of a
strict maximal point component, including at field order four. The original
seed marking supplies nontriviality and the entire component catalogue. -/
theorem ofFlag_point_quasisimple_of_maximal
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
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G)) :
    IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) := by
  by_contra hn
  have hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  have hl := LocalGeometry.Components.flag_mem_local_of_model D S f 0 hseed
  have hA : f.Li 0 ≠ ⊥ := by
    intro hb
    exact hl.1.ne_bot (by rw [hb]; exact bot_subgroupOf _)
  exact hne (ofFlag_eq_of_nonquasisimple S f X z H h hA hseed hlinear h1132 hstar hn
    (le_centralizer_iff.mp hcent) hline hXR
    (ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl))

/-- The symplectic Hall comparison uses its prime-residual theorem also
at field four. The full image sieve and inner placement construct the actor;
no cubic-containment or omega-center premise is needed. -/
theorem ofFlag_sp4_eq_of_maximal_of_normalizer
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
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  let := ofFlag_point_quasisimple_of_maximal S f X z H h hlinear h1132 hcent hline hXR e hne hstar
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hc := ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl
  have hm := Quasisimple.Classification.ofFlag_rankTwo_of_componentAlternative
    S f X z H h hne hstar hlinear h1132 hcent hline hXR hc e
  have hi := Quasisimple.Hall.rankTwo_radical_image_le_component (ofFlag S f X z H)
    h hf hne hstar hcent (f.invariant 0) e hm
  obtain ⟨p,Y,hp,hodd,hd,hYK,hYR,hY,hrY⟩ := Quasisimple.Hall.exists_odd_actor_of_inner_radical
    (ofFlag S f X z H) h hf hne hstar hcent hm hi
  let : Fact p.Prime := ⟨hp⟩
  have hYM := hYR.trans hNM
  have hYL : Y ≤ L := by
    rw [LocalGeometry.Preliminary.sp4_prime_residual D S m hp
      (hd.trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2))]
    have hr := map_mono (le_primeToResidual_of_isPGroup
      (hY.comap_subtype : IsPGroup p (Y.subgroupOf (normalizer (L : Set G)))))
      (f := (normalizer (L : Set G)).subtype)
    change (Y.subgroupOf (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype ≤ _ at hr
    rwa [map_subgroupOf_eq_of_le hYM] at hr
  exact Quasisimple.Hall.ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132
    Y hYK hYL hodd hrY

/-- The original G₂ comparison in every field, including four. The two
previous source implications supply maximality, and the complete
nonquasisimple and quasisimple comparisons discharge every image branch. -/
theorem ofFlag_g2_eq_of_normalized_source
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
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree)
    : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hs := ofFlag_point_mem_LStar_of_normalized_source S f X z H h hne hlinear h1132 e hcent
    h325 hpositive
  let := ofFlag_point_quasisimple_of_maximal S f X z H h hlinear h1132 hcent hline hXR e hne hs
  exact hne (Quasisimple.Classification.ofFlag_g2_eq S f X z H h hs hlinear h1132 hcent hline hXR
    (ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl) e m hradical)

/-- Maximality and point quasisimplicity are internal to the symplectic
normalizer-contained comparison at every field size. -/
theorem ofFlag_sp4_eq_of_normalizer_of_normalized_source
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
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hs := ofFlag_point_mem_LStar_of_normalized_source S f X z H h hne hlinear h1132 e hcent
    h325 hpositive
  exact hne (ofFlag_sp4_eq_of_maximal_of_normalizer S f X z H h hlinear h1132 hcent hline hXR e
    hs m hNM)

/-- The invariant chosen SL₃ seed supplies cubic containment at field
four. Larger fields use a prime greater than three. Thus no cubic premise
is needed in this entire normalizer-contained, invariant-seed branch. -/
theorem ofFlag_sl3_eq_of_normalizer_of_fullModule_of_normalized_source
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
    (hfull : V = Source.conjugateSpan (normalizer (L : Set G)) V)
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_cases hfour : S.field.degree = 2
  · by_contra hne
    have hs := ofFlag_point_mem_LStar_of_normalized_source S f X z H h hne hlinear h1132 e hcent
      h325 hpositive
    let := ofFlag_point_quasisimple_of_maximal S f X z H h hlinear h1132 hcent hline hXR e hne hs
    have hf := (fixed_and_transitive D S _ hlinear h1132).1
    have hc := ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl
    have hm := Quasisimple.Classification.ofFlag_rankTwo_of_componentAlternative
      S f X z H h hne hs hlinear h1132 hcent hline hXR hc e
    have hi := Quasisimple.Hall.rankTwo_radical_image_le_component (ofFlag S f X z H)
      h hf hne hs hcent (f.invariant 0) e hm
    obtain ⟨p,Y,hp,ho,hd,hYK,hYR,_,hrY⟩ := Quasisimple.Hall.exists_odd_actor_of_inner_radical
      (ofFlag S f X z H) h hf hne hs hcent hm hi
    let : Fact p.Prime := ⟨hp⟩
    have hYM := hYR.trans hNM
    have heven : Even S.field.degree := hfour ▸ (by decide : Even 2)
    have hfull' : componentOrbit V (normalizer (L : Set G)) = V := hfull.symm
    have hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2^S.field.degree) →
        ∀ y ∈ Y, orderOf y = 3 → y ∈ L := by
      intro _ y hy h3
      exact LocalGeometry.Preliminary.sl3_orderThree_mem_of_fullModule_eq
        D S m heven hfull' (hYM hy) h3
    rw [← Quasisimple.Hall.primeRank_intersection_eq_of_source S c Y hYM ho hd hcubic] at hrY
    exact Quasisimple.Hall.ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132
      (Y ⊓ L) (inf_le_left.trans hYK) inf_le_right ho hrY
  · exact ofFlag_eq_of_normalizer_of_not_fieldFour S f X z H h hlinear h1132 hcent hline hXR e
      hfour hNM

private theorem sp4_not_linear_block
    (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    ¬ ChapterC.IsSL3EvenBlock L S.field.degree := by
  rintro ⟨_,_,F,inst,fin,hF,hmodel⟩
  let : Field F := inst
  let : Finite F := fin
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let e : Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier ≃* SL(3,F) :=
    m.groupEquiv.symm.trans hmodel.quotient_iso.some
  let P := Theory.SpecificGroups.SymplecticFour.unipotentSylow S.field.card_eq S.field.degree_pos
  let Q := Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F S.field.degree_pos hF
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc : Nat.card P = Nat.card Q :=
    (Nat.card_congr ((P : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).trans
      (Nat.card_congr (Sylow.equiv R Q).toEquiv)
  change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := S.field.Carrier)) =
    Nat.card (Matrix.PSL3.LinearThree.unipotentSL F) at hc
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,
    Matrix.PSL3.LinearThree.card_unipotentSL, S.field.card_eq, hF, ← pow_mul, ← pow_mul] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  have hn := S.nonbinary
  omega

/-- The unresolved symplectic comparison is precisely the actual short
Sp₄(4) block alternative. Every original clause, including the literal
omega-center equality and escaping radical normalizer, is retained. -/
theorem ofFlag_sp4_eq_or_fieldFour_block_of_normalized_source
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
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree)
    : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K ∨
      (S.field.degree = 2 ∧ ChapterC.IsSp4FourBlock L ∧
        V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
        (ofFlag S f X z H).V₁ = omegaOneAmbient
          ((center (ofFlag S f X z H).R₁).map (ofFlag S f X z H).R₁.subtype) ∧
        ¬ normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) := by
  by_cases he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K
  · exact .inl he
  have hNM : ¬ normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G) :=
    fun hn => he (ofFlag_sp4_eq_of_normalizer_of_normalized_source S f X z H h hlinear h1132
      hcent hline hXR e h325 hpositive m hn)
  obtain ⟨hv,hb,ht,hz⟩ := hradical.resolve_left hNM
  exact .inr ⟨Quasisimple.Hall.sp4_block_degree_eq_two S m hb,
    hb.resolve_left (sp4_not_linear_block S m),hv,ht,hz,hNM⟩

/-- Exact remaining source cases after the complete nonlinear and
invariant-seed comparisons. A normalizer-contained counterexample must
be the original SL₃(4) action with a genuinely larger normalizer orbit of V.
An escaping normalizer retains all clauses of the actual block alternative.
The strict block-center argument and the noninvariant cubic branch remain
unproved; neither is inserted as an earlier source hypothesis. -/
theorem ofFlag_remaining_cases_of_normalized_source
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
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree)
    : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K ∨
      (S.field.degree = 2 ∧ Source.IsSL (L ⧸ pCore 2 L) 3 4 ∧
        V ≠ Source.conjugateSpan (normalizer (L : Set G)) V ∧
        normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) ∨
      ((ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) ∧
        V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
        (ofFlag S f X z H).V₁ = omegaOneAmbient
          ((center (ofFlag S f X z H).R₁).map (ofFlag S f X z H).R₁.subtype) ∧
        ¬ normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) := by
  by_cases he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K
  · exact .inl he
  by_cases hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)
  · have hfour : S.field.degree = 2 := by
      by_contra hn
      exact he (ofFlag_eq_of_normalizer_of_not_fieldFour S f X z H h hlinear h1132 hcent hline hXR e
        hn hNM)
    cases c with
    | sl3 m =>
      have hm : Source.IsSL (L ⧸ pCore 2 L) 3 4 :=
        ⟨S.field.Carrier,inferInstance,inferInstance,by rw [S.field.card_eq,hfour]; rfl,
          ⟨m.groupEquiv⟩⟩
      have hfull : V ≠ Source.conjugateSpan (normalizer (L : Set G)) V :=
        fun hv => he (ofFlag_sl3_eq_of_normalizer_of_fullModule_of_normalized_source
          S f X z H h hlinear h1132 hcent hline hXR e h325 hpositive m hv hNM)
      exact .inr (.inl ⟨hfour,hm,hfull,hNM⟩)
    | sp4 m =>
      exact (he (ofFlag_sp4_eq_of_normalizer_of_normalized_source
        S f X z H h hlinear h1132 hcent hline hXR e h325 hpositive m hNM)).elim
    | g2 m =>
      exact (he (ofFlag_g2_eq_of_normalized_source S f X z H h hlinear h1132 hcent hline hXR e
        h325 hpositive m hradical)).elim
  · obtain ⟨hv,hb,ht,hz⟩ := hradical.resolve_left hNM
    exact .inr (.inr ⟨hb,hv,ht,hz,hNM⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
