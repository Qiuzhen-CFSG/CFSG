module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.LargeField
public import Theory.NumberTheory.BinarySignedTorus

/-!
# The component comparison at a split prime greater than three

For every original field larger than four, q−1 has a prime divisor greater
than three. The proved inner radical placement and inner Sylow normalizer
construct a rank-two subgroup at that particular prime in Kz ∩ N_G(R₁).
When N_G(R₁) lies in N_G(L), the original prime-to-p residual puts the whole
subgroup in L. The nonidentity source point and the natural fixed-space
calculation then contradict its rank. This applies to all three original
natural actions and requires no cubic-containment hypothesis.

The chosen-flag application discharges maximality, point quasisimplicity,
the complete model sieve and all actor choices above field order four.
Combining it with the literal 11.1.5 alternative confines a remaining strict
comparison to field four or a genuine short SL₃ block with V=V_M,
C_T(L)=1 and V₁=Ω₁Z(R₁). The symplectic block is excluded by comparing
Sylow orders through the original two-core quotient isomorphisms.

The block-center contradiction and field-four maximality remain with
qt-d-1222-shadow-component-comparison. The positive normalized-module input
retains qt-d-1222-normalized-nonff as its producer. Earlier-source discharge
and the actual seed quotient marking remain with qt-d-1222-shadow-components.
This does not establish unconditional 11.4.2.
Source: Aschbacher--Smith, 11.4.2, printed pp.776--777, using 11.0.4 and 11.1.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open CFSG.Quasithin.ChapterB.QuasisimpleSource

private theorem exists_split_prime_gt_three {n : ℕ} (hn : 1 < n) (hfour : n ≠ 2) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2^n-1 := by
  by_cases he : n = 3
  · subst n
    exact ⟨7,by decide,by decide,by decide⟩
  · exact Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub (by omega)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- Select a split prime greater than three and lift its rank-two actor
through the literal VK-action quotient. All model-normalizer choices and
inner-placement premises are discharged on the original geometry. -/
theorem exists_prime_actor_gt_three
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hT : (T : Subgroup G) ≤ E.G₁)
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hm : RankTwoModel E) (hfour : E.input.field.degree ≠ 2) :
    ∃ (p : ℕ) (Y : Subgroup G), p.Prime ∧ 3 < p ∧ p ∣ 2^E.input.field.degree-1 ∧
      Y ≤ E.Kz ∧ Y ≤ normalizer (E.R₁ : Set G) ∧ IsPGroup p Y ∧ 2 ≤ primeRank p Y := by
  obtain ⟨p,hp,hp3,hd⟩ := exists_split_prime_gt_three E.input.nonbinary hfour
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hi := rankTwo_radical_image_le_component E h hf hne hstar hcent hT e hm
  obtain ⟨P,hP⟩ := exists_model_normalizer_of_inner_radical E h hf hne hstar hcent hm hi
  obtain ⟨Y,hYK,hYR,hY,hrY⟩ := exists_odd_actor_of_normalizer_rank E h hf hne hstar hcent ho
    (radical_image_normalizer_rank_of_model E hm P hP ho hd)
  exact ⟨p,Y,hp,hp3,hd,hYK,hYR,hY,hrY⟩

variable {E}

/-- Every surviving image row closes the original comparison above field
four when the original radical normalizer preserves L. The selected prime
uses the proved residual clause, including in the original SL₃ action. -/
theorem ofFlag_eq_of_rankTwo_of_normalizer_of_not_fieldFour
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
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hm : RankTwoModel (ofFlag S f X z H)) (hfour : S.field.degree ≠ 2)
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  obtain ⟨p,Y,hp,hp3,hd,hYK,hYR,hY,hrY⟩ := exists_prime_actor_gt_three
    (ofFlag S f X z H) h hf hne hstar hcent (f.invariant 0) e hm hfour
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hYM := hYR.trans hNM
  have hres : L = (primeToResidual p (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype := by
    have hd2 := hd.trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2)
    cases c with
    | sl3 m => exact LocalGeometry.Preliminary.sl3_prime_residual D S m hp hp3 hd
    | sp4 m => exact LocalGeometry.Preliminary.sp4_prime_residual D S m hp hd2
    | g2 m => exact LocalGeometry.Preliminary.g2_prime_residual D S m hp hd2
  have hYL : Y ≤ L := by
    rw [hres]
    have hr : (Y.subgroupOf (normalizer (L : Set G))).map
        (normalizer (L : Set G)).subtype ≤
        (primeToResidual p (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype :=
      map_mono (le_primeToResidual_of_isPGroup
      (hY.comap_subtype : IsPGroup p (Y.subgroupOf (normalizer (L : Set G)))))
      (f := (normalizer (L : Set G)).subtype)
    rwa [map_subgroupOf_eq_of_le hYM] at hr
  exact ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132 Y hYK hYL ho hrY

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
open CFSG.Quasithin.ChapterB.QuasisimpleSource Overcomponent.EmbeddingProof
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

private theorem sylow_card_equiv {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (e : A ≃* B) (P : Sylow 2 A) (Q : Sylow 2 B) :
    Nat.card P = Nat.card Q := by
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact (Nat.card_congr ((P : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).trans
    (Nat.card_congr (Sylow.equiv R Q).toEquiv)

omit [Finite G] in
private theorem sl3_not_sp4FourBlock {n : ℕ} (hn : 0 < n)
    (hs : Source.IsSL (L ⧸ pCore 2 L) 3 (2^n)) : ¬ ChapterC.IsSp4FourBlock L := by
  obtain ⟨F,instF,finF,hF,⟨a⟩⟩ := hs
  let : Field F := instF
  let : Finite F := finF
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  rintro ⟨_,K,instK,finK,hK,ρ,⟨m⟩,_⟩
  let : Field K := instK
  let : Finite K := finK
  have hk : Nat.card K = 2^2 := hK
  let : CharP K 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hk
  let e := a.symm.trans m.quotientIso
  have hc := sylow_card_equiv e
    (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F hn hF)
    (Theory.SpecificGroups.SymplecticFour.unipotentSylow hk (by decide))
  change Nat.card (Matrix.PSL3.LinearThree.unipotentSL F) =
    Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := K)) at hc
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,
    Theory.SpecificGroups.SymplecticFour.card_unipotent,hF,hk,←pow_mul,←pow_mul] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  omega

/-- The actual chosen flag above field four: maximality, quasisimplicity,
the complete model comparison and the rank-two actor are internal. -/
theorem ofFlag_eq_of_normalizer_of_not_fieldFour
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
    (hfour : S.field.degree ≠ 2)
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hs := ofFlag_point_mem_LStar_of_not_fieldFour S f X z H h hne hlinear h1132 e hfour
  let := ofFlag_point_quasisimple_of_not_fieldFour S f X z H h hne hlinear h1132 e hfour
  have hc := ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl
  have hm := Quasisimple.Classification.ofFlag_rankTwo_of_componentAlternative
    S f X z H h hne hs hlinear h1132 hcent hline hXR hc e
  exact hne (Quasisimple.Hall.ofFlag_eq_of_rankTwo_of_normalizer_of_not_fieldFour
    S f X z H h hs hlinear h1132 hcent e hm hfour hNM)

/-- Above field four, strict omega-center containment is sufficient for
comparison equality in every original natural action. No cubic input remains. -/
theorem ofFlag_eq_of_omega_center_ne_of_not_fieldFour
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
    (hfour : S.field.degree ≠ 2)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree)
    (hZ : (ofFlag S f X z H).V₁ ≠ omegaOneAmbient
      ((center (ofFlag S f X z H).R₁).map (ofFlag S f X z H).R₁.subtype)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  apply ofFlag_eq_of_normalizer_of_not_fieldFour S f X z H h hlinear h1132
    hcent hline hXR e hfour
  exact hradical.resolve_right (fun hb => hZ hb.2.2.2)

/-- The remaining original-source cases, with every clause of the exceptional
block retained. In particular an unresolved case above field four must be
an actual short SL₃ block, not just an SL₃ group-image label. -/
theorem ofFlag_eq_or_linear_block_or_fieldFour
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
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K ∨ S.field.degree = 2 ∨
      (Source.IsSL (L ⧸ pCore 2 L) 3 (2^S.field.degree) ∧
        ChapterC.IsSL3EvenBlock L S.field.degree ∧
        V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
        (ofFlag S f X z H).V₁ = omegaOneAmbient
          ((center (ofFlag S f X z H).R₁).map (ofFlag S f X z H).R₁.subtype) ∧
        ¬ normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) := by
  by_cases he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K
  · exact Or.inl he
  by_cases hfour : S.field.degree = 2
  · exact Or.inr (Or.inl hfour)
  have hNM : ¬ normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G) :=
    fun hn => he (ofFlag_eq_of_normalizer_of_not_fieldFour S f X z H h hlinear h1132
      hcent hline hXR e hfour hn)
  have hs := ((ofFlag_eq_or_linear_or_fieldFour S f X z H h hlinear h1132
    hcent hline hXR e hradical).resolve_left he).resolve_right hfour
  obtain ⟨hv,hb,ht,hz⟩ := hradical.resolve_left hNM
  have hb' := hb.resolve_right (sl3_not_sp4FourBlock S.field.degree_pos hs)
  exact Or.inr (Or.inr ⟨hs,hb',hv,ht,hz,hNM⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
