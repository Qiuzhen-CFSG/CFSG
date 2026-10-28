module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue

/-!
# The original symplectic and G₂ comparisons above field order four

The full containing-component catalogue forces maximality outside field order
four. The nonquasisimple two-rank bound and the same complete catalogue then
force the point quotient to be quasisimple. These deductions retain every
source row and use the original seed quotient marking.

For the original Sp₄ action, the two exceptional blocks in 11.1.5 are compared
through their actual quotient isomorphisms. Their Sylow orders exclude the
SL₃ block and force field order four in the symplectic block. Thus the original
radical normalizer lies in N_G(L). The already constructed inner radical and
odd-primary rank-two actor, followed by the original Sp₄ prime residual theorem,
give Kz = K. No strict omega-center or cubic-containment input is needed.
The existing G₂ Hall theorem gives the parallel result, including even degree.

The final chosen-flag consumer confines the unfinished comparison to the
original SL₃ action or field order four. The omega-center and field-four
proper-overcomponent obligations remain with qt-d-1222-shadow-component-comparison;
all preceding source inputs and the seed marking retain final discharge by
qt-d-1222-shadow-components. This does not assert full source 11.4.2.
Source: Aschbacher--Smith, 11.4.2, printed pp.776--777, using 11.0.4 and 11.1.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open CFSG.Quasithin.ChapterB.QuasisimpleSource

private theorem sylow_card_congr {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (e : A ≃* B) (P : Sylow 2 A) (Q : Sylow 2 B) :
    Nat.card P = Nat.card Q := by
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact (Nat.card_congr ((P : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).trans
    (Nat.card_congr (Sylow.equiv R Q).toEquiv)

private theorem sp4_not_sl3 {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (hK : Nat.card K = 2^n)
    (e : Theory.SpecificGroups.SymplecticFour.Sp F ≃* SL(3,K)) : False := by
  have hc := sylow_card_congr e
    (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF hn)
    (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow K hn hK)
  change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)) =
    Nat.card (Matrix.PSL3.LinearThree.unipotentSL K) at hc
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,
    Matrix.PSL3.LinearThree.card_unipotentSL, hF, hK, ← pow_mul, ← pow_mul] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  omega

private theorem sp4_degree_of_four {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (hK : Nat.card K = 4)
    (e : Theory.SpecificGroups.SymplecticFour.Sp F ≃*
      Theory.SpecificGroups.SymplecticFour.Sp K) : n = 2 := by
  have hk : Nat.card K = 2^2 := by omega
  have hc := sylow_card_congr e
    (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF hn)
    (Theory.SpecificGroups.SymplecticFour.unipotentSylow hk (by decide))
  change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)) =
    Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := K)) at hc
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,
    Theory.SpecificGroups.SymplecticFour.card_unipotent,
    hF, hk, ← pow_mul, ← pow_mul] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- In an original symplectic action, the exceptional block alternative of
11.1.5 forces the original field to have order four. Both block markings
are compared through their literal two-core quotient isomorphisms. -/
theorem sp4_block_degree_eq_two (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) :
    S.field.degree = 2 := by
  rcases hb with hb | hb
  · obtain ⟨_,_,F,inst,fin,hF,hmodel⟩ := hb
    let : Field F := inst
    let : Finite F := fin
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact (sp4_not_sl3 S.field.degree_pos S.field.card_eq hF
      (m.groupEquiv.symm.trans hmodel.quotient_iso.some)).elim
  · obtain ⟨_,F,inst,fin,hF,ρ,⟨model⟩,_⟩ := hb
    let : Field F := inst
    let : Finite F := fin
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
      (show Nat.card F = 2^2 from hF)
    exact sp4_degree_of_four S.field.degree_pos S.field.card_eq hF
      (m.groupEquiv.symm.trans model.quotientIso)

/-- The original Sp₄ action over a field larger than four closes the Hall
comparison in every surviving image row. The original radical alternative
supplies ambient normalization, so no omega-center inequality is assumed. -/
theorem ofFlag_sp4_eq_of_rankTwo_of_not_fieldFour
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
    (e₁ : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hm : RankTwoModel (ofFlag S f X z H))
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hfour : S.field.degree ≠ 2)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  have hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G) := by
    rcases hradical with hn | hb
    · exact hn
    · exact (hfour (sp4_block_degree_eq_two S m hb.2.1)).elim
  by_contra hne
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hi := rankTwo_radical_image_le_component (ofFlag S f X z H)
    h hf hne hstar hcent (f.invariant 0) e₁ hm
  obtain ⟨p,Y,hp,hodd,hd,hYK,hYR,hY,hrY⟩ := exists_odd_actor_of_inner_radical
    (ofFlag S f X z H) h hf hne hstar hcent hm hi
  let : Fact p.Prime := ⟨hp⟩
  have hYM := hYR.trans hNM
  have hYL : Y ≤ L := by
    rw [LocalGeometry.Preliminary.sp4_prime_residual D S m hp
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

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
open CFSG.Quasithin.ChapterB.QuasisimpleSource Overcomponent.EmbeddingProof
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The full original catalogue and the nonquasisimple rank bound force
quasisimplicity in a strict comparison outside the field-four case. -/
theorem ofFlag_point_quasisimple_of_not_fieldFour
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hfour : S.field.degree ≠ 2) :
    IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) := by
  by_contra hn
  have hr := Frattini.point_quotient_two_rank_le_one S.source.simpleQTKE h hn
  cases ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl with
  | equal he =>
    exact (h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he
  | lie hm => exact hn (Frattini.Catalogue.lie_quasisimple_of_rank_le_one S.field.degree_pos hr hm)
  | four hd _ => exact hfour hd

/-- For an original Sp₄ action over a field larger than four, source 11.4.2
holds on the actual flag. Maximality, quasisimplicity, the full model sieve,
radical inner placement and the Hall actor are all discharged internally. -/
theorem ofFlag_sp4_eq_of_not_fieldFour
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
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hfour : S.field.degree ≠ 2)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hs := ofFlag_point_mem_LStar_of_not_fieldFour S f X z H h hne hlinear h1132 e hfour
  let := ofFlag_point_quasisimple_of_not_fieldFour S f X z H h hne hlinear h1132 e hfour
  have hc := ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl
  have hm := Quasisimple.Classification.ofFlag_rankTwo_of_componentAlternative
    S f X z H h hne hs hlinear h1132 hcent hline hXR hc e
  exact hne (Quasisimple.Hall.ofFlag_sp4_eq_of_rankTwo_of_not_fieldFour
    S f X z H h hs hlinear h1132 hcent e hm m hfour hradical)

/-- The original G₂ equality over every field larger than four, including
even degree, now also discharges maximality and quasisimplicity. -/
theorem ofFlag_g2_eq_of_not_fieldFour
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
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hfour : S.field.degree ≠ 2)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hs := ofFlag_point_mem_LStar_of_not_fieldFour S f X z H h hne hlinear h1132 e hfour
  let := ofFlag_point_quasisimple_of_not_fieldFour S f X z H h hne hlinear h1132 e hfour
  have hc := ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl
  exact hne (Quasisimple.Classification.ofFlag_g2_eq S f X z H h hs hlinear h1132
    hcent hline hXR hc e m hradical)

/-- The remaining source comparison is confined to the original SL₃ action
or field order four. The original marked module and point are unchanged. -/
theorem ofFlag_eq_or_linear_or_fieldFour
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
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K ∨
      Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨ S.field.degree = 2 := by
  by_cases hfour : S.field.degree = 2
  · exact Or.inr (Or.inr hfour)
  cases c with
  | sl3 m => exact Or.inr (Or.inl
      ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩)
  | sp4 m => exact Or.inl (ofFlag_sp4_eq_of_not_fieldFour S f X z H h hlinear h1132
      hcent hline hXR e m hfour hradical)
  | g2 m => exact Or.inl (ofFlag_g2_eq_of_not_fieldFour S f X z H h hlinear h1132
      hcent hline hXR e m hfour hradical)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
