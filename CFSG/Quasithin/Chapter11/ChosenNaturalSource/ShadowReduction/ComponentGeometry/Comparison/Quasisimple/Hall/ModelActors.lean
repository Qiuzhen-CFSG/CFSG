module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.NormalizerImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.ModelNormalizers

/-!
# Constructed odd actors in the source component comparison

The original nonbinary field supplies an odd prime dividing q−1.
The concrete model normalizer ranks and the relative Sylow lift construct
a p-subgroup in Kz intersect N_G(R₁) of rank at least two. If V₁ is properly
contained in the omega-center of R₁, the literal 11.1.5 dichotomy puts this
actor in N_G(L). The earlier residual clauses and natural fixed spaces
then give the chosen-flag contradiction.

All choices, quotient lifts and rank bounds are discharged. Preservation
of the radical image by an inner Sylow normalizer and strict omega-center
containment remain explicit local obligations of this comparison owner.
The classification consumer supplies the actual rank-two model, so no
FF model is inserted as an earlier source assumption. Earlier-source
discharge stays with qt-d-1222-shadow-components. This conditional result
does not yet establish full 11.4.2.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- An inner Sylow normalizer preserving the actual radical image constructs
the source odd-primary actor, at an automatically chosen divisor of q minus one. -/
theorem exists_odd_actor_of_model_normalizer
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hm : RankTwoModel E)
    (P : Sylow 2 ((component E).map (projection E)))
    (hN : (normalizer (P : Set ((component E).map (projection E)))).map
        ((component E).map (projection E)).subtype ≤
      normalizer ((radical E).map (projection E) : Set (ActionQuotient E))) :
    ∃ (p : ℕ) (Y : Subgroup G), p.Prime ∧ Odd p ∧ p ∣ 2 ^ E.input.field.degree - 1 ∧
      Y ≤ E.Kz ∧ Y ≤ normalizer (E.R₁ : Set G) ∧ IsPGroup p Y ∧ 2 ≤ primeRank p Y := by
  have hn : 2 ≤ E.input.field.degree := by have := E.input.nonbinary; omega
  have hpow : 4 ≤ 2 ^ E.input.field.degree :=
    pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hn
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd
    (show 2 ^ E.input.field.degree - 1 ≠ 1 by omega)
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    have h2 : 2 ∣ 2 ^ E.input.field.degree := dvd_pow_self 2 (by omega)
    have hx := Nat.mod_eq_zero_of_dvd hd
    have hy := Nat.mod_eq_zero_of_dvd h2
    omega)
  obtain ⟨Y,hYK,hYR,hY,hrY⟩ := exists_odd_actor_of_normalizer_rank
    E h hf hne hstar hcent ho (radical_image_normalizer_rank_of_model E hm P hN ho hd)
  exact ⟨p,Y,hp,ho,hd,hYK,hYR,hY,hrY⟩

variable {E}

/-- The rank-two model contradiction with all odd-actor choices and ranks
discharged. The two remaining local geometric inputs are preservation of
the radical image by the inner Sylow normalizer and the strict omega-center
inequality. The original 11.1.5 dichotomy supplies ambient placement. -/
theorem ofFlag_false_of_model_normalizer_geometry
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : RankTwoModel (ofFlag S f X z H))
    (P : Sylow 2 ((component (ofFlag S f X z H)).map (projection (ofFlag S f X z H))))
    (hN : (normalizer (P : Set ((component (ofFlag S f X z H)).map
        (projection (ofFlag S f X z H))))).map
        ((component (ofFlag S f X z H)).map (projection (ofFlag S f X z H))).subtype ≤
      normalizer ((radical (ofFlag S f X z H)).map (projection (ofFlag S f X z H)) :
        Set (ActionQuotient (ofFlag S f X z H))))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree)
    (hZ : (ofFlag S f X z H).V₁ ≠ omegaOneAmbient
      ((center (ofFlag S f X z H).R₁).map (ofFlag S f X z H).R₁.subtype))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ normalizer (L : Set G), orderOf y = 3 → y ∈ L) : False := by
  have hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G) := by
    rcases hradical with hn | hh
    · exact hn
    · exact (hZ hh.2.2.2).elim
  obtain ⟨p,Y,hp,ho,hd,hYK,hYR,_,hrY⟩ := exists_odd_actor_of_model_normalizer
    (ofFlag S f X z H) h (fixed_and_transitive D S _ hlinear h1132).1
    hne hstar hcent hm P hN
  let : Fact p.Prime := ⟨hp⟩
  have hYL := hYR.trans hNM
  rw [← primeRank_intersection_eq_of_source S c Y hYL ho hd
    (fun hs y hy h3 => hcubic hs y (hYL hy) h3)] at hrY
  exact ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132
    (Y ⊓ L) (inf_le_left.trans hYK) inf_le_right ho hrY

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
