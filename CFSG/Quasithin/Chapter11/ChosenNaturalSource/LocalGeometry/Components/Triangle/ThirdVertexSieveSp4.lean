module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.FaithfulJoinSp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SourceCatalogue
public import Theory.SpecificGroups.PSL2.PrimeCoverCartanNormalizer
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# Marked exclusions at the symplectic triangle's third vertex

The original Cartan has order nine, and its intersection with K₀ has
order three. The symplectic Cartan splitting shows that X lies in neither
K₀ nor L₂. Since X lies in their join, both residuals are proper there.

A PSL₃(4) quotient of that join is impossible: the odd Cartan normalizes
the original Sylow intersection with L₂, so the marked PSL₃ residual
calculation would put all of X in L₂. This argument uses the actual
subgroups, rather than only the three-rank of the join. Separately, that
rank excludes every prime-field PSL₂ row, PSL₂(25), and J₁.

The final consumer starts with the original nontrivial common normal Q,
constructs the relatively normal join by the existing theorem, and applies
the proved relative-component catalogue to L₂ inside IT. Besides the
three desired Lie models, its remaining list still includes ³D₄(4) and
field-four covering, sporadic and odd-extension rows. Thus this is a
partial sieve, not the three-model recognition asserted on printed p.763.
The two GL₂(4) markings and their A.3.14 comparison, common-normal existence,
the source SL₃(4) exclusion, maximality and both orientations remain with
qt-d-1222-natural-relative-components. Earlier flag/Cartan assumptions
retain their existing producers and final discharge by
qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.762--764, and A.3.14, printed pp.49--50.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

private theorem no_prime_linear_of_three_rank_two
    {p : ℕ} (hp : p.Prime) (hr : 2 ≤ primeRank 3 G)
    (hm : ClassicalGroup.IsPSL G 2 p) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,hF,ZMod.card])
  have hb := Theory.PSL2.primeField_odd_rank (p := p) (r := 3) (by decide)
  rw [primeRank_congr 3 (e.trans (GorensteinWalter.psl2RingEquiv a))] at hr
  exact (by decide : ¬ (2 ≤ 1)) (hr.trans hb)

private theorem no_twenty_five_of_three_rank_two (hr : 2 ≤ primeRank 3 G)
    (hm : ClassicalGroup.IsPSL G 2 25) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hc : Nat.card G = 7800 := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩,hF]
    norm_num
  have hb : primeRank 3 G ≤ 1 := primeRank_le_of_prime_pow_not_dvd (by rw [hc]; decide)
  omega

private theorem no_janko_one_of_three_rank_two (hr : 2 ≤ primeRank 3 G)
    (hm : Nonempty (G ≃* Janko1.Model)) : False := by
  have hc : Nat.card G = 175560 := (Nat.card_congr hm.some.toEquiv).trans Janko1.card_model
  have hb : primeRank 3 G ≤ 1 := primeRank_le_of_prime_pow_not_dvd (by rw [hc]; decide)
  omega

omit [Finite G] in
private theorem sylow_intersection_normalized
    {T : Sylow 2 G} {L B X : Subgroup G}
    (hX : IsCartan T L X) (hBL : B ≤ L)
    (hXB : X ≤ normalizer (B : Set G)) :
    X ≤ normalizer (((T : Subgroup G) ⊓ B : Subgroup G) : Set G) := by
  have he : (T : Subgroup G) ⊓ B = ((T : Subgroup G) ⊓ L) ⊓ B := by
    exact le_antisymm (le_inf (le_inf inf_le_left (inf_le_right.trans hBL)) inf_le_right)
      (inf_le_inf inf_le_left le_rfl)
  rw [he]
  exact (le_inf (hX.1.trans cartanNormalizer_normalizes_intersection) hXB).trans
    inf_normalizer_le_normalizer_inf

variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- Both marked residuals are proper in the literal third vertex, because
neither contains the original Cartan. This does not assume existence of Q
or a recognized quotient for the join. -/
theorem sp4_triangle_proper_residuals
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    K₀ < K₀ ⊔ f.Li 1 ∧ f.Li 1 < K₀ ⊔ f.Li 1 ∧
      ¬ X ≤ K₀ ∧ ¬ X ≤ f.Li 1 := by
  obtain ⟨hc,h₁,h₀⟩ := first_triangle_cartan_intersections D S f hu hm hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hXI := sp4_triangle_cartan_le_join D S m f hu hm hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hn₀ : ¬ X ≤ K₀ := by
    intro h
    have he : X ⊓ K = X := h₀.trans (inf_eq_left.mpr h)
    rw [he,(Coordinates.sp4 m).cartan_card hX,hfour] at hc
    norm_num at hc
  have hn₂ : ¬ X ≤ f.Li 1 := by
    intro h
    have hd := (sp4_cartan_split D S m f hX).2
    rw [inf_eq_left.mpr h] at hd
    have he : X ⊓ f.Li 0 = ⊥ := disjoint_self.mp
      (Disjoint.mono_right (inf_le_left : X ⊓ f.Li 0 ≤ X) hd)
    rw [h₁,he,card_bot] at hc
    contradiction
  exact ⟨lt_of_le_of_ne le_sup_left (fun he => hn₀ (he.symm ▸ hXI)),
    lt_of_le_of_ne le_sup_right (fun he => hn₂ (he.symm ▸ hXI)),hn₀,hn₂⟩

/-- The projective linear quotient is excluded using the actual Sylow
intersection and the original symplectic Cartan marking. This does not
exclude the special-linear covering row SL₃(4). -/
theorem sp4_triangle_not_psl3
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hI : Source.ComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1)) :
    ¬ ClassicalGroup.IsPSL ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 3 4 := by
  obtain ⟨_,hlt,_,hn⟩ := sp4_triangle_proper_residuals D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hXN : X ≤ normalizer (f.Li 1 : Set G) := by
    have hx : X ≤ L ⊓ normalizer (f.Vi 1 : Set G) :=
      le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 1)
    exact (hx.trans (L ⊓ normalizer (f.Vi 1 : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have htop : (⊤ : Subgroup (K₀ ⊔ f.Li 1 : Subgroup G)).IsCComponent := by
    simpa only [subgroupOf_self] using hI.2.subgroupOf_of_le le_rfl hI.1
  have hTI : (T : Subgroup G) ≤ normalizer ((K₀ ⊔ f.Li 1 : Subgroup G) : Set G) :=
    (le_inf hTK₀ (f.sylow_normalizes_Li 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup K₀ (f.Li 1))
  intro hi
  exact hn (odd_intersection_le_local T htop hTI
    (flag_mem_local_of_model D S f 1 hm₂).1 hlt
    (flag_mem_local_of_model D S f 1 hm₂).1 hlt
    (sp4_triangle_cartan_le_join D S m f hu hm₁ hfour hX hK hLK hK₀ hK₀K hk hp)
    hX.odd (sylow_intersection_normalized hX ((localResidual_le _).trans inf_le_left) hXN) hi)

/-- The original common-normal construction feeds the source embedding
catalogue and the marked exclusions. Every surviving alternative refers
to the literal I/O₂(I); no model-list premise is supplied by the caller.
The triality and remaining field-four rows still need the two marked
GL₂(4) local comparisons before the three-model source conclusion. -/
theorem sp4_triangle_join_remaining_models_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    let A := I ⧸ pCore 2 I
    K₀ < I ∧ f.Li 1 < I ∧
      (Source.IsSL A 3 4 ∨ Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4 ∨
        Triality.Standard.IsTrialityGroupAt 4 A ∨ FieldFourOvergroup A) ∧
      ¬ ClassicalGroup.IsPSL A 3 4 ∧
      (∀ p : ℕ, p.Prime → ¬ ClassicalGroup.IsPSL A 2 p) ∧
      ¬ ClassicalGroup.IsPSL A 2 25 ∧ ¬ Nonempty (A ≃* Janko1.Model) := by
  intro I A
  obtain ⟨hI,_,_,_,_,_,hrq⟩ := sp4_triangle_join_faithful_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨h₀,h₂,_,_⟩ := sp4_triangle_proper_residuals D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hn := sp4_triangle_not_psl3 D S m f hu hm₁ hm₂ hfour
    hX hK hLK hK₀ hK₀K hTK₀ hk hp hI.1
  have hrA : 2 ≤ primeRank 3 A := hrq.ge
  refine ⟨h₀,h₂,?_,hn,fun p hp => no_prime_linear_of_three_rank_two hp hrA,
    no_twenty_five_of_three_rank_two hrA,no_janko_one_of_three_rank_two hrA⟩
  let H := I ⊔ (T : Subgroup G)
  have hHN : H ≤ normalizer (Q : Set G) := sup_le (sup_le hKQ hLQ) hTQ
  have hN := S.source.simpleQTKE.twoLocal_sqtk ⟨Q,hQ,T.isPGroup'.to_le hQT,rfl⟩
  have hH : IsSQTK KnownSimple.IsKnownSimple H := by
    let e := (subgroupOfEquivOfLe hHN).symm
    have hh := hN.subgroup (H.subgroupOf (normalizer (Q : Set G)))
    exact ⟨hh.stronglyQuasithin.of_injective e.toMonoidHom e.injective,
      hh.isKGroup.of_injective e.toMonoidHom e.injective⟩
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hP : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  have hc := Embedding.relative_component_alternative hH hP
    (flag_mem_local_of_model D S f 1 hm₂) hI.1 le_sup_right
    (f.sylow_normalizes_Li 1) S.nonbinary hm₂
  rw [hfour] at hc
  cases hc with
  | equal he => exact (h₂.ne he).elim
  | four _ hm => exact .inr (.inr (.inr (.inr hm)))
  | lie hm =>
    cases hm with
    | sl3 hm => exact .inl hm
    | psl3 hm => exact (hn hm).elim
    | sp4 hm => exact .inr (.inl hm)
    | g2 hm => exact .inr (.inr (.inl hm))
    | triality hm => exact .inr (.inr (.inr (.inl hm)))
    | ree m hm he _ => omega
    | trialityCube m hm he _ => omega

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
