module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicLinear
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSpecialLinearResidual
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SpecialLinearThree

/-!
# The selected A₅ parabolic in the special-linear residual

The selected factor is local at a full Sylow of the original residual.
Its proper image under the residual two-core quotient is preserved by
local-component minimality. The existing SL₃ A₅ placement theorem then
forces the coefficient field to have four elements. The covering group
and its projective quotient remain distinct.

The actual residual Sylow-normalizer torus excludes a cubic escaping
actor, so the actor is quintic. This also excludes the two alternating
seven containing models at the smaller changed Sylow. Together with the
projective linear and symplectic branches, the field comparison proves
the original degree-two normalization conclusion in every rank-two row.
For the actual nonzero-core prime configuration, properness of the
selected parabolic is derived from the escaping actor.

No selected factor is assumed to be an H-component. The remaining source
selection, higher degrees, zero-core models and changed-Sylow branches
remain with the Cartan local-to-global owner.
Source: Aschbacher–Smith 5.1.10–13 and 5.2.2, printed pp.634–638,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem specialLinear_field_of_local_five
    {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) {R : Subgroup X}
    (hR : R ∈ ChapterA.Section03.localCComponents S)
    (htop : (⊤ : Subgroup X).IsCComponent) (hne : R ≠ ⊤)
    {f : ℕ}
    (hm : Chapter1.Section02.LocalModels.IsSL (X ⧸ pCore 2 X) 3 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : f = 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    ext x
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  let : Group.IsNilpotent q.ker := hk ▸ pCore_isNilpotent
  have hproper : R.map q ≠ ⊤ := by
    intro he
    apply hne
    apply local_cComponent_eq_of_map_eq hR htop le_top q
      (hk ▸ pCore_isPGroup.le_sylow_of_normal S)
    simpa only [map_top_of_surjective q hq] using he
  have hr : IsPGroup 2 (q.subgroupMap R).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  obtain ⟨E,_,_,hE,⟨a⟩⟩ := hA5
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hE
  have he := (ChapterA.Section03.SourceEmbeddings.FiveLocalFF.special_linear_three_five_section_image
    hF q hq inferInstance S R hR hr hproper (a.trans e5)).1
  apply Nat.pow_right_injective (by decide : 1 < 2)
  exact hF.symm.trans he

/-- An A₅ selected parabolic forces field order four in the genuine central
cover, without a separate positive-field-degree hypothesis. -/
theorem LocalData.A5_right_specialLinear_residual_field
    {T : Sylow 2 G} {L H B D R : Subgroup G} {f : ℕ}
    (d : LocalData T L H B D R) (hTH : (T : Subgroup G) ≤ H)
    (hR : R < residual H)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : f = 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    IsQuasisimple.of_mulEquiv e.symm
  let eK : pResidual 2 H ≃* residual H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eqK := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  let : IsQuasisimple ((residual H) ⧸ pCore 2 (residual H)) :=
    IsQuasisimple.of_mulEquiv eqK
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 (residual H)) pCore_isPGroup (isPPerfect_embedded_pResidual 2 H)
  obtain ⟨S,_,hl⟩ := d.right_local_in_residual hTH
  have hn : R.subgroupOf (residual H) ≠ ⊤ := fun he => hR.not_ge (subgroupOf_eq_top.mp he)
  let er := subgroupOfEquivOfLe d.right_le_residual
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  exact specialLinear_field_of_local_five S hl ht hn
    ⟨F,inferInstance,inferInstance,hF,⟨eqK.symm.trans e⟩⟩ (hA5.of_mulEquiv eqr)

/-- In the nonzero-core configuration, an A₅ parabolic forces the cover
field to four and every escaping actor to be quintic. -/
theorem LocalData.A5_right_specialLinear_prime
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hf : 1 < f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : f = 2 ∧ p = 5 := by
  have he := d.A5_right_specialLinear_residual_field hH.1.1.2
    (d.right_lt_residual hH.1.1.2 c hd hz) hm hA5
  refine ⟨he,hd.prime.resolve_left ?_⟩
  intro hp
  have hn := c.specialLinear_residual_prime_not_dvd h hd hH hf hm
  apply hn
  simp only [he,hp]
  decide

/-- The special-linear residual excludes both alternating containing models
at the smaller changed Sylow, also for a selected parabolic factor. -/
theorem LocalData.A5_specialLinear_not_alternating_seven_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hf : 1 < f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hmK
  have h5 := (d.A5_right_specialLinear_prime h hH c hd hz hf hm hA5).2
  have h3 := d.source_overcomponent_alternating_seven_prime h hH c hd hz
    hSyl hRK hKX hK hKn hmK
  omega

/-- All three projective/special-linear/symplectic rank-two rows normalize
the original degree-two Cartan in the A₅ parabolic case. -/
theorem LocalData.cartan_normalizes_of_A5_rankTwo_degree_two
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {f : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hR : R < residual H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    A ≤ normalizer (residual H : Set G) := by
  rcases hm with hm | hm | hm
  · exact (d.A5_right_not_linear_residual hH.1.1.2 hR hf hthree hA5 hm).elim
  · have he := d.A5_right_specialLinear_residual_field hH.1.1.2 hR hm hA5
    exact h.cartan_normalizes_of_specialLinear_residual_small_degree hH c hcontrol
      (Or.inl rfl) hf (by rw [he]) hm
  · exact d.cartan_normalizes_of_A5_symplectic_degree_two h hH hgen c hcontrol hR hf hm hA5

/-- The escaping actor supplies properness in the actual nonzero-core branch. -/
theorem LocalData.A5_rankTwo_prime_excluded_degree_two
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hd : CartanPrimeActor A H p D) (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : False :=
  h.prime_actor_not_normalizes hH hd (hd.le_cartan.trans
    (d.cartan_normalizes_of_A5_rankTwo_degree_two h hH hgen hthree c hcontrol
      (d.right_lt_residual hH.1.1.2 c hd hz) hf hm hA5))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
