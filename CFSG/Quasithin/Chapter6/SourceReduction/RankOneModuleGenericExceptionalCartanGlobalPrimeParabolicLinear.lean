module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicField
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic

/-!
# The projective linear residual with an A₅ selected parabolic

The original selected factor is local at a full Sylow of the residual,
without an assumption that it is an H-component. Local component
minimality preserves its proper image through the actual residual
quotient. The point/line placement theorem then recovers field order
four from its intrinsic A₅ quotient. Thus the original exclusion of
PSL₃(4) rules out every projective linear residual in this row.

Together with the symplectic field comparison this proves the original
degree-two normalization conclusion in both projective rank-two rows.
The nonzero-core prime application derives properness from the escaping
actor. It retains the literal quotient, generated subgroup, and Hall pair.
The special-linear central cover and the other degrees and source rows
remain with the Cartan local-to-global assembly owner.

Source: Aschbacher–Smith A.3.12, 5.1.10 and 5.2.2,
printed pp.47–48,634,648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem linear_field_of_local_five
    {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) {R : Subgroup X}
    (hR : R ∈ ChapterA.Section03.localCComponents S)
    (htop : (⊤ : Subgroup X).IsCComponent) (hne : R ≠ ⊤)
    {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 3 (2 ^ f))
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
  obtain ⟨E,_,_,hE,⟨eE⟩⟩ := hA5
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hE
  have hfour := (ChapterA.Section03.SourceEmbeddings.FiveLocalFF.linear_three_five_section_image
    hF hf q hq inferInstance S R hR hr hproper (eE.trans e5)).1
  apply Nat.pow_right_injective (by decide : 1 < 2)
  exact hF.symm.trans hfour

/-- An A₅ selected parabolic in the projective linear row forces field order four. -/
theorem LocalData.A5_right_linear_residual_field
    {T : Sylow 2 G} {L H B D R : Subgroup G} {f : ℕ}
    (d : LocalData T L H B D R) (hTH : (T : Subgroup G) ≤ H)
    (hR : R < residual H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f))
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
  exact linear_field_of_local_five S hl ht hn hf
    ⟨F,inferInstance,inferInstance,hF,⟨eqK.symm.trans e⟩⟩ (hA5.of_mulEquiv eqr)

/-- The source exclusion of PSL₃(4) removes every projective linear
residual field when the selected parabolic has the A₅ quotient. -/
theorem LocalData.A5_right_not_linear_residual
    {T : Sylow 2 G} {L H B D R : Subgroup G} {f : ℕ}
    (d : LocalData T L H B D R) (hTH : (T : Subgroup G) ≤ H)
    (hR : R < residual H) (hf : 1 < f)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) := by
  intro hm
  have he := d.A5_right_linear_residual_field hTH hR hf hm hA5
  apply hthree
  simpa only [he,show (2 : ℕ) ^ 2 = 4 by norm_num] using hm

/-- At original degree two, both projective rank-two rows discharge the
normalization conclusion for an actual A₅ selected parabolic. -/
theorem LocalData.cartan_normalizes_of_A5_projective_rankTwo_degree_two
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {f : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hR : R < residual H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    A ≤ normalizer (residual H : Set G) := by
  rcases hm with hm | hm
  · exact (d.A5_right_not_linear_residual hH.1.1.2 hR hf hthree hA5 hm).elim
  · exact d.cartan_normalizes_of_A5_symplectic_degree_two h hH hgen c hcontrol hR hf hm hA5

/-- The nonzero-core prime branch supplies properness itself. In original
degree two, an A₅ selected parabolic excludes both projective rank-two rows. -/
theorem LocalData.A5_projective_rankTwo_prime_excluded_degree_two
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {p f : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hd : CartanPrimeActor A H p D) (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : False := by
  have hn := d.cartan_normalizes_of_A5_projective_rankTwo_degree_two h hH hgen hthree
    c hcontrol (d.right_lt_residual hH.1.1.2 c hd hz) hf hm hA5
  exact h.prime_actor_not_normalizes hH hd (hd.le_cartan.trans hn)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
