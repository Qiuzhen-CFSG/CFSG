module
public import Theory.SpecificGroups.SL2.Affine.SurjectiveSubgroup
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryComponent
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import Theory.GroupTheory.RankOneSylowExtension
public import Theory.SpecificGroups.PSL2.RootTwoRank

/-!
# Quasisimplicity of the original secondary component quotient

The source torus has odd order, fixes no element of Q, and centralizes
K₂/O₂(K₂). Coprime fixed-point lifting makes C_K₂(Y) cover that quotient.
Since O₂(K)=Q, its map into the original affine point local is injective.
A subgroup of that affine group with full linear part contains an actual
SL₂(2ⁿ): additive irreducibility makes its translation kernel either zero
or the full plane. This constructs a binary SL₂ subgroup inside K₂.

That simple perfect subgroup survives the two-core of every containing
component. Its two-rank is at least n≥2, excluding the noncentral-Fitting
heads of A.3.6. Thus the chosen original component has quasisimple quotient
by its own two-core. The field, original secondary projection, component
embedding and intrinsic quotient are preserved throughout.

MS construction, the parabolic/Sylow markings, the remaining 4.3.14 radical
geometry and the terminal representation contradiction stay with
qt-d-1222-rankone-uniqueness-nonblock. This does not assert the full nonblock
exclusion. Source: Aschbacher--Smith, original 4.3.12, p.617; A.3.6,
pp.43--45; F.1.12(I), pp.262--264, for the affine local model.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}
namespace RootCoordinates
variable (m : RootCoordinates d)
include m

/-- The original secondary subgroup contains an actual binary SL₂ subgroup.
It is obtained inside the centralizer of the original root torus. -/
theorem exists_secondary_sl2_embedding (hn : 1 < n) :
    ∃ j : SL(2,d.field.Carrier) →* secondary c, Function.Injective j := by
  obtain ⟨Y,_,hY,hYK,hYr,_,hfix,hmove,_⟩ := m.exists_moving_root_torus hn
  have hYN := original_normalizes_secondary hYK hYr
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card (pCore 2 (secondary c))) := by
    obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := secondary c)).exists_card_eq
    rw [hY,hr]
    apply Nat.Coprime.pow_right
    apply Nat.coprime_two_right.mpr
    rw [Nat.odd_iff]
    have hmod := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : n ≠ 0))
    have hpos : 0 < 2^n := pow_pos (by decide) _
    omega
  let := (pCore_isPGroup (p := 2) (G := secondary c)).isNilpotent
  have hs := centralizer_quotient_surjective_of_solvable_coprime (secondary c) Y
    (pCore 2 (secondary c)) hYN inferInstance hcop hmove
  let C := secondary c ⊓ centralizer (Y : Set G)
  let i : C →* secondary c := inclusion inf_le_left
  let f : C →* Matrix.SL2.Affine d.field.Carrier :=
    (pointLocalAffineEquiv d.field.Carrier).toMonoidHom.comp (m.secondaryProjection.comp i)
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hp : m.secondaryProjection (i x) = 1 :=
      (pointLocalAffineEquiv d.field.Carrier).injective
        (hx.trans (pointLocalAffineEquiv d.field.Carrier).map_one.symm)
    have hk : (x : G) ∈ (K c).pCoreIn 2 := by
      have hh : i x ∈ m.secondaryProjection.ker := hp
      rw [m.secondaryProjection_ker] at hh
      exact hh
    have hq : (x : G) ∈ Q c := (d.originalCore_eq hn).le hk
    have he : (x : G) = 1 := mem_bot.mp (hfix ▸ ⟨hq,x.property.2⟩)
    exact mem_bot.mpr (Subtype.ext he)
  have hf : Function.Surjective
      ((SemidirectProduct.rightHom : Matrix.SL2.Affine d.field.Carrier →*
        SL(2,d.field.Carrier)).comp f) := by
    intro a
    obtain ⟨x,hx⟩ := hs ((m.secondaryCoreEquiv hn).symm a)
    refine ⟨x,?_⟩
    have hh := congrArg (m.secondaryCoreEquiv hn) hx
    simp only [MonoidHom.comp_apply] at hh
    rw [MulEquiv.apply_symm_apply,m.secondaryCoreEquiv_mk,
      pointLocalSLCoreQuotientEquiv_mk] at hh
    exact hh
  obtain ⟨j,hj⟩ := Matrix.SL2.embedding_of_affine_projection_surjective f hfi hf
  exact ⟨i.comp j,(inclusion_injective inf_le_left).comp hj⟩

/-- The binary SL₂ survives every solvable normal quotient of a containing group. -/
theorem secondary_sl2_survives_twoCore (hn : 1 < n)
    (B : Subgroup (rootNormalizer c))
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype) :
    ∃ j : SL(2,d.field.Carrier) →* (B ⧸ pCore 2 B), Function.Injective j := by
  obtain ⟨j,hj⟩ := m.exists_secondary_sl2_embedding hn
  have hF : 3 < Nat.card d.field.Carrier := by
    rw [d.field.card_eq,d.degree_eq]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hh
    omega
  let : IsSimpleGroup PSL(2,d.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  let : IsSimpleGroup SL(2,d.field.Carrier) :=
    (Theory.PSL2.sl2QuotientEquiv d.field.Carrier).isSimpleGroup
  let : Group.IsPerfect (secondary c) := EndgameSieve.secondary_perfect c
  let : Group.IsPerfect SL(2,d.field.Carrier) := Group.IsPerfect.ofSurjective
    (f := (m.secondaryCoreEquiv hn).toMonoidHom.comp (QuotientGroup.mk' _))
    ((m.secondaryCoreEquiv hn).surjective.comp (QuotientGroup.mk'_surjective _))
  have hSN : secondary c ≤ rootNormalizer c := hsec.trans (map_subtype_le _)
  let u : secondary c →* B := {
    toFun := fun x => ⟨⟨x,hSN x.property⟩, by
      obtain ⟨b,hb,he⟩ := hsec x.property
      exact (show b = ⟨x,hSN x.property⟩ from Subtype.ext he) ▸ hb⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hu : Function.Injective u := by
    intro x y he
    exact Subtype.ext (congrArg (fun b : B => ((b : rootNormalizer c) : G)) he)
  let := (pCore_isPGroup (p := 2) (G := B)).isNilpotent
  exact ⟨(QuotientGroup.mk' (pCore 2 B)).comp (u.comp j),
    RankOneSylowExtension.simple_quotient_injective
      (Group.IsPerfect.not_isSolvable _) (u.comp j) (hu.comp hj) (pCore 2 B)⟩

/-- The actual binary subgroup excludes the noncentral-Fitting heads of A.3.6. -/
theorem secondary_component_quasisimple (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent)
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype) :
    IsQuasisimple (B ⧸ pCore 2 B) := by
  let := (pCore_isPGroup (p := 2) (G := B)).isNilpotent
  let X := B ⧸ pCore 2 B
  have hX : IsSQTK KnownSimple.IsKnownSimple X := by
    refine ⟨?_,((EndgameSieve.rootNormalizer_sqtk c D h).subgroup B).isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (((EndgameSieve.rootNormalizer_sqtk c D h).subgroup B).stronglyQuasithin p hp ho)
  have htop : (⊤ : Subgroup X).IsCComponent := by
    have ht : (⊤ : Subgroup B).IsCComponent := by
      simpa only [subgroupOf_self] using hB.subgroupOf le_rfl
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      ht.map_quotient (pCore 2 B)
  obtain ⟨j,hj⟩ := m.secondary_sl2_survives_twoCore hn B hsec
  have hr : n ≤ primeRank 2 X := by
    have hh := Theory.PSL2.root_two_rank_ge d.field.Carrier
      (d.field.card_eq.trans (congrArg (2 ^ ·) d.degree_eq))
    rw [←primeRank_equiv 2 (Theory.PSL2.sl2QuotientEquiv d.field.Carrier)] at hh
    exact hh.trans (Theory.GroupTheory.primeRank_le_of_injective 2 j hj)
  let : IsQuasisimple (⊤ : Subgroup X) :=
    ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank hX
      (pCore_quotient_pCore_eq_bot 2) htop (by
        rw [primeRank_equiv 2 (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X)]
        omega)
  exact IsQuasisimple.of_mulEquiv Subgroup.topEquiv
end RootCoordinates

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- Quasisimplicity for the component chosen from the original root geometry. -/
theorem MSData.sourceComponent_quasisimple (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    IsQuasisimple (d.sourceComponent hn D h hL hSL ⧸
      pCore 2 (d.sourceComponent hn D h hL hSL)) := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨hB,_,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  exact m.secondary_component_quasisimple hn D h _ hB hsec.le

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
