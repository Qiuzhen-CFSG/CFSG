module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Preparation
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import Theory.SpecificGroups.PSL3.LocalResidualFixer
public import Theory.SpecificGroups.PSL3Two.ProperSubgroups
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# The original linear-three containing component

In the binary field every proper subgroup is solvable, excluding the
proper local image. Over a larger field the full restricted Sylow places
that image in one of the two actual parabolic residuals. The nonsolvable
image contains the standard unipotent group, so its automorphism fixer is
trivial. Faithful descent on perfect central covers then gives common
centralization on the original subgroup I.

No module choice, A₅ marking, or bound on a generation parameter enters.
Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02 ChapterA.Section03 Matrix.PSL3.LinearThree
universe u

private theorem local_not_solvable {H : Type*} [Group H]
    {S B : Subgroup H} (hB : B ∈ localCComponents S) : ¬ Group.IsSolvable B := by
  intro hs
  let := hs
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)
  exact hB.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective)

private theorem local_transport {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    (e : H ≃* K) (S : Sylow 2 H) (B : Subgroup H)
    (hl : B ∈ localCComponents S) (hp : B ≠ ⊤) :
    B.map e.toMonoidHom ∈ localCComponents (S.mapSurjective (f := e.toMonoidHom) e.surjective) ∧
      B.map e.toMonoidHom ≠ ⊤ := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  refine ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom, ?_⟩
  intro ht
  apply hp
  apply map_injective (f := e.toMonoidHom) e.injective
  rwa [map_top_of_surjective _ e.surjective]

private theorem binary_local_impossible
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤) : False := by
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Nat.card_zmod])
  let e := (Atlas.fieldEquivPSL 3 a).trans
    Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm
  obtain ⟨hl,hh⟩ := local_transport e S B hB hp
  exact local_not_solvable hl (Matrix.PSL3Two.isSolvable_subgroup_SL_of_ne_top _ hh)

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The literal opposite moved subgroup centralizes every linear-three
containing component from the rank-two catalogue. -/
theorem linear_common_centralizer [Group.IsPerfect I] {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSL (I ⧸ center I) 3 (2 ^ n)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨S,_,hl,_,_,hp,_⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let A := B.map eI.toMonoidHom
  obtain ⟨hA,hpA⟩ := local_transport eI R B hl hp
  have hn2 : 1 < n := by
    by_contra! hh
    have he : n = 1 := by omega
    exact binary_local_impossible (by simpa only [he,pow_one] using hF)
      (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hA hpA
  obtain ⟨g,hg⟩ := SourceEmbeddings.FiveLocalFF.linear_three_local_placement hF hn2
    (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hA hpA
  let f := eI.trans (MulAut.conj g)
  let C := B.map f.toMonoidHom
  have hmap : C = A.map (MulAut.conj g).toMonoidHom := by
    rw [map_map]
    rfl
  have hC : ¬ Group.IsSolvable C := local_not_solvable (local_transport f R B hl hp).1
  have hUC : unipotent F ≤ C := by
    rw [hmap]
    rcases hg with hg | hg
    · rw [hg]
      exact unipotent_le_pointLocal F
    · rw [hg]
      exact unipotent_le_lineLocal F
  intro u hu
  let a : MulAut I := I.normalizerMonoidHom ⟨u, partner_normalizes D c hu⟩
  have hfix : ∀ x ∈ C, MulAut.centralQuotientAction f a x = x := by
    rintro _ ⟨y,⟨l,hl',rfl⟩,rfl⟩
    change MulAut.centralQuotientAction f a (f (q l)) = f (q l)
    rw [MulAut.centralQuotientAction_apply]
    have ha : a l = l := by
      apply Subtype.ext
      change u * l.val * u⁻¹ = l.val
      exact mul_inv_eq_iff_eq_mul.mpr (c.crossed hu l.val hl').symm
    rw [ha]
  have ha : a = 1 := MulAut.centralQuotientAction_injective f
    ((eq_one_of_fixes_nonsolvable_unipotent_overgroup (by omega) hF C hUC hC _ hfix).trans
      (map_one _).symm)
  intro i hi
  have hh := congrArg (fun b : MulAut I => (b ⟨i,hi⟩ : G)) ha
  change u * i * u⁻¹ = i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
