module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryMixedCubic
public import Mathlib.GroupTheory.IndexNormal

/-!
# Excluding both concrete Hall--Janko amalgams

An elementary subgroup of order sixteen in a group of order 32 is normal
of index two. Its intersection with a quaternion subgroup has order at most
two, contradicting the subgroup product formula. The original natural layer
is elementary of order sixteen and lies in the full two-core of LT.

The actual first Hall--Janko core has order 32 and contains the checked
quaternion factor. The same full core is transported through the concrete
outer numerator and the fixed equivalence with Aut(J2). Hence neither
first vertex can be LT. In the reversed orientation, the original right
parabolic is solvable whereas each model's first vertex has a nonsolvable
A5 section. This excludes both orientations, even for parabolic equivalence
without compatibility of overlap maps.

The final application retains the same escaping subgroup, whole overlap,
quotient maps, cubic constraints and unitary exclusions. These are exclusions
of the fixed concrete models; general mixed-amalgam recognition remains to
be proved. S5 parabolic escape, initial 6.1.4–5, omega escape and the remaining
geometry through unconditional 6.1.27 stay with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed p.675, and F.1.12(I)(10–11),
printed p.263 (`refs/quasithin.pdf`). The imported Hall--Janko models retain
their original ATLAS carrier, attribution and checked structure calculations.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalJanko
open ChapterF.GreenBook.HallJanko
open Sporadic.LeechRelated.J2.ExceptionalParabolics

private theorem quaternion_elementary_card_le_two
    {H : Type*} [Group H] (A Q : Subgroup H) [IsElementaryAbelian 2 A]
    (e : Q ≃* QuaternionGroup 2) : Nat.card (A ⊓ Q : Subgroup H) ≤ 2 := by
  let f : (A ⊓ Q : Subgroup H) → {x : QuaternionGroup 2 // x^2=1} := fun x =>
    ⟨e ⟨x,x.property.2⟩,by
      rw [←map_pow]
      have hh : (⟨x,x.property.2⟩ : Q)^2=1 :=
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ x.property.1)
      rw [hh,map_one]⟩
  have hi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : Q => (z : H)) (e.injective (congrArg Subtype.val he))
  have hc : Nat.card {x : QuaternionGroup 2 // x^2=1}=2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact (Nat.card_le_card_of_injective f hi).trans_eq hc

private theorem no_elementary_sixteen
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H=32)
    (Q : Subgroup H) (e : Q ≃* QuaternionGroup 2)
    (A : Subgroup H) [IsElementaryAbelian 2 A] (hA : Nat.card A=16) : False := by
  have hindex : A.index=2 := by
    have hh := A.card_mul_index
    rw [hA,hH] at hh
    omega
  let : A.Normal := A.normal_of_index_eq_two hindex
  have hn : Q ≤ normalizer (A : Set H) := by rw [A.normalizer_eq_top]; exact le_top
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A Q hn
  have hQ : Nat.card Q=8 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hi := quaternion_elementary_card_le_two A Q e
  have hs : Nat.card (A ⊔ Q : Subgroup H) ≤ 32 :=
    (Nat.card_le_card_of_injective _ (A ⊔ Q).subtype_injective).trans_eq hH
  rw [hA,hQ] at hh
  nlinarith [Nat.mul_le_mul hi hs]

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

private theorem natural_not_quaternion_core
    {H : Type*} [Group H] [Finite H]
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hQ : Sporadic.LeechRelated.J2.IsQuaternionDihedralCore (pCore 2 H)) :
    ¬ Nonempty ((L ⊔ (T : Subgroup G) : Subgroup G) ≃* H) := by
  rintro ⟨e⟩
  let X := L ⊔ (T : Subgroup G)
  let V := layer L R
  have hVQ : V ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le h.layer_le_T) (h.layer_le_L.trans le_sup_left)
    (sup_le (normalizer_commutator_ge_right R L) h.sylow_normalizes_layer)
  let a : (pCore 2 X) ≃* X.pCoreIn 2 :=
    (pCore 2 X).equivMapOfInjective X.subtype X.subtype_injective
  let b := LocalCoreTransport.coreEquiv 2 e
  let f : V →* pCore 2 H := b.toMonoidHom.comp
    (a.symm.toMonoidHom.comp (inclusion hVQ))
  have hi : Function.Injective f := b.injective.comp (a.symm.injective.comp (inclusion_injective hVQ))
  let := h.layer_elementary
  let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hf : Nat.card f.range=16 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,hnat.card]
    norm_num
  obtain ⟨Q,_,⟨eQ⟩,_,_,_,_,h32⟩ := hQ
  exact no_elementary_sixteen h32 Q eQ f.range hf

private def outer_core_equiv : pCore 2 Seed.l₁ ≃* pCore 2 Seed.l₁s :=
  FirstParabolic.radicalCoreEquiv.symm.trans
    (((FirstParabolic.radical.equivMapOfInjective intoExtension
      SecondParabolic.intoExtension_injective).trans
      (subgroupOfEquivOfLe FirstParabolic.outerRadical_le_l₁s).symm).trans
      (MulEquiv.subgroupCongr FirstParabolic.l₁s_core_eq.symm))

private theorem outer_core :
    Sporadic.LeechRelated.J2.IsQuaternionDihedralCore (pCore 2 Seed.l₁s) := by
  obtain ⟨B,C,⟨eB⟩,⟨eC⟩,hi,hcomm,hgen,hcard⟩ :=
    ChapterF.GreenBook.HallJanko.FirstParabolic.l₁_core_isQuaternionDihedralCore
  let e := outer_core_equiv
  refine ⟨B.map e.toMonoidHom,C.map e.toMonoidHom,
    ⟨(e.subgroupMap B).symm.trans eB⟩,⟨(e.subgroupMap C).symm.trans eC⟩,?_,?_,?_,?_⟩
  · rw [←Subgroup.map_inf _ _ _ e.injective,card_map_of_injective e.injective,hi]
  · rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    rw [←map_mul,←map_mul,hcomm b hb c hc]
  · rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ e.surjective]
  · exact (Nat.card_congr e.symm.toEquiv).trans hcard

private theorem inner_not_solvable : ¬ Group.IsSolvable Seed.l₁ := by
  intro hs
  let := hs
  let e := FirstParabolic.l₁_quotient.some
  let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

private theorem outer_not_solvable : ¬ Group.IsSolvable Seed.l₁s := by
  intro hs
  let := hs
  let f : Seed.l₁ →* Seed.l₁s :=
    (inclusion (show Seed.outerL 0 ≤ Seed.l₁s from le_sup_left)).comp
      (Seed.l₁.equivMapOfInjective intoExtension SecondParabolic.intoExtension_injective).toMonoidHom
  exact inner_not_solvable (Group.isSolvable_of_isSolvable_injective (f := f)
    ((inclusion_injective (show Seed.outerL 0 ≤ Seed.l₁s from le_sup_left)).comp (Seed.l₁.equivMapOfInjective intoExtension
      SecondParabolic.intoExtension_injective).injective))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalJanko

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterF.GreenBook.HallJanko
open Sporadic.LeechRelated.J2.ExceptionalParabolics
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- The order-sixteen natural layer excludes both concrete Hall--Janko
first vertices, including the full outer numerator. Their intrinsic cores
have order 32 and contain the actual quaternion factor. -/
theorem natural_four_not_janko_first_vertex
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2) :
    (¬ Nonempty ((L ⊔ (T : Subgroup G) : Subgroup G) ≃* j2Model.toMarking.P 0)) ∧
    (¬ Nonempty ((L ⊔ (T : Subgroup G) : Subgroup G) ≃* autJ2Model.toMarking.P 0)) := by
  have hi := NaturalJanko.natural_not_quaternion_core h hnat
    ChapterF.GreenBook.HallJanko.FirstParabolic.l₁_core_isQuaternionDihedralCore
  have ho := NaturalJanko.natural_not_quaternion_core h hnat NaturalJanko.outer_core
  constructor
  · rintro ⟨e⟩
    exact hi ⟨e.trans (MulEquiv.subgroupCongr j2Model_P_zero)⟩
  · rintro ⟨e⟩
    apply ho
    exact ⟨(e.trans extensionAutAmalgamIso.left.symm).trans
      (MulEquiv.subgroupCongr extensionModel_P_zero)⟩

/-- Both orientations are excluded using the original left natural core
and solvability of the original right parabolic, respectively. -/
@[expose] def NaturalJankoAmalgamExclusion (T : Sylow 2 G) (L B : Subgroup G) : Prop :=
    let P := ChapterF.Source.parabolic ![L,B] (T : Subgroup G)
    let D := ChapterF.Source.commonBorel ![L,B] (T : Subgroup G)
    let α := RankTwoAmalgam.ofSubgroups (P 0) D (P 1)
      (ChapterF.Source.commonBorel_le_parabolic 0) (ChapterF.Source.commonBorel_le_parabolic 1)
    let β := RankTwoAmalgam.ofSubgroups (P 1) D (P 0)
      (ChapterF.Source.commonBorel_le_parabolic 1) (ChapterF.Source.commonBorel_le_parabolic 0)
    (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv α j2Model.toMarking.amalgam)) ∧
    (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv β j2Model.toMarking.amalgam)) ∧
    (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv α autJ2Model.toMarking.amalgam)) ∧
    (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv β autJ2Model.toMarking.amalgam))

theorem natural_cubic_amalgam_not_janko
    {B : Subgroup G}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hs : Group.IsSolvable (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1)) :
    NaturalJankoAmalgamExclusion T L B := by
  obtain ⟨hi,ho⟩ := natural_four_not_janko_first_vertex h hnat
  have hP := (natural_cubic_amalgam_products hF e).1
  rw [←hP] at hi ho
  let := hs
  refine ⟨fun ⟨j⟩ => hi ⟨j.left⟩,?_,fun ⟨j⟩ => ho ⟨j.left⟩,?_⟩
  · rintro ⟨j⟩
    let f := j.left.trans (MulEquiv.subgroupCongr j2Model_P_zero)
    exact NaturalJanko.inner_not_solvable (Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective)
  · rintro ⟨j⟩
    let f := (j.left.trans extensionAutAmalgamIso.left.symm).trans
      (MulEquiv.subgroupCongr extensionModel_P_zero)
    exact NaturalJanko.outer_not_solvable (Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]
/-- The same escaping pair, retaining both original maps and all cubic
geometry, excludes the concrete ordinary and automorphism Hall--Janko rows. -/
@[expose] def NaturalEscapingAmalgamJankoData (T : Sylow 2 G) (L R P N M : Subgroup G) : Prop :=
  ∃ B : Subgroup G, B ≤ P ⊔ N.pCoreIn 2 ∧
    B ≤ Escape.I (T : Subgroup G) L R ∧ (¬ B ≤ M) ∧
    Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
    ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G) ∧
    Group.IsSolvable (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1) ∧
    ChapterF.Source.LocallyRankOneTriple
      (fun i => (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) i).subgroupOf
        (ChapterF.Source.generated ![L,B] (T : Subgroup G)))
      ((ChapterF.Source.commonBorel ![L,B] (T : Subgroup G)).subgroupOf
        (ChapterF.Source.generated ![L,B] (T : Subgroup G))) ∧ NaturalUnitaryAmalgamExclusion T L B ∧
      NaturalJankoAmalgamExclusion T L B ∧
    ∀ e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3),
      NaturalCubicRightQuotientData T L R B e ∧
      NaturalCubicRightCoreData T L R B ∧
      NaturalCubicRightCubicData T L R B e ∧
      let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
      (Nonempty ((J ⧸ pCore 2 J) ≃*
          Equiv.Perm (Fin 3) × alternatingGroup (Fin 3)) ∧
        Nat.card T = 2 * Nat.card (pCore 2 J)) ∨
      (Nonempty ((J ⧸ pCore 2 J) ≃*
          Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
        Nat.card T = 4 * Nat.card (pCore 2 J))

variable [Finite G] {T : Sylow 2 G} {L M R P N : Subgroup G}

/-- Apply both Hall--Janko exclusions to the original escaping pair while
retaining its entire marked quotient and cubic geometry. -/
theorem natural_escaping_amalgam_janko_exclusion
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (d : NaturalEscapingAmalgamCubicData T L R P N M) :
    NaturalEscapingAmalgamJankoData T L R P N M := by
  obtain ⟨B,hBK,hBI,hBM,he,hF,hsolv,htriple,hno,hright⟩ := d
  exact ⟨B,hBK,hBI,hBM,he,hF,hsolv,htriple,hno,
    natural_cubic_amalgam_not_janko h hnat hF he.some hsolv,hright⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
