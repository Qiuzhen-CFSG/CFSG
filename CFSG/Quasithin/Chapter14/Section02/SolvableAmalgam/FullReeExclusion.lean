module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.OriginalSource
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.Tits
public import Theory.GroupTheory.Recognition.ReeTwo.CentralizerExclusion

/-!
# Excluding the full binary Ree row in original 14.2.22

Original 14.2.21 identifies the first parabolic with the centralizer of
the order-two Sylow omega-center. Choosing its nonidentity element gives
the literal centralizer required by the proved full-Ree transfer theorem.
The concrete first-parabolic equivalence identifies this centralizer with
the verified Ree two local group, so nonsolvable simplicity excludes the row.

The source application derives local rigidity from the original hypotheses.
It needs neither a small-completion witness nor global amalgam recognition.
The Tits row, whose first parabolic has half the order, remains separate.

Source: Aschbacher--Smith 14.2.21--22, printed pp.988--989. The independent
full-Ree centralizer exclusion and its sources are documented in
`Theory.GroupTheory.Recognition.ReeTwo.CentralizerExclusion`.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The full Ree first parabolic cannot be the original central-involution
centralizer in a nonsolvable simple ambient group. -/
theorem full_ree_exclusion [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (T : Sylow 2 G) (H : Subgroup G)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hH : H = centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (eH : Tits.ExceptionalParabolics.FullRee.first ≃* H) : False := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2
    (hZ ▸ (by decide : 2 ∣ 2))
  have hzG : orderOf (z : G) = 2 :=
    (orderOf_injective Z.subtype Z.subtype_injective z).trans hz
  have hzgen : zpowers (z : G) = Z :=
    eq_of_le_of_card_ge (zpowers_le.mpr z.property) (by
      rw [Nat.card_zpowers,hzG]
      exact hZ.le)
  have hC : centralizer ({(z : G)} : Set G) = H := by
    calc
      _ = centralizer (zpowers (z : G) : Set G) := by
        rw [zpowers_eq_closure,centralizer_closure]
      _ = H := (congrArg (fun K : Subgroup G => centralizer (K : Set G)) hzgen).trans hH.symm
  have hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp z.property).2.2 t ht)
  exact ReeTwo.false_of_centralizer_equiv hns T z hzG hTC
    ((MulEquiv.subgroupCongr hC).trans
      (eH.symm.trans ReeTwo.ParabolicMarkedComparison.Verified.firstEquiv.symm))

/-- Original 14.2.21 supplies all centralizer premises needed to exclude the
full Ree parabolic, without a compatibility or global recognition assumption. -/
theorem source_full_ree_parabolic_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel : Nonempty (Tits.ExceptionalParabolics.FullRee.first ≃* H)) : False := by
  let : IsSimpleGroup G := hG.simple
  have hns : ¬ Group.IsSolvable G := fun hs =>
    hG.nonabelian (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,_,hMc,_⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  have hHMc := (ReeLocal.source_ree_tits_rigidity hG T hempty hM hu hmany hcard e
    H hH (Or.inl hmodel)).1
  exact full_ree_exclusion hns T H hZ (hHMc.trans hMc) hmodel.some

/-- The marked full-Ree row of the actual 14.2.20 inclusion amalgam is
excluded under the unchanged original source hypotheses. -/
theorem source_full_ree_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel : ChapterF.GreenBook.IsBinaryReeAmalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right)) : False := by
  obtain ⟨m⟩ := hmodel
  exact source_full_ree_parabolic_exclusion hG T hempty hM hu hmany hcard e H hH
    ⟨m.left.symm⟩

/-- The original Ree/Tits alternatives leave only the Tits amalgam, with the
original centralizer and second-parabolic equalities already discharged. -/
theorem source_tits_of_ree_tits_marks
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel :
      ChapterF.GreenBook.IsBinaryReeAmalgam
        (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
          (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right) ∨
      ChapterF.GreenBook.IsAtlasTitsAmalgam
        (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
          (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right)) :
    ChapterF.GreenBook.IsAtlasTitsAmalgam
        (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
          (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right) ∧
      H = Mc ∧ M = sourceResidual M Mc ⊔ (T : Subgroup G) ∧
      H = centralizer (centralInvolutions T : Set G) := by
  rcases hmodel with hfull | htits
  · exact (source_full_ree_exclusion hG T hempty hM hu hmany hcard e H hH hfull).elim
  · have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
    obtain ⟨_,_,hMc,_⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
    obtain ⟨hHMc,hMX⟩ := ReeLocal.source_ree_tits_rigidity hG T hempty hM hu hmany
      hcard e H hH (Or.inr ⟨htits.some.left.symm⟩)
    exact ⟨htits,hHMc,hMX,hHMc.trans hMc⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
