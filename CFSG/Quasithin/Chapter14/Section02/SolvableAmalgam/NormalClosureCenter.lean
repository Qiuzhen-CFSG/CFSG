module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalOppositeCenter
public import CFSG.Quasithin.Chapter14.Section02.ProperOutsideSylow
public import CFSG.Quasithin.ChapterG.Section02.Binary.CenterFixedLine

/-!
# Removing the central radical in the original normal Bender row

The original opposite-core geometry contains the full center of the
closure. A center of order four would give a fixed line normalized by
both parabolics, contradicting the actual generated two-core being
trivial. The closure therefore has center of order two and order 32
or 512 in the respective four- and eight-field cases. This removes the
larger radical alternatives before the F.1.12 recognition consumer.

Source: Aschbacher–Smith 14.2.16/F.1.12,
printed pp.985–986 and 262–264.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter12.Section08
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

 theorem source_normal_bender_closure_extraspecial_orders
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (f : ℕ) (hm : BenderModel ((H ⊓ M).subgroupOf H) K f) :
    let U := conjugateSpanBy (localModule T M) H
    Nat.card (center U) = 2 ∧
      ((f = 2 ∧ Nat.card U = 32) ∨ (f = 3 ∧ Nat.card U = 512)) := by
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h,⟨b⟩,_⟩ := source_nonabelian_binary_data hG T hempty hM hu hmany hcard e H hH.1 hne
  obtain ⟨g,hg,hgN,hCE⟩ := source_normal_bender_center_le_opposite
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen f hm
  let : Group.IsPerfect K := hK.perfect
  have hgen' : K.map H.subtype ⊔ (T : Subgroup G) = H := by
    have he := congrArg (Subgroup.map H.subtype) hgen
    change (K ⊔ (T : Subgroup G).subgroupOf H).map H.subtype =
      (⊤ : Subgroup H).map H.subtype at he
    simpa only [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hH.1.1.2] using he
  have hnot : Nat.card (center D.U) ≠ 4 :=
    ChapterG.Section02.Setup.binary_center_card_ne_four_of_opposite h b hne
      g hg hgN hCE
      (source_residual_twoCore_quotient_card hG T hempty hM hu hmany hcard e)
      K hgen' (source_solvable_amalgam_twoCore_eq_bot
        hG T hempty hM hu hmany hcard e H hH.1.2)
  have hs := source_normal_bender_closure_structure
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen f hm
  rcases hs with ⟨hf,hs | hs⟩ | ⟨hf,hs | hs⟩
  · exact ⟨hs.2,Or.inl ⟨hf,hs.1⟩⟩
  · exact (hnot hs.2).elim
  · exact ⟨hs.2,Or.inr ⟨hf,hs.1⟩⟩
  · exact (hnot hs.2).elim
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
