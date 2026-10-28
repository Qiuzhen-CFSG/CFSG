module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.FullNormalizer
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.OuterSylow

/-!
# Outer degree and the original Sylow in the marked Ree extension

The original prepared inputs construct the simultaneous full-normalizer
marking. For this very carrier, the native automorphism calculation supplies
a cyclic outer quotient of odd order dividing the original field degree,
the exact O^{2′} subgroup, and the exact carrier-order factorization.
The entire original ambient Sylow maps through the full common-normalizer
comparison to a Sylow of this extension. Both endpoint markings and the
whole Borel comparison remain in the same witness.

This discharges the Ree outer/Sylow step of F.4.38. Involution exhaustion,
full short-root centralizer containment, and the ambient order comparison
with this carrier remain necessary for ambient recognition.
Source: Aschbacher–Smith 5.3.1–3 and F.4.29,33,38,43,
printed pp.658–659,289,291,294,296 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
variable {G : Type*} [Group G]

/-- The literal full common-normalizer map into the same extension carrier. -/
@[expose] def FullNormalizerMarking.middleToCarrier {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β) :
    (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* D.extension.carrier :=
  (inclusion (inf_le_left.trans D.extension.left_le)).comp D.full.middle.toMonoidHom

variable [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include d h hH hp he

/-- The actual prepared full-normalizer extension has odd cyclic outer degree,
exact prime-to-two residual, and the marked original ambient Sylow. -/
theorem Preparation.ree_full_extension_outer_sylow :
    2*m+1 = n ∧ 0 < m ∧
    ∃ D : ReeNormalizerMarking L (residual H) (sourceS L H) m,
      let J := (MulAut.innerSubgroup (ReeF4.Model m)).subgroupOf D.extension.carrier
      J.index ∣ 2*m+1 ∧ Odd J.index ∧ IsCyclic (D.extension.carrier ⧸ J) ∧
      primeToResidual 2 D.extension.carrier = J ∧
      Nat.card D.extension.carrier = J.index * Nat.card (ReeF4.Model m) ∧
      (T : Subgroup G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      ∃ S : Sylow 2 D.extension.carrier,
        (S : Subgroup D.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map D.middleToCarrier := by
  obtain ⟨hn,hm,⟨D⟩⟩ := d.ree_full_normalizer_marking h hH hp m he
  obtain ⟨_,hTL,hTK,_⟩ := d.ree_full_sylow h hH hp m he
  have hTI : (T : Subgroup G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
    le_inf (hTL.trans L.le_normalizer) (hTK.trans (residual H).le_normalizer)
  refine ⟨hn,hm,D,ReeF4.SourceCompletion.extension_inner_index_dvd hm D.extension.carrier,
    ReeF4.SourceCompletion.extension_inner_index_odd hm D.extension.carrier,
    ReeF4.SourceCompletion.extension_outer_cyclic hm D.extension.carrier,
    ReeF4.SourceCompletion.extension_primeToResidual hm D.extension.carrier D.extension.contains_inner,
    ReeF4.SourceCompletion.extension_card_factor hm D.extension.carrier D.extension.contains_inner,
    hTI,?_⟩
  exact GeneralReeFour.extension_middle_sylow D.extension hm D.full.middle (T.subtype hTI)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
