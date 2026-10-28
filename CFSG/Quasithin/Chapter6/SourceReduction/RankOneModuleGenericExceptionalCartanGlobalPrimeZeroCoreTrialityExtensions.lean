module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreLieModels
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.Triality.ExtensionAmalgam

/-!
# Original triality extensions on the selected Cartan pair

Each triality extension endpoint contains its actual local factor. The
arms quotient is nonsolvable at every positive degree, so it cannot be
the source's solvable left endpoint. The central quotient similarly forces
the field degree to one in the other orientation. The broad source's
two-group outer image then collapses the entire automorphism extension,
and compatible restriction of both endpoints and the full overlap feeds
the existing binary-triality exclusion on the same selected R.

The field degree here is the model's parameter, not the original degree n.
The original sourceS is retained. Broad DGS comparison and its two-group
extension clause remain independent inputs; exhaustive recognition and
the final Cartan normalization are not asserted here.
Source: Aschbacher–Smith F.1.12, pp.263–264, and 5.2.2, pp.647–648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook
open _root_.Triality.Standard
variable {G : Type*} [Group G] [Finite G]

/-- Solvability fixes both the orientation and the binary model parameter
before any extension is collapsed. The source degree n is unchanged. -/
theorem LocalData.zeroCore_triality_extension_parameter
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (m : ℕ) (hm : 0 < m) (E : Subgroup (MulAut (BinaryCarrier m hm)))
    (hE : MulAut.innerSubgroup (BinaryCarrier m hm) ≤ E) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (LieModels.Triality.ExtensionAmalgam.amalgam m hm E hE)) ∧
      (Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        (LieModels.Triality.ExtensionAmalgam.amalgam m hm E hE).reverse) → m = 1) := by
  let := (d.zeroCore_mixed_solvability h hH c hd hz).1
  constructor
  · rintro ⟨e⟩
    exact LieModels.Triality.ExtensionAmalgam.arms_endpoint_not_solvable m hm E hE
      (Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective)
  · rintro ⟨e⟩
    by_contra hn
    exact LieModels.Triality.ExtensionAmalgam.central_endpoint_not_solvable m hm E hE
      (by omega)
      (Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective)

/-- Every regular original triality extension by an outer two-group is
excluded on the literal prime pair. The binary restriction retains both
commuting squares before the existing parabolic exclusion is applied. -/
theorem LocalData.zeroCore_not_triality_extension_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (m : ℕ) (hm : 0 < m) (E : Subgroup (MulAut (BinaryCarrier m hm)))
    (hE : MulAut.innerSubgroup (BinaryCarrier m hm) ≤ E)
    (h2 : IsPGroup 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier m hm))))) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (LieModels.Triality.ExtensionAmalgam.amalgam m hm E hE)) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        (LieModels.Triality.ExtensionAmalgam.amalgam m hm E hE).reverse) := by
  have hp := d.zeroCore_triality_extension_parameter h hH c hd hz m hm E hE
  refine ⟨hp.1, ?_⟩
  intro he
  have hm1 := hp.2 he
  subst m
  obtain ⟨e⟩ := he
  let a := (LieModels.Triality.ExtensionAmalgam.binaryIso E hE h2).symm.reverse
  exact d.zeroCore_not_binaryTriality_parabolic h hH c hd hz ⟨e.trans a.toParabolicEquiv⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
