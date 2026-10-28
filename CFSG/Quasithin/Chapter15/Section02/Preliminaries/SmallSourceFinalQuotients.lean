module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallSourceCoarseSize
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceBound

/-!
# The original small-source H-star quotients

The proved original mixed bound supplies the two-chief-factor contradiction
in the cubic and Omega rows. The marked-five row was proved independently.
Thus every original H-star quotient is S₃ wreath C₂, with no added mixed
size or recognition premise. Only the permitted original source prior is
retained for its independent producer.

Source: Aschbacher--Smith 15.2.1--8, printed pp.1104--1110.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
variable {G : Type*} [Group G] [Finite G]

/-- Original 15.2.8 for every small action row, with the numerical and
marked-five recognition inputs discharged on the actual H-star subgroups. -/
theorem ChosenSmallSource.HStar_wreath
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hprior : SmallSourcePrior T M V) :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  apply h.HStar_wreath_of_coarse_mixed_size _ hprior
  intro K A S hf _ _ hk ha _
  exact ChapterF.Source.MixedDGS.mixed_a5_s3_sylow_card_le_1024 hf hk ha

end CFSG.Quasithin.Chapter15.Section02
