module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.NativeCore
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Cartan

/-!
# Cartan calculations in the supplied full Ree completion

The actual marked native Borel map is injective. Its literal positive and
Cartan images therefore inherit the no-fixed-point and Borel-normalizer
calculations from the native model. No global map from the native group is
used, and no order bound or recognition premise is needed.

Source: the local input to Aschbacher–Smith F.4.10,16, pp.279,282.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
open Subgroup Theory.GroupTheory ReeF4.Parabolics
variable {m : ℕ} (E : SourceExtension m) {M : Type*} [Group M] (c : Completion E M)

/-- The marked native Borel homomorphism into the original full completion. -/
def nativeBorelMap : borel m →* M :=
  (nativeLeft E c).comp (inclusion (borel_le_parabolic m .linear))

private theorem nativeBorelMap_injective (hm : 0 < m) : Function.Injective (nativeBorelMap E c) :=
  fun _ _ h => (nativeCompletion E c hm).middle_injective (Subtype.ext h)

/-- The literal native Cartan image in the original full completion. -/
def nativeCartan : Subgroup M :=
  ((fixedTorus m).subgroupOf (borel m)).map (nativeBorelMap E c)

/-- The literal positive-root image in the original full completion. -/
def nativePositive : Subgroup M :=
  ((unipotent m).subgroupOf (borel m)).map (nativeBorelMap E c)

/-- The marked native torus fixes no nonidentity positive element in any completion. -/
theorem nativePositive_inf_centralizer_nativeCartan (hm : 0 < m) :
    nativePositive E c ⊓ centralizer (nativeCartan E c : Set M) = ⊥ :=
  ReeF4.SmallCompletion.mapped_unipotent_inf_centralizer_fixedTorus hm
    (nativeBorelMap E c) (nativeBorelMap_injective E c hm)

/-- Cartan self-normalization holds in the original native Borel image. -/
theorem nativeBorel_inf_normalizer_nativeCartan (hm : 0 < m) :
    (nativeBorelMap E c).range ⊓ normalizer (nativeCartan E c : Set M) = nativeCartan E c :=
  ReeF4.SmallCompletion.mapped_borel_inf_normalizer_fixedTorus hm
    (nativeBorelMap E c) (nativeBorelMap_injective E c hm)

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
