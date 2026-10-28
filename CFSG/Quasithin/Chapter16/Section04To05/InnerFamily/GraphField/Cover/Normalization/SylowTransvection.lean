module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Normalization.SylowTransvection.Transfer
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Normalization.SylowTransvection.ProjectiveFixedSylow

/-!
# The marked Sylow transvection in the graph-field cover

The marked cover transvection r ↦ rz is realized in the original prepared
Sylow subgroup T. The intrinsic graph-field fixed-Sylow theorem supplies
Sylow saturation in the projective fixed subgroup. Lifting through the
central two-kernel gives saturation in L ∩ N_G(⟨r,z⟩); conjugating the
component factor of the model transvection into this subgroup places the
actor in T while preserving its action on both marks.

The intrinsic normalizer and cover-action witnesses remain explicit source
inputs. The projective fixed-Sylow premise of the transfer is discharged here.
Compatible placement of the whole quaternion model is a separate consumer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.9(2), printed p.1191.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter16.Intersections.GraphField.SylowTransvection

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {r z g : G} {L R : Subgroup G}

/-- The cover transvection lies in the fixed prepared Sylow subgroup.
The projective fixed-Sylow assertion is proved for the genuine matrix model;
no position of the intrinsic quaternion subgroup in T is required. -/
theorem exists_transvection_prepared {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z) (hcore : pCore 2 L ≠ ⊥)
    (hmodel : IsL3FourGraphField L r)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (d : NormalizerData L r z) (c : CoverActionData d) :
    ∃ t ∈ (T : Subgroup G) ⊓ normalizer (fourGroup r z : Set G),
      MulAut.conj t r = r * z :=
  exists_transvection_prepared_of_projective_fixedSylow projectiveFixedSylow
    hG h hr hr2 hout hTC hcore hmodel hD h9 d c

end CFSG.Quasithin.Chapter16.Intersections.GraphField.SylowTransvection
