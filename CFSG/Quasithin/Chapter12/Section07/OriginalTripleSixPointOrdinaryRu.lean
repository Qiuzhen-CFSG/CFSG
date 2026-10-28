module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryRuNormalizer
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryRuRadical

/-!
# Excluding the actual Rudvalis ordinary component at the original point

The original radical normalizer fixes a central-class Rudvalis involution.
Radical saturation and the certified two-core center bound exclude the
original elementary image of order at least 32. Every hypothesis comes
from the unchanged chosen-module configuration and specified quotient.

Source: Aschbacher--Smith, 12.7.5, printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original ordinary component cannot have the Rudvalis central quotient. -/
theorem original_tripleSix_point_ordinary_not_ru_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G)))
    (hJ : IsComponent (centralizer ({(t : G)} : Set G)) J)
    (e : J ⧸ center J ≃* Rudvalis.Model) : False := by
  obtain ⟨hP,hE,hcard,hcenter,z,_,hz,hN⟩ :=
    original_tripleSix_point_ordinary_ru_radical_control_at
      h structural D a t ht heven J hJ e
  let := hE
  exact ordinary_ru_large_centered_radical_false _ _ hP hcard hcenter z hz hN

end CFSG.Quasithin.Chapter12.Section07
