module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity.CoreCases
public import Theory.GroupTheory.CentralInvolutionMarking

/-!
# Intrinsic marking in the Aut(M₁₂) source pair

The kernel mark transported by any recognized first parabolic is central.
Its order is two, so full Sylow containment identifies its ambient image
with the original Sylow omega-center. Thus the quotient coordinates retain
the source involution without any extra marking hypothesis.

Source: Aschbacher--Smith 14.2.21, printed p.988.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
open SourceModel.Transport
open Sporadic.Mathieu.M12ExceptionalExtension FirstParabolic
variable {G B R : Type*} [Group G] [Finite G] [Group B] [Group R]

omit [Finite G] in
/-- The transported kernel of the wreath map is central in the actual first
parabolic, under every recognition of the marked pair. -/
theorem markedCore_central (H : Subgroup G) {α : RankTwoAmalgam H B R}
    (r : RankTwoAmalgam.Iso α ChapterF.GreenBook.AutMathieuTwelve.autAmalgam)
    (x : markedCore r) : ((x : pCore 2 H) : H) ∈ center H := by
  apply mem_center_iff.mpr
  intro h
  apply (pairIso r).left.injective
  apply Subtype.ext
  simp only [map_mul,coe_mul]
  have hx : ((pairIso r).left ((x : pCore 2 H) : H)).val ∈ distinguished := by
    rw [←coreEquiv_val]
    exact x.property
  rcases (mem_distinguished _).mp hx with he | he
  · rw [he,mul_one,one_mul]
  · rw [he]
    exact mem_centralizer_singleton_iff.mp ((pairIso r).left h).property

/-- The core marking supplied by arbitrary full-pair recognition is the
original Sylow omega-center; it is not a new choice of central involution. -/
theorem markedCore_image (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    {α : RankTwoAmalgam H B R}
    (r : RankTwoAmalgam.Iso α ChapterF.GreenBook.AutMathieuTwelve.autAmalgam) :
    (markedCore r).map (H.subtype.comp (pCore 2 H).subtype) =
      omegaOneCenterAmbient (T : Subgroup G) := by
  have hcard : Nat.card (markedCore r) = 2 :=
    (Nat.card_congr (markedEquiv r).toEquiv).trans card_distinguished
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := markedCore r) 2 (by rw [hcard])
  let z : H := (x : pCore 2 H)
  have hz : orderOf z = 2 :=
    (orderOf_injective (pCore 2 H).subtype (pCore 2 H).subtype_injective (x : pCore 2 H)).trans
      ((Subgroup.orderOf_coe x).trans hx)
  have he := central_involution_marking T H hTH hZ z (markedCore_central H r x) hz
  rw [←he]
  apply (eq_of_le_of_card_ge ?_ ?_).symm
  · exact zpowers_le.mpr ⟨x,x.property,rfl⟩
  · have hk : Function.Injective (H.subtype.comp (pCore 2 H).subtype) :=
      H.subtype_injective.comp (pCore 2 H).subtype_injective
    rw [card_map_of_injective hk,
      hcard,Nat.card_zpowers]
    exact ((orderOf_injective H.subtype H.subtype_injective z).trans hz).ge

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
end
