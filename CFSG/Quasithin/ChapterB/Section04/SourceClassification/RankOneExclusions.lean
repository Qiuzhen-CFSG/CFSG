module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SuzukiRecognition.Source
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SourceAssembly
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenScalarLift

/-!
# Excluding unitary and Suzuki layers from B.4.2

The proved Suzuki recognition has quadratic ratio two. For PSU3(2^n), the
actual SU3 scalar lift is constructed using every completed odd-primary
covering bound, so the natural-module recognition and ratio theorem need no
extra covering input. Both actual original representations therefore have
ratio two and cannot be FF-modules.

Source: Aschbacher--Smith K.3.3 and K.3.6, pp.456--457; B.4.2, p.86.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceClassification
open ComponentRecognition.KnownFFTypes.Classical
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem not_ff_suzuki (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* SuzukiMatrixGroup m) :
    ¬ IsFFModule ρ := by
  classical
  intro hff
  have hq := (isFFModule_iff_quadraticRatio_le_one ρ).mp hff
  have hs := h.suzuki_case_of_quotient hm e (Classical.choice (inferInstance : Nonempty (Sylow 2 G)))
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hquad,_,_⟩ := hs
  rw [hquad] at hq
  norm_num at hq

theorem unitary_central_quotient (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    IsCentralQuotient L J.specialSubgroup := by
  let := h.quasisimple
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨k,hk,hfac⟩ := HermitianForm.UniversalCover.exists_even_scalar_lift J hn hcard hconj
    f hf h.layer_twoCore_eq_bot
  refine ⟨k.ker,inferInstance,?_,⟨(QuotientGroup.quotientKerEquivOfSurjective k hk).symm⟩⟩
  intro x hx
  apply J.specialToProjective_ker_le_center
  have hx1 : k x = 1 := MonoidHom.mem_ker.mp hx
  apply MonoidHom.mem_ker.mpr
  rw [← hfac,MonoidHom.comp_apply,hx1,map_one]

theorem not_ff_unitary (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 2 ≤ n)
    (he : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n)) : ¬ IsFFModule ρ := by
  classical
  intro hff
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := he
  let : CharP F 2 := Theory.SpecificGroups.UnitaryRootNormalizer.charP_binary (by omega) hcard
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hc := unitary_central_quotient h J hn hcard hconj e
  have hcalc := ChapterK.RankOne.UnitaryRecognition.source_case_of_centralQuotient
    J h hn hcard hconj hc (Classical.choice (inferInstance : Nonempty (Sylow 2 G)))
  have hq := (isFFModule_iff_quadraticRatio_le_one ρ).mp hff
  rw [hcalc.1] at hq
  norm_num at hq
end CFSG.Quasithin.ChapterB.SourceClassification
