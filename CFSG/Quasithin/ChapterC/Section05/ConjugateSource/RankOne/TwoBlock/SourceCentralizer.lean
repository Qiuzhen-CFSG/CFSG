module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.FullCentralizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CubicCentralizer

/-!
# The full centralizer supplement for the original rank-one block

This applies the full-normalizer calculation to the literal intrinsic block
model. In the linear case the genuine preceding assertion S∩K∈Syl₂(K)
marks its image; internality already belongs to the original setup. In the
A₃ case the original module has order four, so no Sylow premise is needed.

Source: Aschbacher–Smith, C.5.4 and C.5.6(7), printed pp.155,159–160.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {E : Type*} [Field E]

/-- The independent earlier Sylow input is only requested in the linear
branch. The normalizer premise comes from the original source orbit. -/
theorem Setup.source_full_centralizer_le
    (h : Setup R K E) (hR : IsPGroup 2 R)
    (hSylow : (∃ n, IsL2EvenBlock K n) →
      ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = S R ⊓ K)
    {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hNK : R ⊓ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤ normalizer (K : Set G)) :
    R ⊓ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤
      (U K).map (MulAut.conj x⁻¹).toMonoidHom ⊔ (R ⊓ centralizer (U K : Set G)) := by
  rcases h.block with ⟨n,hn,hi⟩ | hA
  · obtain ⟨P,hP⟩ := hSylow ⟨n,hn⟩
    obtain ⟨_,_,F,_,_,hF,_,τ,⟨m⟩,hτ⟩ := hn
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let : Algebra (ZMod 2) F := ZMod.algebra F 2
    obtain ⟨d⟩ := h.full_natural_model hi ⟨P,hP⟩ τ m hτ
    exact h.full_centralizer_le_conjugate_sup d hR hx hnc hNK
  · exact h.cubic_full_centralizer_le hA hx hnc hNK
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
