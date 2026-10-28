module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.NaturalAveraging
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CubicAveraging

/-!
# Source averaging for both genuine rank-one alternatives

The original setup supplies the intrinsic linear model and its internal
S-action. The preceding Sylow input then constructs the full normalizer
model used by averaging. The cubic alternative is discharged directly by
its order-three quotient. Both give an actual K-fixed representative in
Uc for c∈C_R(UUˣ), with the original cover and conjugator.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/
public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {E : Type*} [Field E]

theorem Setup.source_common_centralizer_le
    (h : Setup R K E)
    (hSylow : (∃ n, IsL2EvenBlock K n) →
      ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = S R ⊓ K)
    {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hNK : R ⊓ centralizer (U K : Set G) ≤ normalizer (K : Set G)) :
    (R ⊓ centralizer (U K : Set G)) ⊓
        centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤
      U K ⊔ (R ⊓ centralizer (K : Set G)) := by
  rcases h.block with ⟨n,hn,hi⟩ | hA
  · have hT := hSylow ⟨n,hn⟩
    obtain ⟨_,_,F,_,_,hF,_,τ,⟨m⟩,hτ⟩ := hn
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let : Algebra (ZMod 2) F := ZMod.algebra F 2
    obtain ⟨d⟩ := h.full_natural_model hi hT τ m hτ
    exact h.natural_common_centralizer_le d hT hx hnc hNK
  · rintro c ⟨hc,_⟩
    have hm := cubic_module_fixer_le hA ⟨hNK hc,hc.2⟩
    have hm' : c ∈ (U K : Set G) * (centralizer (K : Set G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left (U K) (centralizer (K : Set G))
        ((centralizer_le (map_subtype_le _)).trans (Subgroup.centralizer_le_normalizer _))]
      exact hm
    obtain ⟨u,hu,d,hd,rfl⟩ := hm'
    have hdR : d ∈ R := by
      have hh := R.mul_mem (R.inv_mem (h.module_le.trans inf_le_left hu)) hc.1
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem_sup hu ⟨hdR,hd⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
