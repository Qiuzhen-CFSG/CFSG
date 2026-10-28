module
public import CFSG.Quasithin.Chapter1.Section03.Basic
public import CFSG.Quasithin.ChapterB.Section06To07.Residual
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Xi membership from the minimal-parabolic core

When the maximal-overgroup core is the two-core, an invariant subgroup of
the residual Frattini quotient lifts to a normal subgroup of the whole group.
The minimal-parabolic dichotomy forces that lift into the two-core or makes
it contain the full residual. Thus an elementary residual quotient of order
p² satisfies the irreducibility clause of Definition 1.3.1.

Source: Aschbacher–Smith, B.6.8(4), applied in Lemma 13.2.10, printed p.881.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1
variable {K : Type*} [Group K] [Finite K]

/-- An elementary rank-two residual quotient belongs to Xi when the
minimal-parabolic maximal core is exactly the two-core. -/
theorem residual_mem_Xi_of_minimalParabolic_core_eq
    (S : Sylow 2 K) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (hcore : ChapterB.minimalParabolicCore S hP = pCore 2 K)
    (hH : (⊤ : Subgroup K) ∈ H K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    [he : IsElementaryAbelian p (XiQuotient (pResidual 2 K))]
    (hc : Nat.card (XiQuotient (pResidual 2 K)) = p ^ 2) :
    pResidual 2 K ∈ Xi K (S : Subgroup K) := by
  let X := pResidual 2 K
  have hn : (S : Subgroup K) ≤ normalizer (X : Set K) := le_normalizer_of_normal
  refine ⟨isPPerfect_pResidual 2, hn, ?_, ⟨p,hp,ho,Or.inl ⟨he,hc⟩⟩, ?_⟩
  · simpa only [pResidual_sup_sylow_eq_top] using hH
  · intro A hA
    let f : X →* XiFrattiniQuotient X :=
      (QuotientGroup.mk' (frattini (XiQuotient X))).comp (QuotientGroup.mk' (pCore 2 X))
    have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
      (QuotientGroup.mk'_surjective _)
    let B := A.comap f
    let N := B.map X.subtype
    have hBN : B.Normal := inferInstance
    have hXN : X ≤ normalizer (N : Set K) := by
      have hh := B.le_normalizer_map X.subtype
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
    have hSN : (S : Subgroup K) ≤ normalizer (N : Set K) := by
      apply le_normalizer_iff.mpr
      rintro s hs x ⟨y,hy,rfl⟩
      let z : X := ⟨s * (y : K) * s⁻¹,
        (mem_normalizer_iff.mp (hn hs) (y : K)).mp y.property⟩
      refine ⟨z,?_,rfl⟩
      change f z ∈ A
      have hh := hA (⟨s,hs⟩ : (S : Subgroup K)) (f y) hy
      change xiFrattiniAction (S : Subgroup K) X hn ⟨s,hs⟩
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ y)) ∈ A at hh
      simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk] at hh
      exact hh
    have hN : N.Normal := normalizer_eq_top_iff.mp (top_unique (by
      rw [← pResidual_sup_sylow_eq_top S]
      exact sup_le hXN hSN))
    let _ := hN
    rcases ChapterB.minimalParabolic_normal_subgroup_residual_dichotomy S hP N with hNC | hXN'
    · left
      rw [hcore] at hNC
      have hBQ : B ≤ pCore 2 X := by
        apply le_sSup
        refine ⟨hBN,?_⟩
        have hb : B ≤ (pCore 2 K).subgroupOf X := by
          intro x hx
          exact hNC (mem_map_of_mem X.subtype hx)
        exact (pCore_isPGroup (p := 2) (G := K)).comap_subtype.to_le hb
      apply bot_unique
      intro a ha
      obtain ⟨x,rfl⟩ := hf a
      have hx : x ∈ pCore 2 X := hBQ ha
      change f x = 1
      dsimp only [f,MonoidHom.comp_apply]
      have hxq : QuotientGroup.mk' (pCore 2 X) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      rw [hxq,map_one]
    · right
      apply top_unique
      intro a _
      obtain ⟨x,rfl⟩ := hf a
      obtain ⟨y,hy,hyx⟩ := hXN' x.property
      have hyx' : y = x := X.subtype_injective hyx
      exact hyx' ▸ hy
end CFSG.Quasithin.Chapter1
