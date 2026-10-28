module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.Data
public import Theory.GroupTheory.PCoreSurjective

/-!
# Faithfulness on P* from the source parabolic-core placement

If K = PJ with P normal, the intersection of a normal two-subgroup of J
with C_K(P) is normal in K: J normalizes it and P centralizes it. It lies
in O₂(K). Apply this to K = H/O₂(H), which has trivial two-core, using
H = P(L₁T) from ReducedFive. The resulting kernel is trivial. Conjugation
then transfers this fact to Vγ* using the genuine placement
Vγ^h ≤ O₂(L₁T) from 13.8.8(2), for h in H.

Thus faithfulness on P* is a conclusion, not an extra input. The source
placement remains an explicit earlier input; no minimality or solvability
conclusion is smuggled into the action kernel.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.8(2)
and the final five-primary paragraph of 13.8.13, printed pp.949 and 951.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor

private theorem supplement_core_centralizer
    {K : Type*} [Group K] (P J Q : Subgroup K) [P.Normal]
    (hgen : P ⊔ J = ⊤) (hQ : IsPGroup 2 Q)
    (hnQ : J ≤ normalizer (Q : Set K)) :
    Q ⊓ centralizer (P : Set K) ≤ pCore 2 K := by
  let C := Q ⊓ centralizer (P : Set K)
  have hPC : P ≤ normalizer (C : Set K) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (P : Set K) from inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hJC : J ≤ normalizer (C : Set K) :=
    (le_inf hnQ le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have hC : C.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hPC hJC))
  exact le_sSup ⟨hC, hQ.to_le inf_le_left⟩

variable {G : Type*} [Group G] [Finite G]

private theorem hstar_core (H : Subgroup G) : pCore 2 (Source.Hstar H) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := congrArg (map q)
    (q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk)
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at he
  exact he.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))

omit [Finite G] in
private theorem core_normalized (J : Subgroup G) :
    J ≤ normalizer (J.pCoreIn 2 : Set G) := by
  apply le_normalizer_iff.mpr
  rintro j hj x ⟨y, hy, rfl⟩
  exact ⟨⟨j, hj⟩ * y * ⟨j, hj⟩⁻¹,
    (pCore_normal (p := 2) (G := J)).conj_mem y hy ⟨j, hj⟩, rfl⟩

/-- The two-core of the parabolic supplement has trivial starred centralizer of P*. -/
theorem parabolic_core_star_centralizer
    {H L₁ T M Vα : Subgroup G} (r : ReducedFive H L₁ T M Vα) :
    Source.starImage H ((L₁ ⊔ T).pCoreIn 2) ⊓
      centralizer (Source.starImage H r.P : Set (Source.Hstar H)) = ⊥ := by
  let J := L₁ ⊔ T
  have hJ : J ≤ H := r.generated ▸ le_sup_right
  have hQ : J.pCoreIn 2 ≤ H := (pCoreIn_le 2 J).trans hJ
  let := r.Pstar_normal
  have hgen : Source.starImage H r.P ⊔ Source.starImage H J = ⊤ := by
    unfold Source.starImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup r.P_le hJ, ← r.generated,
      subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hn : Source.starImage H J ≤ normalizer (Source.starImage H (J.pCoreIn 2) : Set _) := by
    have hi : J.subgroupOf H ≤ normalizer ((J.pCoreIn 2).subgroupOf H : Set H) := by
      apply le_normalizer_iff.mpr
      intro j hj x hx
      exact le_normalizer_iff.mp (core_normalized J) j hj x hx
    exact (map_mono hi).trans (le_normalizer_map _)
  have hp : IsPGroup 2 (Source.starImage H (J.pCoreIn 2)) :=
    ((isPGroup_pCoreIn 2 J).comap_subtype).map _
  apply bot_unique
  exact (supplement_core_centralizer _ _ _ hgen hp hn).trans_eq (hstar_core H)

/-- The source conjugate-core placement makes the actual Vγ* action on P* faithful. -/
theorem star_faithful_on_P_of_core_placement
    {H L₁ T M Vα Vγ : Subgroup G} (r : ReducedFive H L₁ T M Vα)
    (h : H)
    (hplace : Vγ.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Source.starImage H Vγ ⊓ centralizer (Source.starImage H r.P : Set _) = ⊥ := by
  let := r.Pstar_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  apply bot_unique
  rintro x ⟨hx, hc⟩
  obtain ⟨v, hv, rfl⟩ := hx
  have hconj : q h * q v * (q h)⁻¹ ∈
      Source.starImage H ((L₁ ⊔ T).pCoreIn 2) := by
    refine ⟨h * v * h⁻¹, hplace (mem_map_of_mem _ hv), ?_⟩
    change q (h * v * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hcent : q h * q v * (q h)⁻¹ ∈
      centralizer (Source.starImage H r.P : Set _) :=
    (inferInstance : (centralizer (Source.starImage H r.P : Set (Source.Hstar H))).Normal).conj_mem (q v) hc (q h)
  have he : q h * q v * (q h)⁻¹ = 1 := by
    have hh := show q h * q v * (q h)⁻¹ ∈
        Source.starImage H ((L₁ ⊔ T).pCoreIn 2) ⊓ centralizer (Source.starImage H r.P : Set _)
      from ⟨hconj, hcent⟩
    rwa [parabolic_core_star_centralizer r, mem_bot] at hh
  exact mem_bot.mpr (mul_left_cancel ((mul_inv_eq_one.mp he).trans (mul_one (q h)).symm))

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor
