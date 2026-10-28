module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Lifting the exceptional central factors

For C two-perfect and normalized by O₂(H), the embedded two-residual of
CO₂(H) is C. Centralization of C* by K* makes K normalize CO₂(H), and
characteristicity of that residual makes K normalize C. The source
normalizer bound for L₀ then contradicts K ≰ M.

All normalization is relative to H until the last ambient normalizer
comparison. Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.20 on printed p.955, and the analogous lifting in 13.7.5(7), p.938.
The hypotheses identifying the actual central factor remain explicit.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Lifting
variable {G : Type*} [Group G]

private theorem normalizes_twoPerfect (Q K C : Subgroup G) [Q.Normal]
    (hQ : IsPGroup 2 Q) (hC : IsPPerfect 2 C)
    (hQC : Q ≤ normalizer (C : Set G)) (hKC : ⁅C, K⁆ ≤ Q) :
    K ≤ normalizer (C : Set G) := by
  have hres := embedded_pResidual_join_pGroup C Q hC hQ hQC
  have hchar := normalizer_le_normalizer_characteristic_image (C ⊔ Q) (pResidual 2 (C ⊔ Q : Subgroup G))
  rw [hres] at hchar
  exact (le_normalizer_sup_of_commutator_le C K C Q le_rfl hKC).trans hchar

open CFSG.Quasithin.Chapter13.Section08
/-- Lift centralization modulo O₂(H) to normalization of a two-perfect marked subgroup. -/
public theorem normalizes_of_star_centralizing (H K C : Subgroup G) (hKH : K ≤ H) (hCH : C ≤ H)
    (hC : IsPPerfect 2 C) (hQC : Source.QH H ≤ normalizer (C : Set G))
    (hstar : Source.starImage H K ≤ centralizer (Source.starImage H C : Set (Source.Hstar H))) :
    K ≤ normalizer (C : Set G) := by
  have hC' : IsPPerfect 2 (C.subgroupOf H) :=
    hC.of_surjective (subgroupOfEquivOfLe hCH).symm.toMonoidHom
      (subgroupOfEquivOfLe hCH).symm.surjective
  have hQC' : pCore 2 H ≤ normalizer (C.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hCH]
    intro x hx
    exact hQC (mem_map.mpr ⟨x, hx, rfl⟩)
  have hcomm : ⁅C.subgroupOf H, K.subgroupOf H⁆ ≤ pCore 2 H := by
    rw [← QuotientGroup.ker_mk' (pCore 2 H), ← Subgroup.map_eq_bot_iff, map_commutator,
      commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hstar
  have hn := normalizes_twoPerfect (pCore 2 H) (K.subgroupOf H) (C.subgroupOf H)
    (pCore_isPGroup (p := 2) (G := H)) hC' hQC' hcomm
  apply le_normalizer_iff.mpr
  intro k hk c hc
  exact le_normalizer_iff.mp hn ⟨k, hKH hk⟩ hk ⟨c, hCH hc⟩ hc
/-- The L₀ central-factor case contradicts the source bound N_G(L₀) ≤ M.
The equality N_G(L₀) = M is not required. -/
public theorem central_factor_exclusion (H K C M : Subgroup G)
    (hKH : K ≤ H) (hCH : C ≤ H) (hKM : ¬ K ≤ M)
    (hC : IsPPerfect 2 C) (hQC : Source.QH H ≤ normalizer (C : Set G))
    (hNM : normalizer (C : Set G) ≤ M)
    (hstar : Source.starImage H K ≤ centralizer (Source.starImage H C : Set (Source.Hstar H))) :
    False :=
  hKM ((normalizes_of_star_centralizing H K C hKH hCH hC hQC hstar).trans hNM)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Lifting
