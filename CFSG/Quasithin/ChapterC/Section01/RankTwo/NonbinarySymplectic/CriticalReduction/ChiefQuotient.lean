module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ChiefBudget
public import Theory.GroupAction.SymmetricSixChiefBudget.Quotient

/-!
# The symplectic chief budget on an actual seed quotient

The ambient symplectic projection descends through a normal seed inside
its two-kernel. The literal actor image and its order are unchanged, and
the centralizer-modulo index becomes the fixed index in the quotient.
The chief-factor budget yields at most one noncentral factor. Refinement
through any normal subgroup then gives the residual fixed-or-covering
alternative, transported back through the same quotient map.

`RadiusChief` uses these results on the complete radius and starting seed
of the characteristic replacement. Neither is replaced by a moving layer.
Source: Meierfrankenfeld--Stellmacher (1993), (5.2)(i), printed p.914.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement NoncentralChiefRefinement.SymmetricSixBudget
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H G F : Type*} [Group H] [Finite H] [Group G] [Finite G]
  [IsSimpleGroup G] [IsQuasisimple G] [Field F] [Finite F]

private theorem symplectic_residual_dichotomy
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hG : Nat.card G = Nat.card (Sp F))
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (q : H →* G) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : U ≤ q.ker)
    (A : Subgroup H) [IsElementaryAbelian 2 (A.map q)]
    (hlarge : Nat.card F^2 ≤ Nat.card (A.map q))
    (hindex : (centralizer (A : Set H)).relIndex U ≤ Nat.card F^3)
    (X : Subgroup H) [X.Normal] (hXU : X ≤ U) :
    ⁅X, pResidual 2 H⁆ = ⊥ ∨ ⁅U, pResidual 2 H⁆ ≤ X := by
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hU2 : IsPGroup 2 U := hp.of_injective (inclusion hU) (inclusion_injective hU)
  have hs := symplectic_noncentralCount_le_one hF hn hG hsq q hq hp U hU2 A hlarge hindex s
  by_cases hz : s.noncentralCount = 0
  · right
    have hlast : IsPGroup 2 s.series.last.val := by
      rw [s.last_eq]
      exact hU2
    have h := s.series.residual_commutator_le_head_of_central_steps
      hlast (s.noncentralCount_eq_zero_iff.mp hz)
    rw [s.last_eq, s.head_eq] at h
    change ⁅U, pResidual 2 H⁆ ≤ ⊥ at h
    exact h.trans bot_le
  · exact s.residual_dichotomy_of_count_one hU2 (by omega) X hXU

/-- Every normal subgroup of V either centralizes the residual modulo Z or
contains the whole residual movement modulo Z. The two-group V/Z is not
assumed abelian. -/
theorem symplectic_residual_dichotomy_modulo
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hG : Nat.card G = Nat.card (Sp F))
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (q : H →* G) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) [IsElementaryAbelian 2 (A.map q)]
    (hlarge : Nat.card F^2 ≤ Nat.card (A.map q))
    (hindex : (centralizerModulo V A Z).relIndex V ≤ Nat.card F^3)
    (X : Subgroup H) [X.Normal] (hXV : X ≤ V) :
    ⁅X, pResidual 2 H⁆ ≤ Z ∨ ⁅V, pResidual 2 H⁆ ≤ X ⊔ Z := by
  let π := QuotientGroup.mk' Z
  let qbar := QuotientGroup.lift Z q (hZV.trans hV)
  have hqbar : Function.Surjective qbar :=
    QuotientGroup.lift_surjective_of_surjective Z q hq _
  have hker : qbar.ker = q.ker.map π := QuotientGroup.ker_lift Z q _
  have hpbar : IsPGroup 2 qbar.ker := by rw [hker]; exact hp.map π
  let : (V.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  let : (X.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  have hVbar : V.map π ≤ qbar.ker := by rw [hker]; exact map_mono hV
  have hAbar : (A.map π).map qbar = A.map q := by
    rw [map_map]
    rfl
  have hidxbar : (centralizer (A.map π : Set (H ⧸ Z))).relIndex (V.map π) ≤ Nat.card F^3 := by
    rwa [centralizerModulo_relIndex_eq] at hindex
  let : IsElementaryAbelian 2 ((A.map π).map qbar) := hAbar.symm ▸ inferInstance
  have h := symplectic_residual_dichotomy hF hn hG hsq qbar hqbar hpbar
    (V.map π) hVbar (A.map π) (hAbar.symm ▸ hlarge) hidxbar (X.map π) (map_mono hXV)
  have hres : (pResidual 2 H).map π = pResidual 2 (H ⧸ Z) := map_pResidual_quotient 2 Z
  rcases h with h | h
  · left
    have hm : (⁅X, pResidual 2 H⁆).map π ≤ ⊥ := by
      rw [map_commutator, hres, h]
    have hk := (map_le_iff_le_comap).mp hm
    simpa only [MonoidHom.comap_bot, π, QuotientGroup.ker_mk'] using hk
  · right
    have hm : (⁅V, pResidual 2 H⁆).map π ≤ X.map π := by
      rwa [map_commutator, hres]
    have hk := (map_le_iff_le_comap).mp hm
    simpa only [comap_map_eq, π, QuotientGroup.ker_mk'] using hk

/-- The q³ budget on the literal quotient by the full seed. -/
theorem symplectic_noncentralCount_le_one_modulo
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hG : Nat.card G = Nat.card (Sp F))
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (q : H →* G) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) [IsElementaryAbelian 2 (A.map q)]
    (hlarge : Nat.card F^2 ≤ Nat.card (A.map q))
    (hindex : (centralizerModulo V A Z).relIndex V ≤ Nat.card F^3)
    (s :
      letI : (V.map (QuotientGroup.mk' Z)).Normal :=
        Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
      SeriesOn (V.map (QuotientGroup.mk' Z))) : s.noncentralCount ≤ 1 := by
  let π := QuotientGroup.mk' Z
  let qbar := QuotientGroup.lift Z q (hZV.trans hV)
  have hqbar : Function.Surjective qbar :=
    QuotientGroup.lift_surjective_of_surjective Z q hq _
  have hker : qbar.ker = q.ker.map π := QuotientGroup.ker_lift Z q _
  have hpbar : IsPGroup 2 qbar.ker := by rw [hker]; exact hp.map π
  let : (V.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  have hVbar : V.map π ≤ qbar.ker := by rw [hker]; exact map_mono hV
  have hAbar : (A.map π).map qbar = A.map q := by
    rw [map_map]
    rfl
  have hidxbar : (centralizer (A.map π : Set (H ⧸ Z))).relIndex (V.map π) ≤ Nat.card F^3 := by
    rwa [centralizerModulo_relIndex_eq] at hindex
  let : IsElementaryAbelian 2 ((A.map π).map qbar) := hAbar.symm ▸ inferInstance
  exact symplectic_noncentralCount_le_one hF hn hG hsq qbar hqbar hpbar
    (V.map π) (hpbar.to_le hVbar) (A.map π) (hAbar.symm ▸ hlarge) hidxbar s


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
