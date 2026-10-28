module
public import Theory.GroupAction.SymmetricSixChiefBudget
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer
public import Theory.GroupTheory.CentralizerModulo
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Lifting the S₆ chief-factor budget through an actual quotient

Let H map onto S₆ with a two-group kernel, and let Z ≤ V be normal
subgroups inside that kernel. The centralizer-modulo index on V is exactly
the fixed index on the image of V in H/Z. The projection to S₆ descends
through the same quotient, preserving both its two-group kernel and the
marked even involution in the actor image.

The chief-factor budget and the residual dichotomy then apply in H/Z.
Images of commutators and of the two-residual give their precise preimage
conclusions in H. In particular, taking X = [V,ker(q)] yields the source
alternative before radius centrality. An additional form takes the original
subgroup K with [V ∩ K,A] ≤ Z and index at most eight. Neither V nor V/Z is
assumed elementary abelian, and no quotient-action compatibility is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (5.2)(i), printed p.914.
-/

public section

open Subgroup NoncentralChiefRefinement
namespace NoncentralChiefRefinement.SymmetricSixBudget
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
/-- The modulo centralizer index is exactly the fixed index on the literal quotient image. -/
theorem centralizerModulo_relIndex_eq (V A Z : Subgroup H) [Z.Normal] :
    (centralizerModulo V A Z).relIndex V =
      (centralizer (A.map (QuotientGroup.mk' Z) : Set (H ⧸ Z))).relIndex
        (V.map (QuotientGroup.mk' Z)) := by
  rw [centralizerModulo, inf_relIndex_left, relIndex_comap]

private theorem residual_dichotomy
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : U ≤ q.ker)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 8)
    (X : Subgroup H) [X.Normal] (hXU : X ≤ U) :
    ⁅X, pResidual 2 H⁆ = ⊥ ∨ ⁅U, pResidual 2 H⁆ ≤ X := by
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hU2 : IsPGroup 2 U := hp.of_injective (inclusion hU) (inclusion_injective hU)
  have hs := noncentralCount_le_one_of_le_ker q hq hp U hU A a ha heven haA hindex s
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
theorem residual_dichotomy_modulo
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (hindex : (centralizerModulo V A Z).relIndex V ≤ 8)
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
  have hidxbar : (centralizer (A.map π : Set (H ⧸ Z))).relIndex (V.map π) ≤ 8 := by
    rwa [centralizerModulo_relIndex_eq] at hindex
  have h := residual_dichotomy qbar hqbar hpbar (V.map π) hVbar (A.map π) a ha heven
    (hAbar.symm ▸ haA) hidxbar (X.map π) (map_mono hXV)
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

/-- The original source commutator, with P equal to the actual S₆ kernel. -/
theorem kernel_commutator_residual_dichotomy
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (hindex : (centralizerModulo V A Z).relIndex V ≤ 8) :
    ⁅⁅V, q.ker⁆, pResidual 2 H⁆ ≤ Z ∨ ⁅V, pResidual 2 H⁆ ≤ ⁅V, q.ker⁆ ⊔ Z := by
  exact residual_dichotomy_modulo q hq hp V Z hZV hV A a ha heven haA hindex
    ⁅V, q.ker⁆ (commutator_le_left V q.ker)

/-- A specified index subgroup whose commutators lie in Z bounds the actual
centralizer-modulo index. No normality of K is required. -/
theorem centralizerModulo_relIndex_le_of_commutator (V A Z K : Subgroup H) [Z.Normal]
    (hc : ⁅V ⊓ K, A⁆ ≤ Z) :
    (centralizerModulo V A Z).relIndex V ≤ K.relIndex V := by
  have hle : V ⊓ K ≤ centralizerModulo V A Z := by
    intro x hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hx.1, fun a ha => ?_⟩
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator ha hx)
  have hidx := relIndex_le_of_le_left hle
    (Subgroup.FiniteIndex.index_ne_zero (H := (V ⊓ K).subgroupOf V))
  simpa only [inf_relIndex_left] using hidx

/-- The source form retaining the original subgroup K and its commutator
centralization modulo Z, rather than a quotient-action compatibility premise. -/
theorem kernel_commutator_residual_dichotomy_of_index
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (K : Subgroup H) (hc : ⁅V ⊓ K, A⁆ ≤ Z) (hindex : K.relIndex V ≤ 8) :
    ⁅⁅V, q.ker⁆, pResidual 2 H⁆ ≤ Z ∨ ⁅V, pResidual 2 H⁆ ≤ ⁅V, q.ker⁆ ⊔ Z :=
  kernel_commutator_residual_dichotomy q hq hp V Z hZV hV A a ha heven haA
    ((centralizerModulo_relIndex_le_of_commutator V A Z K hc).trans hindex)
end NoncentralChiefRefinement.SymmetricSixBudget
