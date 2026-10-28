module
public import Stellmacher.SectionTen.TenOneCommonIntersection
public import Stellmacher.SectionNine.CubicLocalAction

/-!
# Cubic-neighborhood order bounds in the large branch of (10.1)

For the actual Section Ten context, the source-(14) cardinalities
|Vfirst|=32 and |Vfirst ∩ Vend|=8 force the generated middle neighborhood
U to have order between 128 and 512, divisible by 128. The exact order and
quotient conclusions later in the source are not used as hypotheses.

The opening SL₂(2) action has exactly three neighbors. Conjugacy transports
the first-module order to each neighbor, and the common-intersection theorem
identifies every distinct pair intersection with I. The unconditional derived
bound U'≤I makes all required subgroup products into joins. One pair has
order128; a second product count bounds the full threefold join by512.

This is the geometric cardinal input to the large-branch quotient calculations
following (16)–(19), Stellmacher, Journal of Algebra 190 (1997), printed
pp.63–65 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_neighborhood_card_bounds
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hmodule : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 32)
    (hintersection : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8) :
    128 ≤ Nat.card (GeneratedNeighborhoodV ctx.Γ middle) ∧
      Nat.card (GeneratedNeighborhoodV ctx.Γ middle) ≤ 512 ∧
      128 ∣ Nat.card (GeneratedNeighborhoodV ctx.Γ middle) := by
  classical
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let I := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a'
  have hopen := sectionTenOpeningData ctx middle hpath
  let : Finite ctx.Γ.Vertex := ctx.Γ.finiteVertex
  let : Fintype {neighbor // ctx.Γ.adjacent middle neighbor} := Fintype.ofFinite _
  have hdegree : Fintype.card {neighbor // ctx.Γ.adjacent middle neighbor} = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
      hopen.quotient_model).degree
  let e : Fin 3 ≃ {neighbor // ctx.Γ.adjacent middle neighbor} :=
    (Fintype.equivFinOfCardEq hdegree).symm
  let vertex (i : Fin 3) := (e i).val
  let V (i : Fin 3) : Subgroup G := VAt ctx.Γ (vertex i)
  have hadj (i : Fin 3) : ctx.Γ.adjacent middle (vertex i) := (e i).property
  have hVU (i : Fin 3) : V i ≤ U :=
    le_sSup ⟨vertex i, (mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj i), rfl⟩
  have hcardV (i : Fin 3) : Nat.card (V i) = 32 := by
    obtain ⟨actor, hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (sectionTenOpeningGeometry ctx middle hpath).2.1)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj i))
    change Nat.card (VAt ctx.Γ (vertex i)) = 32
    rw [← hmove, VAt, v_act]
    exact (Subgroup.card_map_of_injective (MulAut.conj (actor : G)⁻¹).injective).trans
      hmodule
  have hcommon (i j : Fin 3) (hne : i ≠ j) : V i ⊓ V j = I :=
    ten_one_neighbor_intersection ctx middle hpath (hadj i) (hadj j)
      (fun heq => hne (e.injective (Subtype.ext heq)))
  have hIV (i : Fin 3) : I ≤ V i := by
    rw [← hcommon i (if i = 0 then 1 else 0) (by split_ifs <;> omega)]
    exact inf_le_left
  have hU : U = V 0 ⊔ V 1 ⊔ V 2 := by
    apply le_antisymm
    · apply sSup_le
      rintro subgroup ⟨neighbor, hneighbor, rfl⟩
      obtain ⟨i, hi⟩ := e.surjective
        (⟨neighbor, (mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor⟩ :
          {n // ctx.Γ.adjacent middle n})
      have heq : neighbor = vertex i := congrArg Subtype.val hi.symm
      rw [heq]
      fin_cases i
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · exact sup_le (sup_le (hVU 0) (hVU 1)) (hVU 2)
  have hcomm : ⁅U, U⁆ ≤ I := by
    rw [← Subgroup.map_subtype_commutator U]
    exact ten_one_generated_derived_le_intersection ctx middle hpath
  have hnormalize : V 1 ≤ Subgroup.normalizer (V 0 : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono (hVU 0) (hVU 1)).trans (hcomm.trans (hIV 0)))
  have hpair : Nat.card (V 0 ⊔ V 1 : Subgroup G) = 128 := by
    have hh := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
      (V 0) (V 1) hnormalize
    rw [hcardV 0, hcardV 1, hcommon 0 1 (by decide)] at hh
    change 32 * 32 = Nat.card I * Nat.card (V 0 ⊔ V 1 : Subgroup G) at hh
    rw [show Nat.card I = 8 from hintersection] at hh
    omega
  have hpairU : V 0 ⊔ V 1 ≤ U := sup_le (hVU 0) (hVU 1)
  have hlower : 128 ≤ Nat.card U := by
    rw [← hpair]
    exact Subgroup.card_le_of_le hpairU
  have hdvd : 128 ∣ Nat.card U := by
    rw [← hpair]
    exact Subgroup.card_dvd_of_le hpairU
  have hnormalizePair : V 2 ≤ Subgroup.normalizer ((V 0 ⊔ V 1 : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hpairU (hVU 2)).trans
        (hcomm.trans ((hIV 0).trans le_sup_left)))
  have hintersectionLower : 8 ≤ Nat.card ((V 0 ⊔ V 1) ⊓ V 2 : Subgroup G) := by
    rw [← hintersection]
    exact Subgroup.card_le_of_le (le_inf ((hIV 0).trans le_sup_left) (hIV 2))
  have hcount := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (V 0 ⊔ V 1) (V 2) hnormalizePair
  rw [hpair, hcardV 2, ← hU] at hcount
  have hupper : Nat.card U ≤ 512 := by nlinarith
  exact ⟨hlower, hupper, hdvd⟩

end Stellmacher.SectionTen

