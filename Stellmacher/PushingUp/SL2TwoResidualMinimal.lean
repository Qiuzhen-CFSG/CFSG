module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.TwoResidualSylowSupplement

/-!
# Minimality of the two-residual in `SL₂(2)`

If a finite group is isomorphic to `SL₂(2)`, its two-residual is the normal
subgroup of order three and is therefore a minimal nontrivial normal subgroup.
This supplies the residual-minimality hypothesis inherited from standing
condition (A) in Stellmacher, *Pushing up*, Arch. Math. 46 (1986), Lemma (1.4),
specialized to `p = 2` and `n = 1`.

The proof identifies `SL₂(2)` with the permutation group on three letters and
pulls back its alternating subgroup. The defining intersection for the
two-residual lies in this normal subgroup of index two. The residual--Sylow
supplement theorem rules out a trivial residual, since a Sylow 2-subgroup has
order two while the ambient group has order six. Thus the residual equals the
alternating subgroup of prime order three, whose only subgroups are trivial and
the whole subgroup. The normality field is retained in the exact
`IsMinimalNormalOver ⊥ ⊤` form needed by the pushing-up argument.
-/

namespace Stellmacher.PushingUp

universe u

private theorem alternatingComap_data
    {G : Type u} [Group G] [Finite G]
    (e : G ≃* Equiv.Perm (Fin 3)) :
    let A := (alternatingGroup (Fin 3)).comap e.toMonoidHom
    A.Normal ∧ A.index = 2 ∧ Nat.card A = 3 := by
  let A : Subgroup G := (alternatingGroup (Fin 3)).comap e.toMonoidHom
  have hAnormal : A.Normal := by
    dsimp only [A]
    exact (inferInstance : (alternatingGroup (Fin 3)).Normal).comap e.toMonoidHom
  let _ : A.Normal := hAnormal
  have hAindex : A.index = 2 := by
    dsimp only [A]
    rw [Subgroup.index_comap_of_surjective _ e.surjective,
      alternatingGroup.index_eq_two]
  have hGcard : Nat.card G = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    norm_num
  have hAcard : Nat.card A = 3 := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup A
    have hqcard : Nat.card (G ⧸ A) = 2 := by
      rw [← Subgroup.index_eq_card A, hAindex]
    rw [hGcard, hqcard] at hmul
    omega
  exact ⟨hAnormal, hAindex, hAcard⟩

private theorem twoResidualAmbient_top_le_alternatingComap
    {G : Type u} [Group G] [Finite G]
    (e : G ≃* Equiv.Perm (Fin 3)) :
    twoResidualAmbient (⊤ : Subgroup G) ≤
      (alternatingGroup (Fin 3)).comap e.toMonoidHom := by
  classical
  let A : Subgroup G := (alternatingGroup (Fin 3)).comap e.toMonoidHom
  have hA := alternatingComap_data e
  let ATop : Subgroup (⊤ : Subgroup G) := A.subgroupOf ⊤
  have hATopNormal : ATop.Normal := hA.1.subgroupOf ⊤
  have hATopIndex : ATop.index = 2 ^ 1 := by
    calc
      ATop.index = A.relIndex ⊤ := rfl
      _ = A.index := Subgroup.relIndex_top_right A
      _ = 2 := hA.2.1
      _ = 2 ^ 1 := by norm_num
  have hATop_mem : ATop ∈
      {N : Subgroup (⊤ : Subgroup G) |
        N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n} :=
    ⟨hATopNormal, 1, hATopIndex⟩
  have hsInf : twoResidualSubgroup (⊤ : Subgroup G) ≤ ATop :=
    sInf_le hATop_mem
  calc
    twoResidualAmbient (⊤ : Subgroup G) =
        (twoResidualSubgroup (⊤ : Subgroup G)).map
          (⊤ : Subgroup G).subtype := rfl
    _ ≤ ATop.map (⊤ : Subgroup G).subtype := Subgroup.map_mono hsInf
    _ = A := Subgroup.map_subgroupOf_eq_of_le le_top
    _ = (alternatingGroup (Fin 3)).comap e.toMonoidHom := rfl

private theorem sylow_card_two_of_isSL2Two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hG : IsSL2Two G) :
    Nat.card S = 2 := by
  have hGcard : Nat.card G = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hG
  rw [S.card_eq_multiplicity, hGcard]
  have hf6 : Nat.factorization 6 2 = 1 := by
    change Nat.factorization (3 * 2) 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  simp [hf6]

private theorem twoResidualAmbient_top_eq_alternatingComap
    {G : Type u} [Group G] [Finite G]
    (hG : IsSL2Two G) (e : G ≃* Equiv.Perm (Fin 3)) :
    twoResidualAmbient (⊤ : Subgroup G) =
      (alternatingGroup (Fin 3)).comap e.toMonoidHom := by
  classical
  let R : Subgroup G := twoResidualAmbient (⊤ : Subgroup G)
  let A : Subgroup G := (alternatingGroup (Fin 3)).comap e.toMonoidHom
  have hA := alternatingComap_data e
  have hRA : R ≤ A := by
    simpa [R, A] using twoResidualAmbient_top_le_alternatingComap e
  have hRne : R ≠ ⊥ := by
    intro hRbot
    let S : Sylow 2 G := default
    have hsup : R ⊔ (S : Subgroup G) = ⊤ := by
      simpa [R] using twoResidualAmbient_top_sup_sylow S
    have hStop : (S : Subgroup G) = ⊤ := by
      simpa [hRbot] using hsup
    have hScard : Nat.card S = 2 := sylow_card_two_of_isSL2Two S hG
    have hGcard : Nat.card G = 6 :=
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hG
    have hcard := congrArg (fun H : Subgroup G => Nat.card H) hStop
    rw [Subgroup.card_top, hGcard, hScard] at hcard
    omega
  let RA : Subgroup A := R.subgroupOf A
  let hprimeA : Fact (Nat.Prime (Nat.card A)) :=
    ⟨by rw [hA.2.2]; exact Nat.prime_three⟩
  let _ : Fact (Nat.Prime (Nat.card A)) := hprimeA
  rcases RA.eq_bot_or_eq_top_of_prime_card with hRAbot | hRAtop
  · have hmap : RA.map A.subtype = R :=
      Subgroup.map_subgroupOf_eq_of_le hRA
    have hRbot : R = ⊥ := by
      rw [hRAbot, Subgroup.map_bot] at hmap
      exact hmap.symm
    exact False.elim (hRne hRbot)
  · have hmap : RA.map A.subtype = R :=
      Subgroup.map_subgroupOf_eq_of_le hRA
    have hAR : A = R := by
      rw [hRAtop] at hmap
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hAR.symm

/-- In a finite group of type `SL₂(2)`, the two-residual is a minimal
nontrivial normal subgroup. -/
public theorem sl2Two_twoResidual_isMinimalNormal
    {G : Type u} [Group G] [Finite G] (hG : IsSL2Two G) :
    SectionThree.IsMinimalNormalOver
      (⊥ : Subgroup G) (⊤ : Subgroup G)
      (twoResidualAmbient (⊤ : Subgroup G)) := by
  classical
  have hG' := hG
  obtain ⟨eSL⟩ := hG
  obtain ⟨eS⟩ := SectionOne.sl2Two_equiv_perm_three
  let e : G ≃* Equiv.Perm (Fin 3) := eSL.trans eS
  let R : Subgroup G := twoResidualAmbient (⊤ : Subgroup G)
  let A : Subgroup G := (alternatingGroup (Fin 3)).comap e.toMonoidHom
  have hA := alternatingComap_data e
  have hRA : R = A := by
    simpa [R, A] using twoResidualAmbient_top_eq_alternatingComap hG' e
  have hRne : R ≠ ⊥ := by
    rw [hRA]
    exact (Subgroup.one_lt_card_iff_ne_bot A).mp (by rw [hA.2.2]; omega)
  have hRnormal : R.Normal := by
    rw [hRA]
    exact hA.1
  refine ⟨bot_le, le_top, hRne, hRnormal.subgroupOf ⊤, ?_⟩
  intro K _hbotK _hKtop _hKnormal hKR
  let KR : Subgroup R := K.subgroupOf R
  have hRcard : Nat.card R = 3 := by rw [hRA, hA.2.2]
  let hprimeR : Fact (Nat.Prime (Nat.card R)) :=
    ⟨by rw [hRcard]; exact Nat.prime_three⟩
  let _ : Fact (Nat.Prime (Nat.card R)) := hprimeR
  have hmap : KR.map R.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKR
  rcases KR.eq_bot_or_eq_top_of_prime_card with hKRbot | hKRtop
  · left
    rw [hKRbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  · right
    change K = R
    rw [hKRtop] at hmap
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hmap.symm

end Stellmacher.PushingUp
