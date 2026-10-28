module

public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal

/-!
# Stellmacher (3.3): solvable local structure

Let `P` be a member of `℘(S)`, let `B` be its unique maximal subgroup
containing `S`, and let `P₀` be the largest normal subgroup of `P` contained
in `B`.  For solvable `P`, the two-residual of `P/O₂(P)` is an odd-prime
group, `O²(P/P₀)` is irreducible under the image of `S`, and
`P₀/O₂(P)` is the Frattini subgroup of that first two-residual.

The proof first identifies `P₀` with `B.normalCore` and shows
`O₂(P) ≤ P₀`.  The solvable primitive two-local theorem is applied to
`P/O₂(P)` for parts (a) and (c).  Part (b) is obtained directly by applying
the core-free quotient result to `P/P₀`.

The quotient formulation of part (b) follows the journal version,
Journal of Algebra 190 (1997), pp. 21--22.  The earlier repository LaTeX
transcription wrote the generally false expression `O²(P)/P₀`; that
transcription has been repaired to match the scan.
-/

namespace Stellmacher.SectionThree

universe u

public structure LemmaThreeThreeConclusion
    {G : Type u} [Group G] [Finite G]
    (S P : Subgroup G) (P₀ B : Subgroup P) : Prop where
  part_a :
    ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧
      IsPGroup p
        (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)))
  part_b :
    IsIrreducibleResidualQuotient (S.subgroupOf P) P₀
  part_c :
    P₀.map (QuotientGroup.mk' (pCore 2 P)) =
      frattiniAmbient
        (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)))

private theorem twoCore_le_Pzero
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (B P₀ : Subgroup P)
    (hB : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B)
    (hP₀ : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ P₀) :
    pCore 2 P ≤ P₀ := by
  rcases hP.1.2.1 with ⟨T, hT⟩
  have hcore_le_T : pCore 2 P ≤ (T : Subgroup P) :=
    IsPGroup.le_sylow_of_normal (pCore_isPGroup (p := 2) (G := P)) T
  apply hP₀.2.2 (pCore 2 P) inferInstance
  intro x hx
  apply hB.2.1
  change ((x : P) : G) ∈ S
  rw [← hT]
  exact ⟨x, hcore_le_T hx, rfl⟩

private theorem Pzero_eq_normalCore
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) (B P₀ : Subgroup P)
    (hP₀ : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ P₀) :
    P₀ = B.normalCore := by
  let _ : P₀.Normal := hP₀.2.1
  apply le_antisymm
  · exact Subgroup.normal_le_normalCore.mpr hP₀.1
  · exact hP₀.2.2 B.normalCore inferInstance B.normalCore_le

/-! **Stellmacher (3.3).**  `B` is represented as a subgroup of the local
group `P`; the maximality and the definition of `P₀` are explicit. -/
public theorem lemma_three_three
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (B P₀ : Subgroup P)
    (hB : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B)
    (hP₀ : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ P₀)
    (hsolv : Group.IsSolvable P) :
    LemmaThreeThreeConclusion S P P₀ B := by
  rcases h with ⟨_heven, _hnontrivial⟩
  classical
  obtain ⟨T, hTmap⟩ := hP.1.2.1
  let TP : Subgroup P := S.subgroupOf P
  have hT : (T : Subgroup P) = TP := by
    apply le_antisymm
    · intro t ht
      change ((t : P) : G) ∈ S
      rw [← hTmap]
      exact ⟨t, ht, rfl⟩
    · intro x hx
      change ((x : P) : G) ∈ S at hx
      rw [← hTmap] at hx
      obtain ⟨t, ht, htx⟩ := hx
      have : t = x := P.subtype_injective htx
      subst x
      exact ht
  have hO_le_P₀ : pCore 2 P ≤ P₀ :=
    twoCore_le_Pzero S P hP B P₀ hB hP₀
  have hP₀core : P₀ = B.normalCore := Pzero_eq_normalCore P B P₀ hP₀
  have hirred : IsIrreducibleResidualQuotient TP P₀ := by
    rw [hP₀core]
    exact quotientCoreFree_irreducible TP B T hT hB.1 hB.2.1 hB.2.2 hsolv
  let O : Subgroup P := pCore 2 P
  have hOnormal : O.Normal := inferInstance
  let _ : O.Normal := hOnormal
  let q : P →* P ⧸ O := QuotientGroup.mk' O
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective O
  let Tbar : Subgroup (P ⧸ O) := TP.map q
  let Bbar : Subgroup (P ⧸ O) := B.map q
  have hO_le_B : O ≤ B := hO_le_P₀.trans hP₀.1
  have hcomapBbar : Bbar.comap q = B := by
    simpa [Bbar, q, QuotientGroup.ker_mk', sup_eq_left.2 hO_le_B] using
      (Subgroup.comap_map_eq q B)
  have hBbar : IsCoatom Bbar := by
    refine ⟨?_, ?_⟩
    · intro htop
      apply hB.1.ne_top
      apply top_unique
      rw [← hcomapBbar, htop]
      simp
    · intro M hBM
      have hB_lt_comap : B < M.comap q := by
        refine lt_of_le_of_ne ?_ ?_
        · intro x hx
          exact hBM.le (Subgroup.mem_map_of_mem q hx)
        · intro heq
          apply hBM.ne
          apply le_antisymm hBM.le
          intro x hx
          obtain ⟨y, rfl⟩ := hq x
          have hy : y ∈ M.comap q := hx
          rw [← heq] at hy
          exact Subgroup.mem_map_of_mem q hy
      have hcomap_top : M.comap q = ⊤ := hB.1.2 (M.comap q) hB_lt_comap
      apply top_unique
      intro x _
      obtain ⟨y, rfl⟩ := hq x
      have hy : y ∈ M.comap q := by rw [hcomap_top]; trivial
      exact hy
  have hTbarBbar : Tbar ≤ Bbar := Subgroup.map_mono hB.2.1
  have huniqbar : ∀ M : Subgroup (P ⧸ O),
      IsCoatom M → Tbar ≤ M → M = Bbar := by
    intro M hM hTM
    have hMcomap : IsCoatom (M.comap q) :=
      Subgroup.isCoatom_comap_of_surjective hq hM
    have hTPcomap : TP ≤ M.comap q := by
      intro t ht
      exact hTM (Subgroup.mem_map_of_mem q ht)
    have hEq : M.comap q = B := hB.2.2 (M.comap q) hMcomap hTPcomap
    rw [← hcomapBbar] at hEq
    exact Subgroup.comap_injective hq hEq
  let Tbarₛ : Sylow 2 (P ⧸ O) := T.mapSurjective hq
  have hTbarₛ : (Tbarₛ : Subgroup (P ⧸ O)) = Tbar := by
    change (T : Subgroup P).map q = TP.map q
    rw [hT]
  have hcorebar : pCore 2 (P ⧸ O) = ⊥ := by
    have hmap := pCore_map_mk'_eq_of_normal_isPGroup
      (G := P) (p := 2) O (pCore_isPGroup (G := P) (p := 2))
    have hmapbot : (pCore 2 P).map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (f := q) (H := pCore 2 P)).2
      simp [q, O, QuotientGroup.ker_mk']
    dsimp [q] at hmapbot
    exact hmap.symm.trans hmapbot
  have hsolvbar : Group.IsSolvable (P ⧸ O) := by infer_instance
  obtain ⟨p, hp, hpodd, hresp, hcorePhi, _hirredbar⟩ :=
    solvable_primitive_two_local Tbar Bbar Tbarₛ hTbarₛ hBbar
      hTbarBbar huniqbar hcorebar hsolvbar
  have hP₀barNormal : (P₀.map q).Normal :=
    hP₀.2.1.map q hq
  have hP₀bar_le_Bbar : P₀.map q ≤ Bbar :=
    Subgroup.map_mono hP₀.1
  have hP₀bar_le_core : P₀.map q ≤ Bbar.normalCore :=
    @Subgroup.normal_le_normalCore (P ⧸ O) _ Bbar (P₀.map q)
      hP₀barNormal |>.mpr hP₀bar_le_Bbar
  have hcore_le_P₀bar : Bbar.normalCore ≤ P₀.map q := by
    have hcomapNormal : (Bbar.normalCore.comap q).Normal :=
      (inferInstance : Bbar.normalCore.Normal).comap q
    have hcomap_le_B : Bbar.normalCore.comap q ≤ B := by
      rw [← hcomapBbar]
      exact Subgroup.comap_mono Bbar.normalCore_le
    have hcomap_le_P₀ : Bbar.normalCore.comap q ≤ P₀ :=
      hP₀.2.2 (Bbar.normalCore.comap q) hcomapNormal hcomap_le_B
    intro x hx
    obtain ⟨y, rfl⟩ := hq x
    exact Subgroup.mem_map_of_mem q (hcomap_le_P₀ hx)
  have hP₀barCore : P₀.map q = Bbar.normalCore :=
    le_antisymm hP₀bar_le_core hcore_le_P₀bar
  refine ⟨⟨p, hp, hpodd, hresp⟩, ?_, ?_⟩
  · exact hirred
  · rw [hP₀barCore]
    exact hcorePhi

end Stellmacher.SectionThree
