module

public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.CoreFree
public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Residual

/-!
# The core-free normal-core quotient

For the unique maximal subgroup `B` above a Sylow `2`-subgroup, quotienting by
`B.normalCore` preserves maximality and uniqueness and makes the image of `B`
core-free.  The core-free primitive theorem then provides an elementary
abelian odd-prime complement, identifies it with the quotient's two-residual,
and proves irreducibility under the mapped Sylow subgroup.  The public
predicate below deliberately states irreducibility of `O²(Q/N)`; this is the
source-faithful reading of Stellmacher (3.3)(b), confirmed by the journal
version (Journal of Algebra 190 (1997), pp. 21--22).
-/

namespace Stellmacher.SectionThree

open scoped Pointwise IsMulCommutative

universe u


@[expose] public def IsIrreducibleResidualQuotient
    {Q : Type u} [Group Q] (T N : Subgroup Q) : Prop :=
  ∃ hN : N.Normal,
    let _ : N.Normal := hN
    IsIrreducibleSection
      (T.map (QuotientGroup.mk' N)) ⊥
      (twoResidualAmbient (⊤ : Subgroup (Q ⧸ N)))

public theorem quotientCoreFree_data
    {Q : Type u} [Group Q] [Finite Q]
    (T B : Subgroup Q) (Tₛ : Sylow 2 Q)
    (hT : (Tₛ : Subgroup Q) = T)
    (hB : IsCoatom B) (hTB : T ≤ B)
    (huniq : ∀ M : Subgroup Q, IsCoatom M → T ≤ M → M = B)
    (hsolv : Group.IsSolvable Q) :
    ∃ (p : ℕ) (K : Subgroup (Q ⧸ B.normalCore)),
      p.Prime ∧ Odd p ∧ K.Normal ∧ IsElementaryAbelian p K ∧
      K ⊓ B.map (QuotientGroup.mk' B.normalCore) = ⊥ ∧
      K ⊔ T.map (QuotientGroup.mk' B.normalCore) = ⊤ ∧
      IsIrreducibleResidualQuotient T B.normalCore := by
  classical
  let N : Subgroup Q := B.normalCore
  have hNnormal : N.Normal := inferInstance
  let _ : N.Normal := hNnormal
  let q : Q →* Q ⧸ N := QuotientGroup.mk' N
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  let Tbar : Subgroup (Q ⧸ N) := T.map q
  let Bbar : Subgroup (Q ⧸ N) := B.map q
  have hNleB : N ≤ B := B.normalCore_le
  have hcomapBbar : Bbar.comap q = B := by
    simpa [Bbar, q, N, QuotientGroup.ker_mk', sup_eq_left.2 hNleB] using
      (Subgroup.comap_map_eq q B)
  have hBbar : IsCoatom Bbar := by
    refine ⟨?_, ?_⟩
    · intro htop
      apply hB.ne_top
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
          obtain ⟨y, rfl⟩ := hqsurj x
          have hy : y ∈ M.comap q := hx
          rw [← heq] at hy
          exact Subgroup.mem_map_of_mem q hy
      have hcomap_top : M.comap q = ⊤ := hB.2 (M.comap q) hB_lt_comap
      apply top_unique
      intro x _
      obtain ⟨y, rfl⟩ := hqsurj x
      have hy : y ∈ M.comap q := by rw [hcomap_top]; trivial
      exact hy
  have hTbarBbar : Tbar ≤ Bbar := Subgroup.map_mono hTB
  have huniqbar : ∀ M : Subgroup (Q ⧸ N),
      IsCoatom M → Tbar ≤ M → M = Bbar := by
    intro M hM hTM
    have hMcomap : IsCoatom (M.comap q) :=
      Subgroup.isCoatom_comap_of_surjective hqsurj hM
    have hTcomap : T ≤ M.comap q := by
      intro t ht
      exact hTM (Subgroup.mem_map_of_mem q ht)
    have hEq : M.comap q = B := huniq (M.comap q) hMcomap hTcomap
    rw [← hcomapBbar] at hEq
    exact Subgroup.comap_injective hqsurj hEq
  have hcorebar : Bbar.normalCore = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, rfl⟩ := hqsurj x
      have hycore : y ∈ Bbar.normalCore.comap q := hx
      have hcomapNormal : (Bbar.normalCore.comap q).Normal :=
        (inferInstance : Bbar.normalCore.Normal).comap q
      have hcomap_le_B : Bbar.normalCore.comap q ≤ B := by
        rw [← hcomapBbar]
        exact Subgroup.comap_mono Bbar.normalCore_le
      have hcomap_le_N : Bbar.normalCore.comap q ≤ N := by
        simpa [N] using
          (@Subgroup.normal_le_normalCore Q _ B
            (Bbar.normalCore.comap q) hcomapNormal).mpr hcomap_le_B
      exact (QuotientGroup.eq_one_iff y).2 (hcomap_le_N hycore)
    · exact bot_le
  let Tbarₛ : Sylow 2 (Q ⧸ N) := Tₛ.mapSurjective hqsurj
  have hTbarₛ : (Tbarₛ : Subgroup (Q ⧸ N)) = Tbar := by
    change (Tₛ : Subgroup Q).map q = T.map q
    rw [hT]
  have hsolvbar : Group.IsSolvable (Q ⧸ N) := by infer_instance
  obtain ⟨p, K, hp, hpodd, hKnormal, hKelem, hKinfB,
      hKTtop, hKirred⟩ :=
    coreFree_uniqueSylowMaximal Tbar Bbar Tbarₛ hTbarₛ
      hBbar hTbarBbar huniqbar hcorebar hsolvbar
  have hp2 : p ≠ 2 := by
    intro hp2
    subst p
    rcases hpodd with ⟨k, hk⟩
    omega
  have hKp : IsPGroup p K := by
    let _ : IsElementaryAbelian p K := hKelem
    exact IsElementaryAbelian.isPGroup p K
  have hresK : twoResidualAmbient (⊤ : Subgroup (Q ⧸ N)) = K :=
    twoResidualAmbient_top_eq_of_normal_complement_sylow_two
      hp hp2 K Tbar Tbarₛ hTbarₛ hKnormal hKp hKTtop
  refine ⟨p, K, hp, hpodd, hKnormal, hKelem, hKinfB, hKTtop, hNnormal, ?_⟩
  change IsIrreducibleSection (T.map q) ⊥
    (twoResidualAmbient (⊤ : Subgroup (Q ⧸ N)))
  change IsIrreducibleSection Tbar ⊥
    (twoResidualAmbient (⊤ : Subgroup (Q ⧸ N)))
  rw [hresK]
  refine ⟨bot_le, ?_, ?_⟩
  · intro hbotK
    have hTtop : Tbar = ⊤ := by simpa [← hbotK] using hKTtop
    apply hBbar.ne_top
    exact top_unique (by simpa [hTtop] using hTbarBbar)
  · intro A _ hAK hAinv
    exact hKirred A hAK hAinv

public theorem quotientCoreFree_irreducible
    {Q : Type u} [Group Q] [Finite Q]
    (T B : Subgroup Q) (Tₛ : Sylow 2 Q)
    (hT : (Tₛ : Subgroup Q) = T)
    (hB : IsCoatom B) (hTB : T ≤ B)
    (huniq : ∀ M : Subgroup Q, IsCoatom M → T ≤ M → M = B)
    (hsolv : Group.IsSolvable Q) :
    IsIrreducibleResidualQuotient T B.normalCore := by
  obtain ⟨p, K, hp, hpodd, hKnormal, hKelem, hKinfB, hKTtop, hirred⟩ :=
    quotientCoreFree_data T B Tₛ hT hB hTB huniq hsolv
  exact hirred

end Stellmacher.SectionThree
