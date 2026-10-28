module

public import Stellmacher.SectionOne.RankOneLocalSL2Coordinate

/-!
# Full fixed index for local `SL₂(2)` coordinates

This module upgrades the factor-coordinate conclusion of
`RankOneLocalSL2Coordinate` from the odd-core commutator module to the full
module.  If the local Sylow subgroup has `m(P) = 1`, the fixed part of the
coprime odd-core decomposition is fixed pointwise by `P`: the full fixed
index and the commutator-module fixed index have the same value, so their
complementary cardinal factors cancel.  Each factor coordinate therefore has
full-module fixed index two.

This is the precise fixed-point input used when the recursive quotient in
Stellmacher (1.6) is lifted back to the ambient group.  Source:
`refs/latex/stellmacher-n-group.tex`, journal page 18, the assertion
`|V_A/C_{V_A}(A_i)| = 2`.
-/

@[expose] public section

open scoped Pointwise

namespace Stellmacher.SectionOne

universe u

private theorem fixedPoints_isInvariant_of_normal
    {H V : Type*} [Group H] [Group V] [MulDistribMulAction H V]
    (A : Subgroup H) [A.Normal] :
    IsInvariant H V (FixedPoints.subgroup A V) := by
  refine ⟨?_⟩
  intro h v
  constructor
  · intro hv
    rw [FixedPoints.mem_subgroup]
    intro a
    have hconj : h⁻¹ * (a : H) * h ∈ A := by
      simpa using (inferInstance : A.Normal).conj_mem (a : H) a.property h⁻¹
    have hfix := (FixedPoints.mem_subgroup (M := A) (a := v)).1 hv
      ⟨h⁻¹ * (a : H) * h, hconj⟩
    have hfix' : (h⁻¹ * (a : H) * h) • v = v := by
      simpa only [Subgroup.smul_def] using hfix
    calc
      (a : H) • (h • v) = ((a : H) * h) • v := by rw [mul_smul]
      _ = h • ((h⁻¹ * (a : H) * h) • v) := by
        simp only [← mul_smul]
        congr 1
        group
      _ = h • v := by rw [hfix']
  · intro hv
    have hinv : h⁻¹ • (h • v) ∈ FixedPoints.subgroup A V := by
      rw [FixedPoints.mem_subgroup]
      intro a
      have hconj : h * (a : H) * h⁻¹ ∈ A :=
        (inferInstance : A.Normal).conj_mem (a : H) a.property h
      have hfix := (FixedPoints.mem_subgroup (M := A) (a := h • v)).1 hv
        ⟨h * (a : H) * h⁻¹, hconj⟩
      have hfix' : (h * (a : H) * h⁻¹) • (h • v) = h • v := by
        simpa only [Subgroup.smul_def] using hfix
      calc
        (a : H) • (h⁻¹ • (h • v)) =
            h⁻¹ • ((h * (a : H) * h⁻¹) • (h • v)) := by
          simp only [← mul_smul]
          congr 1
          group
        _ = h⁻¹ • (h • v) := by rw [hfix']
    simpa [inv_smul_smul] using hinv

private theorem commutatorAction_isInvariant_of_normal_actor
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (Y : Subgroup G) [Y.Normal] :
    IsInvariant G V (commutatorAction Y V) := by
  have hforward : ∀ s : G, ∀ v : V,
      v ∈ commutatorAction Y V → s • v ∈ commutatorAction Y V := by
    intro s v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction
      (p := fun x _ => s • x ∈ Subgroup.closure
        {x : V | ∃ y : Y, ∃ g : V, x = g⁻¹ * y • g})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨y, g, rfl⟩
      refine Subgroup.subset_closure
        ⟨⟨s * (y : G) * s⁻¹,
          (inferInstance : Y.Normal).conj_mem (y : G) y.property s⟩,
          s • g, ?_⟩
      change s • (g⁻¹ * ((y : G) • g)) = _
      have hconj : s • ((y : G) • g) =
          (s * (y : G) * s⁻¹) • (s • g) := by
        simp [smul_smul, mul_assoc]
      rw [smul_mul', smul_inv', hconj]
      rfl
    · simp
    · intro x z _ _ hx hz
      simpa [smul_mul'] using Subgroup.mul_mem _ hx hz
    · intro x _ hx
      simpa [smul_inv'] using Subgroup.inv_mem _ hx
  refine ⟨?_⟩
  intro s v
  constructor
  · exact hforward s v
  · intro hv
    have hback := hforward s⁻¹ (s • v) hv
    simpa [smul_smul] using hback

private theorem subgroup_isComplement'_of_isCompl_of_isMulCommutative
    {V : Type*} [Group V] (C U : Subgroup V)
    (hcomm : IsMulCommutative V) (hcompl : IsCompl C U) :
    C.IsComplement' U := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hcompl.disjoint
  ext v
  constructor
  · intro _
    trivial
  · intro _
    have hv : v ∈ C ⊔ U := by
      rw [hcompl.sup_eq_top]
      trivial
    let _ : C.Normal :=
      ⟨fun c hc x => by
        rw [hcomm.is_comm.comm x c]
        simpa [mul_assoc] using hc⟩
    rcases (Subgroup.mem_sup_of_normal_left.mp hv) with ⟨c, hc, w, hw, rfl⟩
    exact ⟨c, hc, w, hw, rfl⟩

/-- Fixed points split across two invariant complementary subgroups. -/
private theorem natCard_fixedPoints_eq_mul_of_invariant_isCompl
    {A V : Type*} [Group A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (C U : Subgroup V) (hcomm : IsMulCommutative V)
    (hcompl : IsCompl C U)
    [IsInvariant A V C] [IsInvariant A V U] :
    Nat.card (FixedPoints.subgroup A V) =
      Nat.card (FixedPoints.subgroup A C) *
        Nat.card (FixedPoints.subgroup A U) := by
  let hcomp : C.IsComplement' U :=
    subgroup_isComplement'_of_isCompl_of_isMulCommutative C U hcomm hcompl
  let f : FixedPoints.subgroup A C × FixedPoints.subgroup A U →
      FixedPoints.subgroup A V := fun z =>
    ⟨((z.1 : C) : V) * ((z.2 : U) : V), by
      rw [FixedPoints.mem_subgroup]
      intro a
      rw [smul_mul']
      have hc := (FixedPoints.mem_subgroup (M := A) (α := C)
        (a := (z.1 : C))).1 z.1.property a
      have hu := (FixedPoints.mem_subgroup (M := A) (α := U)
        (a := (z.2 : U))).1 z.2.property a
      have hc' := congrArg Subtype.val hc
      have hu' := congrArg Subtype.val hu
      change a • ((z.1 : C) : V) = ((z.1 : C) : V) at hc'
      change a • ((z.2 : U) : V) = ((z.2 : U) : V) at hu'
      rw [hc', hu']⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hpair : ((x.1 : C), (x.2 : U)) = ((y.1 : C), (y.2 : U)) := by
      apply hcomp.1
      exact congrArg Subtype.val hxy
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hpair))
      (Subtype.ext (congrArg Prod.snd hpair))
  have hfsurj : Function.Surjective f := by
    intro v
    obtain ⟨z, hz⟩ := hcomp.2 (v : V)
    let c : C := z.1
    let u : U := z.2
    have hcu : (c : V) * (u : V) = (v : V) := hz
    have hfixed (a : A) : (a • c, a • u) = (c, u) := by
      apply hcomp.1
      have hv := (FixedPoints.mem_subgroup (M := A) (α := V)
        (a := (v : V))).1 v.property a
      have hv' := hv
      change a • (v : V) = (v : V) at hv'
      change (a • (c : V)) * (a • (u : V)) = (c : V) * (u : V)
      rw [← smul_mul', hcu, hv']
    let cf : FixedPoints.subgroup A C := ⟨c, by
      rw [FixedPoints.mem_subgroup]
      intro a
      exact congrArg Prod.fst (hfixed a)⟩
    let uf : FixedPoints.subgroup A U := ⟨u, by
      rw [FixedPoints.mem_subgroup]
      intro a
      exact congrArg Prod.snd (hfixed a)⟩
    refine ⟨(cf, uf), ?_⟩
    apply Subtype.ext
    exact hcu
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)).symm.trans
    (Nat.card_prod _ _)

private theorem isInvariant_restrict_actor
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (A : Subgroup G) (X : Subgroup V) [IsInvariant G V X] :
    IsInvariant A V X := by
  refine ⟨?_⟩
  intro a v
  simpa only [Subgroup.smul_def] using
    (IsInvariant.invariant (A := G) (G := V) (H := X) (a : G) v)

private theorem fixedQuotientCard_eq_restricted_fixedPoints
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V]
    (A : Subgroup G) (X : Subgroup V) [IsInvariant A V X] :
    fixedQuotientCard (G := G) (V := V) A X =
      (Nat.card X : ℚ) / Nat.card (FixedPoints.subgroup A X) := by
  have hmap :
      (FixedPoints.subgroup A X).map X.subtype =
        X ⊓ FixedPoints.subgroup A V :=
    fixedPoints_subgroup_map_subtype_eq_inf X
  have hcard : Nat.card (↥(X ⊓ FixedPoints.subgroup A V)) =
      Nat.card (FixedPoints.subgroup A X) := by
    rw [← hmap, Subgroup.card_map_of_injective X.subtype_injective]
  simp only [fixedQuotientCard, hcard]

/-- The fixed part of an invariant coprime-action complement is fixed by
`P` when the full and commutator-module fixed indices both equal `|P|`. -/
private theorem fixedPart_fixed_by_sylow_of_matching_quotients
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (P : Sylow 2 G)
    (hm : m (G := G) (V := V) (P : Subgroup G) = 1)
    (hfixed : fixedQuotientCard (G := G) (V := V)
      (P : Subgroup G) (commutatorAction (oddCore G) V) =
        (Nat.card (P : Subgroup G) : ℚ)) :
    (P : Subgroup G) ≤ fixingSubgroup G
      (FixedPoints.subgroup (oddCore G) V : Set V) := by
  let W : Subgroup G := oddCore G
  let C : Subgroup V := FixedPoints.subgroup W V
  let U : Subgroup V := commutatorAction W V
  let hWnormal : W.Normal := by
    dsimp only [W, oddCore]
    exact pPrimeCore_normal
  let _ : W.Normal := hWnormal
  let hCinvG : IsInvariant G V C := fixedPoints_isInvariant_of_normal W
  let hUinvG : IsInvariant G V U :=
    commutatorAction_isInvariant_of_normal_actor W
  let _ : IsInvariant G V C := hCinvG
  let _ : IsInvariant G V U := hUinvG
  let hCinvP : IsInvariant (P : Subgroup G) V C :=
    isInvariant_restrict_actor (P : Subgroup G) C
  let hUinvP : IsInvariant (P : Subgroup G) V U :=
    isInvariant_restrict_actor (P : Subgroup G) U
  let _ : IsInvariant (P : Subgroup G) V C := hCinvP
  let _ : IsInvariant (P : Subgroup G) V U := hUinvP
  have hcop : Nat.Coprime (Nat.card W) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact pPrimeCore_coprime_card.symm.pow_right n
  have hcompl : IsCompl C U := by
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := W)
        (Group.isSolvable_of_comm fun x y =>
          (IsMulCommutative.is_comm (M := V)).comm x y)
        hcop inferInstance
  have hcardV : Nat.card C * Nat.card U = Nat.card V :=
    (subgroup_isComplement'_of_isCompl_of_isMulCommutative C U
      inferInstance hcompl).card_mul_card
  have hcardFix :
      Nat.card (FixedPoints.subgroup (P : Subgroup G) V) =
        Nat.card (FixedPoints.subgroup (P : Subgroup G) C) *
          Nat.card (FixedPoints.subgroup (P : Subgroup G) U) :=
    natCard_fixedPoints_eq_mul_of_invariant_isCompl C U inferInstance hcompl
  have hfullNat : Nat.card V =
      Nat.card (FixedPoints.subgroup (P : Subgroup G) V) *
        Nat.card (P : Subgroup G) := by
    have hden : ((Nat.card (FixedPoints.subgroup (P : Subgroup G) V) : ℚ) *
        Nat.card (P : Subgroup G)) ≠ 0 := by
      exact mul_ne_zero
        (by exact_mod_cast (Nat.card_pos
          (α := FixedPoints.subgroup (P : Subgroup G) V)).ne')
        (by exact_mod_cast (Nat.card_pos (α := (P : Subgroup G))).ne')
    unfold m at hm
    exact_mod_cast (div_eq_one_iff_eq hden).1 hm
  have hfixedU : (Nat.card U : ℚ) /
      Nat.card (FixedPoints.subgroup (P : Subgroup G) U) =
        Nat.card (P : Subgroup G) := by
    rw [← fixedQuotientCard_eq_restricted_fixedPoints
      (P : Subgroup G) U]
    exact hfixed
  have hUNat : Nat.card U =
      Nat.card (FixedPoints.subgroup (P : Subgroup G) U) *
        Nat.card (P : Subgroup G) := by
    have hden : (Nat.card (FixedPoints.subgroup (P : Subgroup G) U) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos
        (α := FixedPoints.subgroup (P : Subgroup G) U)).ne'
    have hUNat' : Nat.card U = Nat.card (P : Subgroup G) *
        Nat.card (FixedPoints.subgroup (P : Subgroup G) U) := by
      exact_mod_cast (div_eq_iff hden).1 hfixedU
    simpa [Nat.mul_comm] using hUNat'
  have hcancel : Nat.card C *
        (Nat.card (FixedPoints.subgroup (P : Subgroup G) U) *
          Nat.card (P : Subgroup G)) =
      Nat.card (FixedPoints.subgroup (P : Subgroup G) C) *
        (Nat.card (FixedPoints.subgroup (P : Subgroup G) U) *
          Nat.card (P : Subgroup G)) := by
    calc
      _ = Nat.card C * Nat.card U := by rw [hUNat]
      _ = Nat.card V := hcardV
      _ = Nat.card (FixedPoints.subgroup (P : Subgroup G) V) *
          Nat.card (P : Subgroup G) := hfullNat
      _ = _ := by rw [hcardFix]; ac_rfl
  have hcardC : Nat.card C =
      Nat.card (FixedPoints.subgroup (P : Subgroup G) C) :=
    Nat.mul_right_cancel
      (Nat.mul_pos
        (Nat.card_pos
          (α := FixedPoints.subgroup (P : Subgroup G) U))
        (Nat.card_pos (α := (P : Subgroup G)))) hcancel
  have htop : FixedPoints.subgroup (P : Subgroup G) C = ⊤ :=
    (Subgroup.card_eq_iff_eq_top
      (FixedPoints.subgroup (P : Subgroup G) C)).1 hcardC.symm
  intro p hp
  rw [mem_fixingSubgroup_iff]
  intro c hc
  let cC : C := ⟨c, hc⟩
  have hcfix : cC ∈ FixedPoints.subgroup (P : Subgroup G) C := by
    rw [htop]
    trivial
  have hpc := (FixedPoints.mem_subgroup
    (M := (P : Subgroup G)) (α := C) (a := cC)).1 hcfix ⟨p, hp⟩
  exact congrArg Subtype.val hpc

private theorem full_fixedQuotient_two_of_complement_fixed
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V]
    (A : Subgroup G) (C U : Subgroup V)
    (hcomm : IsMulCommutative V) (hcompl : IsCompl C U)
    [IsInvariant A V C] [IsInvariant A V U]
    (hfixC : A ≤ fixingSubgroup G (C : Set V))
    (hfixedU : fixedQuotientCard (G := G) (V := V) A U = 2) :
    (Nat.card V : ℚ) / Nat.card (FixedPoints.subgroup A V) = 2 := by
  have htopC : FixedPoints.subgroup A C = ⊤ := by
    apply top_unique
    intro c _
    rw [FixedPoints.mem_subgroup]
    intro a
    apply Subtype.ext
    have hafix := hfixC a.property
    rw [mem_fixingSubgroup_iff] at hafix
    exact hafix (c : V) c.property
  have hcardV : Nat.card C * Nat.card U = Nat.card V :=
    (subgroup_isComplement'_of_isCompl_of_isMulCommutative C U
      hcomm hcompl).card_mul_card
  have hcardFix : Nat.card (FixedPoints.subgroup A V) =
      Nat.card (FixedPoints.subgroup A C) *
        Nat.card (FixedPoints.subgroup A U) :=
    natCard_fixedPoints_eq_mul_of_invariant_isCompl C U hcomm hcompl
  have hfixedU' : (Nat.card U : ℚ) /
      Nat.card (FixedPoints.subgroup A U) = 2 := by
    rw [← fixedQuotientCard_eq_restricted_fixedPoints A U]
    exact hfixedU
  have hUNat : Nat.card U =
      2 * Nat.card (FixedPoints.subgroup A U) := by
    have hden : (Nat.card (FixedPoints.subgroup A U) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := FixedPoints.subgroup A U)).ne'
    exact_mod_cast (div_eq_iff hden).1 hfixedU'
  have hfullNat : Nat.card V =
      2 * Nat.card (FixedPoints.subgroup A V) := by
    calc
      Nat.card V = Nat.card C * Nat.card U := hcardV.symm
      _ = Nat.card C * (2 * Nat.card (FixedPoints.subgroup A U)) := by
        rw [hUNat]
      _ = 2 * (Nat.card (FixedPoints.subgroup A C) *
          Nat.card (FixedPoints.subgroup A U)) := by
        rw [htopC]
        simp [Nat.mul_left_comm]
      _ = 2 * Nat.card (FixedPoints.subgroup A V) := by rw [hcardFix]
  have hden : (Nat.card (FixedPoints.subgroup A V) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := FixedPoints.subgroup A V)).ne'
  apply (div_eq_iff hden).2
  exact_mod_cast hfullNat

/-- The local `SL₂(2)` coordinates have fixed index two on the full module
when the Sylow subgroup is a minimal offender (`m(P)=1`). -/
public theorem rankOneLocalSL2Data_full_coordinates
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (P : Sylow 2 G)
    (hdata : RankOneLocalSL2Data (G := G) (V := V) (P : Subgroup G))
    (hm : m (G := G) (V := V) (P : Subgroup G) = 1) :
    ∃ F : Finset (Subgroup G),
      (∀ E : Subgroup G, E ∈ F →
        IsSL2Two (↑E) ∧
          oneOmega (G := G) (V := V)
            ((commutator (↑E)).map E.subtype)) ∧
      IsInternalDirectProduct (oddCore G ⊔ (P : Subgroup G)) F ∧
      oddCore G =
        ⨆ E : {E : Subgroup G // E ∈ F},
          (commutator (E : Subgroup G)).map E.val.subtype ∧
      ∀ E : Subgroup G, E ∈ F →
        let Q := (P : Subgroup G) ⊓ E
        Nat.card Q = 2 ∧
        ⁅(commutator (↑E)).map E.subtype, Q⁆ =
          (commutator (↑E)).map E.subtype ∧
        fixedQuotientCard (G := G) (V := V) Q
          (commutatorAction (oddCore G) V) = 2 ∧
        (Nat.card V : ℚ) / Nat.card (FixedPoints.subgroup Q V) = 2 := by
  obtain ⟨F, hEF, hprod, hodd, hcoord⟩ :=
    rankOneLocalSL2Data_coordinates_generated P hdata
  refine ⟨F, hEF, hprod, hodd, ?_⟩
  let W : Subgroup G := oddCore G
  let C : Subgroup V := FixedPoints.subgroup W V
  let U : Subgroup V := commutatorAction W V
  let hWnormal : W.Normal := by
    dsimp only [W, oddCore]
    exact pPrimeCore_normal
  let _ : W.Normal := hWnormal
  let hCinvG : IsInvariant G V C := fixedPoints_isInvariant_of_normal W
  let hUinvG : IsInvariant G V U :=
    commutatorAction_isInvariant_of_normal_actor W
  let _ : IsInvariant G V C := hCinvG
  let _ : IsInvariant G V U := hUinvG
  have hcop : Nat.Coprime (Nat.card W) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact pPrimeCore_coprime_card.symm.pow_right n
  have hcompl : IsCompl C U := by
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := W)
        (Group.isSolvable_of_comm fun x y =>
          (IsMulCommutative.is_comm (M := V)).comm x y)
        hcop inferInstance
  have hPfixC : (P : Subgroup G) ≤ fixingSubgroup G (C : Set V) := by
    exact fixedPart_fixed_by_sylow_of_matching_quotients P hm hdata.fixed_card
  intro E hE
  let Q : Subgroup G := (P : Subgroup G) ⊓ E
  obtain ⟨hQcard, hcommQ, hfixedQ⟩ := hcoord E hE
  have hQfixC : Q ≤ fixingSubgroup G (C : Set V) :=
    inf_le_left.trans hPfixC
  let hCinvQ : IsInvariant Q V C := isInvariant_restrict_actor Q C
  let hUinvQ : IsInvariant Q V U := isInvariant_restrict_actor Q U
  let _ : IsInvariant Q V C := hCinvQ
  let _ : IsInvariant Q V U := hUinvQ
  refine ⟨hQcard, hcommQ, hfixedQ, ?_⟩
  exact full_fixedQuotient_two_of_complement_fixed Q C U inferInstance
    hcompl hQfixC hfixedQ

end Stellmacher.SectionOne

