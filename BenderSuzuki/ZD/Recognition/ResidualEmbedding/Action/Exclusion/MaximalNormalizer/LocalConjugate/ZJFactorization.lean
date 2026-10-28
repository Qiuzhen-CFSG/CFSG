module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Basic
public import BenderSuzuki.SE.PStabilityReduction

/-!
# Local ZJ factorization

For a solvable join `H = B ⊔ R` with abelian Sylow two-subgroups, an odd-prime
Sylow subgroup `R`, and nontrivial p-core, Glauberman's ZJ theorem makes
`Z(J(R)) O_{p'}(H)` normal. Frattini's argument yields a normalizer
factorization of `H`. Transporting the intrinsic characteristic subgroup
`Omega₁(Z(J(R)))` to the ambient group and intersecting with `B` gives the
factorization used in GLS, Volume 4, Chapter 2, Lemma 7.11.

The core identity with `theta(B)` is an explicit local structural hypothesis;
the canonical quotient construction must establish it separately. Normality
is used only inside `H`. The private transport and Frattini proofs are adapted
from `BenderSuzuki.SE.Section7Final`, without importing that assembly module.
-/

noncomputable section
namespace BenderSuzuki.ZD
open PFAppendixIII PFchapter1section1
universe u

private theorem theorem4b_zj_factorization_of_normal
    {G : Type u} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)
    (P : Sylow p G)
    (hnorm :
      (thompsonCenter (G := G) (P : Subgroup G) ⊔ pPrimeCore p G).Normal) :
    pPrimeCore p G ⊔
        Subgroup.normalizer
          (corollary64Z ⟨p, hp⟩ (P : Subgroup G) : Set G) =
      ⊤ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let J : Subgroup G := thompsonCenter (G := G) (P : Subgroup G)
  let O : Subgroup G := pPrimeCore p G
  let K : Subgroup G := J ⊔ O
  let Z : Subgroup G := corollary64Z ⟨p, hp⟩ (P : Subgroup G)
  have : O.Normal := by
    dsimp [O]
    infer_instance
  have : K.Normal := by
    simpa [K, J, O] using hnorm
  have hJP : J ≤ (P : Subgroup G) := by
    simpa [J] using thompsonCenter_le (G := G) (P : Subgroup G)
  have hPOcop : Nat.Coprime (Nat.card (P : Subgroup G)) (Nat.card O) := by
    rcases P.isPGroup'.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hPO : (P : Subgroup G) ⊓ O = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hPOcop).eq_bot
  have hPK : (P : Subgroup G) ⊓ K = J := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_sup_of_normal_right.mp hx.2 with
        ⟨j, hj, o, ho, hjo⟩
      have hjP : j ∈ (P : Subgroup G) := hJP hj
      have hoP : o ∈ (P : Subgroup G) := by
        have hoeq : o = j⁻¹ * x := by
          rw [← hjo]
          simp
        rw [hoeq]
        exact P.mul_mem (P.inv_mem hjP) hx.1
      have hoBot : o ∈ (⊥ : Subgroup G) := by
        rw [← hPO]
        exact ⟨hoP, ho⟩
      have hoOne : o = 1 := by simpa using hoBot
      rw [← hjo, hoOne]
      simpa using hj
    · exact le_inf hJP le_sup_left
  let PK : Sylow p K := External.hallSylowSubgroupOfNormal P K
  have hPKmap : (PK : Subgroup K).map K.subtype = J := by
    rw [show (PK : Subgroup K) =
        (P : Subgroup G).comap K.subtype by
      exact External.hallSylowSubgroupOfNormal_coe P K]
    rw [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype]
    simpa [inf_comm] using hPK
  have hfrattini : Subgroup.normalizer (J : Set G) ⊔ K = ⊤ := by
    simpa [hPKmap] using
      (Sylow.normalizer_sup_eq_top (G := G) (N := K) PK)
  have hnormJZ : Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (Z : Set G) := by
    have : (omega₁ (G := J) (p := p)).Characteristic :=
      omega₁_characteristic (G := J) (p := p)
    simpa [J, Z, corollary64Z] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (G := G) (H := J) (K := omega₁ (G := J) (p := p)))
  change O ⊔ Subgroup.normalizer (Z : Set G) = ⊤
  apply top_unique
  rw [← hfrattini]
  apply sup_le
  · exact hnormJZ.trans le_sup_right
  · change J ⊔ O ≤ O ⊔ Subgroup.normalizer (Z : Set G)
    apply sup_le
    · exact Subgroup.le_normalizer.trans (hnormJZ.trans le_sup_right)
    · exact le_sup_left

private theorem theorem4b_zj_factorization_of_constrained_stable
    {G : Type u} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)
    (hpodd : p ≠ 2)
    (hOp_ne : pCore p G ≠ ⊥)
    (hconstrained : PConstrainedGroup (G := G) p)
    (hstable : PStableGroup' (G := G) p)
    (P : Sylow p G) :
    pPrimeCore p G ⊔
        Subgroup.normalizer
          (corollary64Z ⟨p, hp⟩ (P : Subgroup G) : Set G) =
      ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  apply theorem4b_zj_factorization_of_normal hp P
  exact G_theorem_8_2_11 p hpodd hOp_ne hconstrained hstable P

private theorem theorem4b_omega1_map_mulEquiv
    {G H : Type*} [Group G] [Group H] {p : ℕ} (e : G ≃* H) :
    (omega₁ (G := G) (p := p)).map e.toMonoidHom =
      omega₁ (G := H) (p := p) := by
  rw [omega₁, omega, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [pow_one] using congrArg e.toMonoidHom hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    simpa [pow_one] using congrArg e.symm.toMonoidHom hy

private theorem theorem4b_thompsonSubgroup_map_subtype_eq
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) (P : Subgroup N) :
    (thompsonSubgroup (G := N) P).map N.subtype =
      thompsonSubgroup (G := G) (P.map N.subtype) := by
  classical
  let e : P ≃* P.map N.subtype :=
    Subgroup.equivMapOfInjective (f := N.subtype) P N.subtype_injective
  have hcomp :
      ((P.map N.subtype).subtype).comp e.toMonoidHom =
        N.subtype.comp P.subtype := by
    ext x
    rfl
  calc
    (thompsonSubgroup (G := N) P).map N.subtype =
        ((thompsonSubgroup (G := P) (⊤ : Subgroup P)).map P.subtype).map
          N.subtype := by rw [thompsonSubgroup_top_map_subtype]
    _ = (thompsonSubgroup (G := P) (⊤ : Subgroup P)).map
          (N.subtype.comp P.subtype) := by rw [Subgroup.map_map]
    _ = ((thompsonSubgroup (G := P) (⊤ : Subgroup P)).map
          e.toMonoidHom).map (P.map N.subtype).subtype := by
            rw [Subgroup.map_map, hcomp]
    _ = (thompsonSubgroup (G := P.map N.subtype)
          (⊤ : Subgroup (P.map N.subtype))).map
          (P.map N.subtype).subtype := by
            rw [thompsonSubgroup_top_map_mulEquiv]
    _ = thompsonSubgroup (G := G) (P.map N.subtype) := by
          rw [thompsonSubgroup_top_map_subtype]

private theorem theorem4b_corollary64Z_map_subtype
    {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    {p : Nat.Primes} (P : Subgroup H) (R : Subgroup X)
    (hPR : P.map H.subtype = R) :
    (corollary64Z p P).map H.subtype = corollary64Z p R := by
  let JH : Subgroup H := thompsonCenter (G := H) P
  let JX : Subgroup X := thompsonCenter (G := X) R
  have hJmap : JH.map H.subtype = JX := by
    calc
      JH.map H.subtype =
          (centerIn (G := H) (thompsonSubgroup (G := H) P)).map
            H.subtype := by rfl
      _ = centerIn (G := X)
          ((thompsonSubgroup (G := H) P).map H.subtype) := by
            exact centerIn_top_map_subtype H (thompsonSubgroup (G := H) P)
      _ = thompsonCenter (G := X) (P.map H.subtype) := by
            rw [theorem4b_thompsonSubgroup_map_subtype_eq]
            rfl
      _ = JX := by rw [hPR]
  let eJ0 : JH ≃* JH.map H.subtype :=
    Subgroup.equivMapOfInjective JH H.subtype H.subtype_injective
  let eJ : JH ≃* JX := eJ0.trans (MulEquiv.subgroupCongr hJmap)
  have hOmega :
      (omega₁ (G := JH) (p := p.val)).map eJ.toMonoidHom =
        omega₁ (G := JX) (p := p.val) :=
    theorem4b_omega1_map_mulEquiv eJ
  have hcomp :
      JX.subtype.comp eJ.toMonoidHom = H.subtype.comp JH.subtype := by
    ext x
    simp [eJ, eJ0, MulEquiv.subgroupCongr_apply]
  calc
    (corollary64Z p P).map H.subtype =
        ((omega₁ (G := JH) (p := p.val)).map JH.subtype).map
          H.subtype := by rfl
    _ = (omega₁ (G := JH) (p := p.val)).map
          (H.subtype.comp JH.subtype) := by rw [Subgroup.map_map]
    _ = ((omega₁ (G := JH) (p := p.val)).map eJ.toMonoidHom).map
          JX.subtype := by rw [Subgroup.map_map, hcomp]
    _ = (omega₁ (G := JX) (p := p.val)).map JX.subtype := by rw [hOmega]
    _ = corollary64Z p R := by rfl

private theorem theorem4b_normalizer_comap_of_map_subtype_eq
    {X : Type*} [Group X] (H : Subgroup X) (K : Subgroup H)
    (L : Subgroup X) (hKL : K.map H.subtype = L) :
    (Subgroup.normalizer (L : Set X)).comap H.subtype =
      Subgroup.normalizer (K : Set H) := by
  have hLrange : L ≤ H.subtype.range := by
    rw [← hKL]
    exact Subgroup.map_le_range H.subtype K
  calc
    (Subgroup.normalizer (L : Set X)).comap H.subtype =
        Subgroup.normalizer (L.comap H.subtype : Set H) :=
      Subgroup.comap_normalizer_eq_of_le_range hLrange
    _ = Subgroup.normalizer (K : Set H) := by
      rw [← hKL,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

private theorem theorem4b_intersect_factorization
    {G : Type*} [Group G]
    {H B O N : Subgroup G}
    (hfactor : O ⊔ N = H) (hOnorm : O.Normal)
    (hOB : O ≤ B) (hBH : B ≤ H) :
    B = O ⊔ (B ⊓ N) := by
  let : O.Normal := hOnorm
  apply le_antisymm
  · intro x hxB
    have hxSup : x ∈ O ⊔ N := by
      rw [hfactor]
      exact hBH hxB
    rcases Subgroup.mem_sup_of_normal_left.mp hxSup with
      ⟨o, ho, n, hn, hon⟩
    have hoB : o ∈ B := hOB ho
    have hnB : n ∈ B := by
      have hne : n = o⁻¹ * x := by
        rw [← hon]
        simp
      rw [hne]
      exact B.mul_mem (B.inv_mem hoB) hxB
    exact Subgroup.mem_sup_of_normal_left.mpr
      ⟨o, ho, n, ⟨hnB, hn⟩, hon⟩
  · exact sup_le hOB inf_le_left

/-- The general local factorization in Lemma 7.11. Its hypotheses concern
only `B ⊔ R`; p-stability and p-constraint are derived, not assumed. -/
public theorem local_zj_factorization
    {G : Type u} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (B R : Subgroup G)
    (hsolv : Group.IsSolvable ↥(B ⊔ R))
    (hSylow : HasAbelianSylow 2 ↥(B ⊔ R))
    (hR : theorem4bIsSylowSubgroupOf p R (B ⊔ R))
    (hcore : pCore p ↥(B ⊔ R) ≠ ⊥)
    (htheta : (pPrimeCore p ↥(B ⊔ R)).map (B ⊔ R).subtype =
      corollary64Theta p B) :
    B = corollary64Theta p B ⊔
      (B ⊓ Subgroup.normalizer (corollary64Z ⟨p, hp⟩ R : Set G)) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let H : Subgroup G := B ⊔ R
  let O : Subgroup H := pPrimeCore p H
  let Z : Subgroup G := corollary64Z ⟨p, hp⟩ R
  let N : Subgroup H := (Subgroup.normalizer (Z : Set G)).comap H.subtype
  obtain ⟨P, hRP⟩ := hR
  have hstable : PStableGroup' (G := H) p :=
    pStableGroup'_of_solvable_abelianSylowTwo hsolv hSylow hpodd
  have hconstrained : PConstrainedGroup (G := H) p :=
    theorem4b_pConstrainedGroup_of_solvable hsolv p
  have hp2 : p ≠ 2 := by
    intro heq
    exact (by decide : ¬ Odd 2) (heq ▸ hpodd)
  have hZmap : (corollary64Z ⟨p, hp⟩ (P : Subgroup H)).map H.subtype = Z :=
    theorem4b_corollary64Z_map_subtype (P : Subgroup H) R hRP.symm
  have hfac : O ⊔ N = ⊤ := by
    dsimp only [O, N]
    rw [theorem4b_normalizer_comap_of_map_subtype_eq H _ Z hZmap]
    exact theorem4b_zj_factorization_of_constrained_stable hp hp2 hcore
      hconstrained hstable P
  have hBH : B ≤ H := le_sup_left
  have hthetaB : corollary64Theta p B ≤ B :=
    (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hOB : O ≤ B.subgroupOf H := by
    intro x hx
    change (x : G) ∈ B
    apply hthetaB
    rw [← htheta]
    exact Subgroup.mem_map_of_mem H.subtype hx
  have hinter : B.subgroupOf H = O ⊔ (B.subgroupOf H ⊓ N) :=
    theorem4b_intersect_factorization hfac inferInstance hOB le_top
  have hmapN : N.map H.subtype = H ⊓ Subgroup.normalizer (Z : Set G) := by
    dsimp only [N]
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
  have hmapInf : (B.subgroupOf H ⊓ N).map H.subtype =
      B ⊓ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hBH, hmapN,
      ← inf_assoc, inf_eq_left.mpr hBH]
  calc
    B = (B.subgroupOf H).map H.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hBH).symm
    _ = (O ⊔ (B.subgroupOf H ⊓ N)).map H.subtype :=
      congrArg (Subgroup.map H.subtype) hinter
    _ = corollary64Theta p B ⊔
        (B ⊓ Subgroup.normalizer (Z : Set G)) := by
      rw [Subgroup.map_sup, hmapInf]
      exact congrArg (fun K => K ⊔ (B ⊓ Subgroup.normalizer (Z : Set G))) htheta

end BenderSuzuki.ZD
