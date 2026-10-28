module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
public import Theory.AlgebraicGroup.RootSystems.GraphDegree

universe u

open Set

/-! Faithful conjugation and the ambient center. -/
namespace Theory.AlgebraicGroup

public theorem center_eq_bot_of_faithful_conjugation
    {G : Type*} [Group G] (L U : Subgroup G)
    (hCenterL : Subgroup.center G ≤ L)
    (hFaithful : ∀ l, l ∈ L → (∀ u, u ∈ U → l⁻¹ * u * l = u) → l = 1) :
    Subgroup.center G = ⊥ := by
  apply le_antisymm
  · intro z hz
    apply Subgroup.mem_bot.mpr
    apply hFaithful z (hCenterL hz)
    intro u hu
    have hcomm := Subgroup.mem_center_iff.mp hz u
    rw [← mul_left_cancel_iff (a := z)]
    simpa [mul_assoc] using hcomm
  · exact bot_le

public theorem kernel_of_conjugation_eq_center_of_intersection
    {G : Type u} [Group G] (L U : Subgroup G)
    (hLU : L ⊓ Subgroup.centralizer (U : Set G) = Subgroup.center G) :
    ∀ l : G, l ∈ L →
      ((∀ u : G, u ∈ U → l⁻¹ * u * l = u) ↔ l ∈ Subgroup.center G) := by
  intro l hl
  constructor
  · intro htriv
    have hcentralizer : l ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hcomm := congrArg (fun x => l * x) (htriv u hu)
      simpa [mul_assoc] using hcomm
    have hlinf : l ∈ L ⊓ Subgroup.centralizer (U : Set G) := ⟨hl, hcentralizer⟩
    simpa [hLU] using hlinf
  · intro hcenter u hu
    have hcomm := (Subgroup.mem_center_iff.mp hcenter) u
    have hconj := congrArg (fun x => l⁻¹ * x) hcomm
    simpa [mul_assoc] using hconj

open scoped commutatorElement

public theorem nilpotencyClass_eq_of_lowerCentralSeries
    {G : Type*} [Group G] (S : ℕ → Subgroup G) (c : ℕ)
    (hEq : ∀ i, S (i + 1) = Subgroup.lowerCentralSeries (⊤ : Subgroup G) i)
    (hTerminal : S (c + 1) = ⊥)
    (hPrev : 0 < c → S c ≠ ⊥) :
    Group.nilpotencyClass G = c := by
  have hnil : Group.IsNilpotent G := by
    apply (Subgroup.nilpotent_iff_finite_descending_central_series G).mpr
    refine ⟨c, fun i => S (i + 1), ?_, hTerminal⟩
    constructor
    · exact hEq 0
    · intro x n hx g
      change x ∈ S (n + 1) at hx
      change ⁅x, g⁆ ∈ S (n + 2)
      rw [hEq n] at hx
      rw [hEq (n + 1)]
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top g)
  let : Group.IsNilpotent G := hnil
  have hle : Group.nilpotencyClass G ≤ c := by
    rw [← Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
    rw [← hEq c]
    exact hTerminal
  have hge : c ≤ Group.nilpotencyClass G := by
    by_contra hnot
    have hlt : Group.nilpotencyClass G < c := Nat.lt_of_not_ge hnot
    have hcle : Group.nilpotencyClass G ≤ c - 1 := by omega
    have hbot : Subgroup.lowerCentralSeries (⊤ : Subgroup G) (c - 1) = ⊥ :=
      (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le).mpr hcle
    have hprev : S c = ⊥ := by
      have hc : c - 1 + 1 = c := by omega
      rw [← hc, hEq (c - 1)]
      exact hbot
    exact hPrev (by omega) hprev
  exact Nat.le_antisymm hle hge

public theorem nilpotencyClass_le_of_descendingCentralSeries
    {G : Type*} [Group G] (H : ℕ → Subgroup G) (n : ℕ)
    (hH : Subgroup.IsDescendingCentralSeries H) (hn : H n = ⊥) :
    Group.nilpotencyClass G ≤ n := by
  have hnil : Group.IsNilpotent G :=
    (Subgroup.nilpotent_iff_finite_descending_central_series G).mpr ⟨n, H, hH, hn⟩
  let : Group.IsNilpotent G := hnil
  rw [← Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  have hle := Subgroup.descending_central_series_ge_lower H hH n
  rw [hn] at hle
  exact le_antisymm hle bot_le

open Set

section

/-- Two successive positive-root extensions across a simple root satisfy the
root-system diamond property. -/
public theorem simpleRootExtension_exchange
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible] (base : P.Base)
    (α δ β η ζ : ι) (hαpos : base.IsPos α) (hβpos : base.IsPos β)
    (hδ : δ ∈ base.support) (hη : P.root η = P.root α + P.root δ)
    (hζ : P.root ζ = P.root η + P.root β) :
    P.root α + P.root β ∈ Set.range P.root ∨
      P.root δ + P.root β ∈ Set.range P.root := by
  classical
  have hδpos := base.isPos_of_mem_support hδ
  have hαδnot : P.root α ≠ -P.root δ := by
    intro hneg
    let := P.indexNeg
    have hidx : α = -δ := P.root.injective (by simpa using hneg)
    rw [hidx, RootPairing.Base.IsPos.neg_iff_not base] at hαpos
    exact hαpos hδpos
  have hαβnot : P.root α ≠ -P.root β := by
    intro hneg
    let := P.indexNeg
    have hidx : α = -β := P.root.injective (by simpa using hneg)
    rw [hidx, RootPairing.Base.IsPos.neg_iff_not base] at hαpos
    exact hαpos hβpos
  have hδβnot : P.root δ ≠ -P.root β := by
    intro hneg
    let := P.indexNeg
    have hidx : δ = -β := P.root.injective (by simpa using hneg)
    rw [hidx, RootPairing.Base.IsPos.neg_iff_not base] at hδpos
    exact hδpos hβpos
  by_cases hG2 : P.IsG2
  · let : P.IsG2 := hG2
    let : P.EmbeddedG2 := RootPairing.IsG2.toEmbeddedG2 P
    let roots : Fin 2 → M :=
      ![RootPairing.EmbeddedG2.shortRoot P, RootPairing.EmbeddedG2.longRoot P]
    let lc : (Fin 2 → ℤ) →ₗ[ℤ] M := Fintype.linearCombination ℤ roots
    have hrepr (i : ι) :
        ∃ c ∈ RootPairing.EmbeddedG2.allCoeffs, P.root i = lc c := by
      have hi := RootPairing.EmbeddedG2.mem_allRoots P i
      rw [RootPairing.EmbeddedG2.allRoots_eq_map_allCoeffs] at hi
      simp only [List.mem_map] at hi
      obtain ⟨c, hc, hci⟩ := hi
      exact ⟨c, hc, by simpa [lc, roots] using hci.symm⟩
    obtain ⟨cα, hcα, hrootα⟩ := hrepr α
    obtain ⟨cδ, hcδ, hrootδ⟩ := hrepr δ
    obtain ⟨cβ, hcβ, hrootβ⟩ := hrepr β
    obtain ⟨cη, hcη, hrootη⟩ := hrepr η
    obtain ⟨cζ, hcζ, hrootζ⟩ := hrepr ζ
    obtain ⟨iα, hiα⟩ := List.mem_iff_get.mp hcα
    obtain ⟨iδ, hiδ⟩ := List.mem_iff_get.mp hcδ
    obtain ⟨iβ, hiβ⟩ := List.mem_iff_get.mp hcβ
    obtain ⟨iη, hiη⟩ := List.mem_iff_get.mp hcη
    obtain ⟨iζ, hiζ⟩ := List.mem_iff_get.mp hcζ
    subst cα
    subst cδ
    subst cβ
    subst cη
    subst cζ
    have hLI : LinearIndependent ℤ roots :=
      (RootPairing.EmbeddedG2.linearIndependent_short_long P).restrict_scalars' ℤ
    have hcoeffη :
        RootPairing.EmbeddedG2.allCoeffs.get iη =
          RootPairing.EmbeddedG2.allCoeffs.get iα +
            RootPairing.EmbeddedG2.allCoeffs.get iδ := by
      apply funext
      apply Fintype.linearIndependent_iffₛ.mp hLI
      simpa [lc, Fintype.linearCombination_apply] using
        (calc
          lc (RootPairing.EmbeddedG2.allCoeffs.get iη) = P.root η := hrootη.symm
          _ = P.root α + P.root δ := hη
          _ = lc (RootPairing.EmbeddedG2.allCoeffs.get iα) +
                lc (RootPairing.EmbeddedG2.allCoeffs.get iδ) := by rw [← hrootα, ← hrootδ]
          _ = lc (RootPairing.EmbeddedG2.allCoeffs.get iα +
                RootPairing.EmbeddedG2.allCoeffs.get iδ) := by rw [map_add])
    have hcoeffζ :
        RootPairing.EmbeddedG2.allCoeffs.get iζ =
          RootPairing.EmbeddedG2.allCoeffs.get iη +
            RootPairing.EmbeddedG2.allCoeffs.get iβ := by
      apply funext
      apply Fintype.linearIndependent_iffₛ.mp hLI
      simpa [lc, Fintype.linearCombination_apply] using
        (calc
          lc (RootPairing.EmbeddedG2.allCoeffs.get iζ) = P.root ζ := hrootζ.symm
          _ = P.root η + P.root β := hζ
          _ = lc (RootPairing.EmbeddedG2.allCoeffs.get iη) +
                lc (RootPairing.EmbeddedG2.allCoeffs.get iβ) := by rw [← hrootη, ← hrootβ]
          _ = lc (RootPairing.EmbeddedG2.allCoeffs.get iη +
                RootPairing.EmbeddedG2.allCoeffs.get iβ) := by rw [map_add])
    have hcoeffαδ : RootPairing.EmbeddedG2.allCoeffs.get iα ≠
        -RootPairing.EmbeddedG2.allCoeffs.get iδ := by
      intro h
      apply hαδnot
      rw [hrootα, hrootδ, h, map_neg]
    have hcoeffαβ : RootPairing.EmbeddedG2.allCoeffs.get iα ≠
        -RootPairing.EmbeddedG2.allCoeffs.get iβ := by
      intro h
      apply hαβnot
      rw [hrootα, hrootβ, h, map_neg]
    have hcoeffδβ : RootPairing.EmbeddedG2.allCoeffs.get iδ ≠
        -RootPairing.EmbeddedG2.allCoeffs.get iβ := by
      intro h
      apply hδβnot
      rw [hrootδ, hrootβ, h, map_neg]
    have hsumαδ : RootPairing.EmbeddedG2.allCoeffs.get iα +
        RootPairing.EmbeddedG2.allCoeffs.get iδ ∈
          RootPairing.EmbeddedG2.allCoeffs := by
      rw [← hcoeffη]
      exact List.get_mem _ iη
    have hsumαδβ : RootPairing.EmbeddedG2.allCoeffs.get iα +
        RootPairing.EmbeddedG2.allCoeffs.get iδ +
          RootPairing.EmbeddedG2.allCoeffs.get iβ ∈
            RootPairing.EmbeddedG2.allCoeffs := by
      rw [← hcoeffη, ← hcoeffζ]
      exact List.get_mem _ iζ
    have hfinite :
        ∀ ia id ib : Fin RootPairing.EmbeddedG2.allCoeffs.length,
          RootPairing.EmbeddedG2.allCoeffs.get ia ≠
            -RootPairing.EmbeddedG2.allCoeffs.get id →
          RootPairing.EmbeddedG2.allCoeffs.get ia ≠
            -RootPairing.EmbeddedG2.allCoeffs.get ib →
          RootPairing.EmbeddedG2.allCoeffs.get id ≠
            -RootPairing.EmbeddedG2.allCoeffs.get ib →
          RootPairing.EmbeddedG2.allCoeffs.get ia +
              RootPairing.EmbeddedG2.allCoeffs.get id ∈
            RootPairing.EmbeddedG2.allCoeffs →
          RootPairing.EmbeddedG2.allCoeffs.get ia +
              RootPairing.EmbeddedG2.allCoeffs.get id +
              RootPairing.EmbeddedG2.allCoeffs.get ib ∈
            RootPairing.EmbeddedG2.allCoeffs →
          RootPairing.EmbeddedG2.allCoeffs.get ia +
              RootPairing.EmbeddedG2.allCoeffs.get ib ∈
            RootPairing.EmbeddedG2.allCoeffs ∨
          RootPairing.EmbeddedG2.allCoeffs.get id +
              RootPairing.EmbeddedG2.allCoeffs.get ib ∈
            RootPairing.EmbeddedG2.allCoeffs := by
      decide
    rcases hfinite iα iδ iβ hcoeffαδ hcoeffαβ hcoeffδβ hsumαδ hsumαδβ with hx | hx
    · obtain ⟨ix, hx⟩ := List.mem_iff_get.mp hx
      apply Or.inl
      have hxmem : lc (RootPairing.EmbeddedG2.allCoeffs.get ix) ∈
          RootPairing.EmbeddedG2.allRoots P := by
        rw [RootPairing.EmbeddedG2.allRoots_eq_map_allCoeffs]
        exact List.mem_map.mpr ⟨_, List.get_mem _ ix, rfl⟩
      obtain ⟨ρ, hρ⟩ := RootPairing.EmbeddedG2.allRoots_subset_range_root P
        (List.mem_toFinset.mpr hxmem)
      refine ⟨ρ, ?_⟩
      rw [hρ, hx, map_add, ← hrootα, ← hrootβ]
    · obtain ⟨ix, hx⟩ := List.mem_iff_get.mp hx
      apply Or.inr
      have hxmem : lc (RootPairing.EmbeddedG2.allCoeffs.get ix) ∈
          RootPairing.EmbeddedG2.allRoots P := by
        rw [RootPairing.EmbeddedG2.allRoots_eq_map_allCoeffs]
        exact List.mem_map.mpr ⟨_, List.get_mem _ ix, rfl⟩
      obtain ⟨ρ, hρ⟩ := RootPairing.EmbeddedG2.allRoots_subset_range_root P
        (List.mem_toFinset.mpr hxmem)
      refine ⟨ρ, ?_⟩
      rw [hρ, hx, map_add, ← hrootδ, ← hrootβ]
  · let : P.IsNotG2 := P.not_isG2_iff_isNotG2.mp hG2
    have hηβmem : P.root η + P.root β ∈ Set.range P.root := ⟨ζ, hζ⟩
    have hηβle : P.pairingIn ℤ η β ≤ 0 := P.pairingIn_le_zero_of_root_add_mem hηβmem
    have hpairaddR : P.pairing η β = P.pairing α β + P.pairing δ β := by
      change P.coroot' β (P.root η) = P.coroot' β (P.root α) + P.coroot' β (P.root δ)
      rw [hη, map_add]
    have hpairadd : P.pairingIn ℤ η β =
        P.pairingIn ℤ α β + P.pairingIn ℤ δ β := by
      apply FaithfulSMul.algebraMap_injective ℤ R
      rw [map_add, P.algebraMap_pairingIn, P.algebraMap_pairingIn,
        P.algebraMap_pairingIn]
      exact hpairaddR
    by_contra hnot
    push Not at hnot
    have hαβnonneg : 0 ≤ P.pairingIn ℤ α β := by
      by_contra hneg
      exact hnot.1 (P.root_add_root_mem_of_pairingIn_neg (by omega) hαβnot)
    have hδβnonneg : 0 ≤ P.pairingIn ℤ δ β := by
      by_contra hneg
      exact hnot.2 (P.root_add_root_mem_of_pairingIn_neg (by omega) hδβnot)
    have hαβzero : P.pairingIn ℤ α β = 0 := by omega
    have hδβzero : P.pairingIn ℤ δ β = 0 := by omega
    have hβαzero : P.pairingIn ℤ β α = 0 :=
      (P.pairingIn_eq_zero_iff (S := ℤ)).mp hαβzero
    have hβδzero : P.pairingIn ℤ β δ = 0 :=
      (P.pairingIn_eq_zero_iff (S := ℤ)).mp hδβzero
    have hζδle : P.pairingIn ℤ ζ δ ≤ 0 := by
      by_contra hpos
      have hζδ : ζ ≠ δ := by
        intro hEq
        have hroot := hζ
        rw [hEq, hη] at hroot
        have hzero : P.root α + P.root β = 0 := by
          calc
            P.root α + P.root β = (P.root α + P.root δ + P.root β) - P.root δ := by abel
            _ = P.root δ - P.root δ := by rw [← hroot]
            _ = 0 := sub_self _
        exact hαβnot (eq_neg_of_add_eq_zero_left hzero)
      obtain ⟨ρ, hρ⟩ := P.root_sub_root_mem_of_pairingIn_pos (by omega) hζδ
      apply hnot.1
      exact ⟨ρ, by rw [hρ, hζ, hη]; abel⟩
    have hζαle : P.pairingIn ℤ ζ α ≤ 0 := by
      by_contra hpos
      have hζα : ζ ≠ α := by
        intro hEq
        have hroot := hζ
        rw [hEq, hη] at hroot
        have hzero : P.root δ + P.root β = 0 := by
          calc
            P.root δ + P.root β = (P.root α + P.root δ + P.root β) - P.root α := by abel
            _ = P.root α - P.root α := by rw [← hroot]
            _ = 0 := sub_self _
        exact hδβnot (eq_neg_of_add_eq_zero_left hzero)
      obtain ⟨ρ, hρ⟩ := P.root_sub_root_mem_of_pairingIn_pos (by omega) hζα
      apply hnot.2
      exact ⟨ρ, by rw [hρ, hζ, hη]; abel⟩
    have hζδadd : P.pairingIn ℤ ζ δ = P.pairingIn ℤ α δ + 2 := by
      apply FaithfulSMul.algebraMap_injective ℤ R
      rw [map_add, P.algebraMap_pairingIn, P.algebraMap_pairingIn, map_ofNat]
      change P.coroot' δ (P.root ζ) = P.coroot' δ (P.root α) + 2
      rw [hζ, hη, map_add, map_add]
      rw [show P.coroot' δ (P.root δ) = 2 by exact P.pairing_same δ]
      rw [show P.coroot' δ (P.root β) = 0 by
        change P.pairing β δ = 0
        rw [← P.algebraMap_pairingIn ℤ, hβδzero, map_zero]]
      ring
    have hζαadd : P.pairingIn ℤ ζ α = 2 + P.pairingIn ℤ δ α := by
      apply FaithfulSMul.algebraMap_injective ℤ R
      rw [map_add, P.algebraMap_pairingIn, P.algebraMap_pairingIn, map_ofNat]
      change P.coroot' α (P.root ζ) = 2 + P.coroot' α (P.root δ)
      rw [hζ, hη, map_add, map_add]
      rw [show P.coroot' α (P.root α) = 2 by exact P.pairing_same α]
      rw [show P.coroot' α (P.root β) = 0 by
        change P.pairing β α = 0
        rw [← P.algebraMap_pairingIn ℤ, hβαzero, map_zero]]
      ring
    have hαδle : P.pairingIn ℤ α δ ≤ -2 := by omega
    have hδαle : P.pairingIn ℤ δ α ≤ -2 := by omega
    have hαδne : P.root α ≠ P.root δ := by
      intro hEq
      have hsameR : P.pairing α δ = 2 := by
        change P.coroot' δ (P.root α) = 2
        rw [hEq]
        exact P.pairing_same δ
      have hsame : P.pairingIn ℤ α δ = 2 := by
        apply FaithfulSMul.algebraMap_injective ℤ R
        rw [P.algebraMap_pairingIn, map_ofNat]
        exact hsameR
      omega
    have hpairs := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'
      α δ hαδne hαδnot
    have hpairαδ : P.pairingIn ℤ α δ = -2 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hpairs
      omega
    have hpairδα : P.pairingIn ℤ δ α = -2 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hpairs
      omega
    have hopp : P.root α = -P.root δ :=
      (P.pairingIn_neg_two_neg_two_iff (S := ℤ) α δ).mp ⟨hpairαδ, hpairδα⟩
    exact hαδnot hopp

end

open scoped commutatorElement

section

/-- A finite descending series is a commutator series when each layer is
generated by the preceding commutator modulo the next layer.  The proof is a
descending induction from the terminal layer; this isolates the quotient-layer
step used in the source proof of GLS3, Chapter 3, §3.2.2. -/
public theorem subgroupSeries_commutator_eq_of_mod_next
    {G : Type u} [Group G] (H : Subgroup G) (S : ℕ → Subgroup G)
    (c : ℕ)
    (hAnti : ∀ i, 0 < i → S (i + 1) ≤ S i)
    (hCommLe : ∀ i, 0 < i → ⁅S i, H⁆ ≤ S (i + 1))
    (hMod : ∀ i, 0 < i → i ≤ c →
      S (i + 1) ≤ ⁅S i, H⁆ ⊔ S (i + 2))
    (hTerminal : S (c + 1) = ⊥) :
    ∀ i, 0 < i → i ≤ c → ⁅S i, H⁆ = S (i + 1) := by
  have hReverse : ∀ i, 0 < i → i ≤ c → S (i + 1) ≤ ⁅S i, H⁆ := by
    intro i hi hile
    refine Nat.decreasingInduction' (m := i) (n := c) ?_ hile ?_
    · intro k hk h1 hnext
      have hnext' : S (k + 2) ≤ ⁅S k, H⁆ := by
        simpa [Nat.add_assoc] using
          hnext.trans ((Subgroup.commutator_mono (hAnti k (by omega)) le_rfl))
      exact (hMod k (by omega) (by omega)).trans <|
        sup_le (le_rfl) hnext'
    · rw [hTerminal]
      exact bot_le
  intro i hi hile
  exact le_antisymm (hCommLe i hi) (hReverse i hi hile)

end

open scoped commutatorElement

section

/-- A subgroup filtration whose first layer is the ambient subgroup and whose
  successive layers are exactly the commutators with that subgroup agrees
  with the lower central series. -/
public theorem subgroupSeries_eq_lowerCentralSeries_of_commutator_eq
    {G : Type u} [Group G] (H : Subgroup G) (S : ℕ → Subgroup G)
    (hS1 : S 1 = H)
    (hComm : ∀ i : ℕ, ⁅S (i + 1), H⁆ = S (i + 2)) :
    ∀ i : ℕ, S (i + 1) = H.lowerCentralSeries i := by
  intro i
  induction i with
  | zero => simpa [Subgroup.lowerCentralSeries_zero] using hS1
  | succ i ih =>
      rw [Subgroup.lowerCentralSeries_succ, ← ih]
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using (hComm i).symm

end

/-!
An explicit factorization and a trivial intersection give uniqueness of the
`U * L` coordinates.  This is the group-theoretic core needed by the Levi
factorization clause; it deliberately keeps both hypotheses visible instead
of importing the unfinished numbered theorem as a proof bridge.
-/
public theorem subgroup_factorization_unique_of_inf_eq_bot
    {G : Type*} [Group G]
    (U L P : Subgroup G)
    (hExist : ∀ p, p ∈ P → ∃ u, u ∈ U ∧ ∃ l, l ∈ L ∧ p = u * l)
    (hInf : U ⊓ L = ⊥) :
    ∀ p, p ∈ P → ∃! z : U × L, p = z.1.1 * z.2.1 := by
  intro p hp
  rcases hExist p hp with ⟨u, hu, l, hl, hpl⟩
  refine ⟨⟨⟨u, hu⟩, ⟨l, hl⟩⟩, hpl, ?_⟩
  intro z hz
  rcases z with ⟨u', l'⟩
  have hprod : (u' : G) * (l' : G) = (u : G) * (l : G) := hz.symm.trans hpl
  have hcancel : (u' : G)⁻¹ * (u : G) = (l' : G) * (l : G)⁻¹ := by
    have hleft := congrArg (fun x : G => (u' : G)⁻¹ * x) hprod
    have hright := congrArg (fun x : G => x * (l : G)⁻¹) hleft
    simpa [mul_assoc] using hright.symm
  have hu' : (u' : G)⁻¹ * (u : G) ∈ U :=
    U.mul_mem (U.inv_mem u'.property) hu
  have hl' : (l' : G) * (l : G)⁻¹ ∈ L :=
    L.mul_mem l'.property (L.inv_mem hl)
  have hinter : (u' : G)⁻¹ * (u : G) ∈ U ⊓ L := by
    rw [Subgroup.mem_inf]
    exact ⟨hu', hcancel ▸ hl'⟩
  have hone : (u' : G)⁻¹ * (u : G) = 1 := by
    rw [hInf] at hinter
    simpa using hinter
  have huEq : (u' : G) = (u : G) := inv_mul_eq_one.mp hone
  have hlEq : (l' : G) = (l : G) := by
    apply mul_inv_eq_one.mp
    rw [← hcancel, huEq]
    simp
  exact Prod.ext (Subtype.ext huEq) (Subtype.ext hlEq)

open scoped commutatorElement

public theorem upperCentralSeries_eq_of_commutator_detection
    {G : Type*} [Group G] (H : ℕ → Subgroup G) (c : ℕ)
    (hZero : H 0 = ⊥)
    (hTop : H (c + 1) = ⊤)
    (hComm : ∀ n, ⁅H (n + 1), (⊤ : Subgroup G)⁆ ≤ H n)
    (hDetect : ∀ n, n < c →
      ∀ x, x ∉ H (n + 1) →
        ∃ y : G, ⁅x, y⁆ ∉ H n) :
    ∀ n, n ≤ c + 1 → Subgroup.upperCentralSeries G n = H n := by
  intro n hn
  induction n with
  | zero => simp [hZero]
  | succ n ih =>
      by_cases hnc : n = c
      · subst n
        apply le_antisymm
        · rw [hTop]
          exact le_top
        · rw [hTop]
          intro x hx
          rw [Subgroup.mem_upperCentralSeries_succ_iff]
          intro y
          have hxH : x ∈ H (c + 1) := by simp [hTop]
          have hxy := (Subgroup.commutator_le.mp (hComm c)) x hxH y (by simp)
          rw [← ih (by omega)] at hxy
          exact hxy
      · have hnc' : n < c := by omega
        have hnle : n ≤ c := by omega
        apply le_antisymm
        · intro x hx
          by_contra hxnot
          obtain ⟨y, hy⟩ := hDetect n hnc' x hxnot
          have hxy : ⁅x, y⁆ ∈ H n := by
            rw [← ih (by omega)]
            exact Subgroup.mem_upperCentralSeries_succ_iff.mp hx y
          exact hy hxy
        · intro x hx
          rw [Subgroup.mem_upperCentralSeries_succ_iff]
          intro y
          have hxy : ⁅x, y⁆ ∈ H n := by
            exact (Subgroup.commutator_le.mp (hComm n) x hx y (by simp))
          exact (ih (by omega)) ▸ hxy

/-! Nilpotency bounds from subgroup series. -/

public theorem nilpotencyClass_le_of_subgroupSeries
    {G : Type*} [Group G] (U : Subgroup G) (S : ℕ → Subgroup G) (a : ℕ)
    (hOne : S 1 = U)
    (hComm : ∀ i, ⁅S (i + 1), U⁆ ≤ S (i + 2))
    (hTerminal : S (a + 1) = ⊥) :
    Group.nilpotencyClass U ≤ a := by
  let H : ℕ → Subgroup U := fun n => (S (n + 1)).comap U.subtype
  have hH : Subgroup.IsDescendingCentralSeries H := by
    constructor
    · dsimp [H]
      rw [hOne]
      ext x
      simp
    · intro x n hx g
      have hx' : (x : G) ∈ S (n + 1) := hx
      have hg' : (g : G) ∈ U := g.property
      have hamb := (Subgroup.commutator_le.mp (hComm n)) (x : G) hx' (g : G) hg'
      change ((⁅x, g⁆ : U) : G) ∈ S (n + 1 + 1)
      simpa [commutatorElement_def] using hamb
  apply nilpotencyClass_le_of_descendingCentralSeries H a hH
  dsimp [H]
  rw [hTerminal]
  ext x
  simp

open scoped commutatorElement

public theorem upperCentralSeries_map_eq_of_commutator_detection
    {G : Type*} [Group G] (U : Subgroup G) (A : ℕ → Subgroup G) (c : ℕ)
    (hZero : A 0 = ⊥)
    (hTop : A (c + 1) = U)
    (hLe : ∀ n, A n ≤ U)
    (hComm : ∀ n, ⁅A (n + 1), U⁆ ≤ A n)
    (hDetect : ∀ n, n < c →
      ∀ x : U, x ∉ (A (n + 1)).subgroupOf U →
        ∃ y : U, ⁅(x : G), (y : G)⁆ ∉ A n) :
    ∀ n, n ≤ c + 1 →
      Subgroup.map U.subtype (Subgroup.upperCentralSeries U n) = A n := by
  let H : ℕ → Subgroup U := fun n => (A n).subgroupOf U
  have hHZero : H 0 = ⊥ := by
    simp [H, hZero]
  have hHTop : H (c + 1) = ⊤ := by
    simp [H, hTop]
  have hHComm : ∀ n, ⁅H (n + 1), (⊤ : Subgroup U)⁆ ≤ H n := by
    intro n
    rw [Subgroup.commutator_le]
    intro x hx y hy
    change ⁅(x : G), (y : G)⁆ ∈ A n
    have hxA : (x : G) ∈ A (n + 1) := hx
    exact (Subgroup.commutator_le.mp (hComm n))
      (x : G) hxA (y : G) y.property
  have hHDetect : ∀ n, n < c →
      ∀ x : U, x ∉ H (n + 1) →
        ∃ y : U, ⁅x, y⁆ ∉ H n := by
    intro n hn x hx
    obtain ⟨y, hy⟩ := hDetect n hn x hx
    refine ⟨y, ?_⟩
    exact hy
  have hUpper : ∀ n, n ≤ c + 1 →
      Subgroup.upperCentralSeries U n = H n := by
    intro n hn
    exact upperCentralSeries_eq_of_commutator_detection H c hHZero hHTop hHComm hHDetect n hn
  intro n hn
  rw [hUpper n hn]
  apply Subgroup.map_comap_eq_self
  simpa [H] using hLe n

open Set

section

/-- If one positive root differs from another by a nonempty sum of simple roots,
then the lower root can be extended by one of those simple roots. -/
public theorem positiveRootDifference_exists_simple_add
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsCrystallographic]
    (base : P.Base) (α γ : ι) (l : List ι)
    (hαpos : base.IsPos α) (hl : ∀ δ ∈ l, δ ∈ base.support) (hlne : l ≠ [])
    (hγ : P.root γ = P.root α + (l.map P.root).sum) :
    ∃ δ ∈ l, P.root α + P.root δ ∈ Set.range P.root := by
  classical
  induction hlen : l.length using Nat.strong_induction_on generalizing l γ with
  | h n ih =>
      let B := P.posRootForm ℤ
      let d : P.rootSpan ℤ := (l.map fun δ => P.rootSpanMem ℤ δ).sum
      have hcoe : (d : M) = (l.map P.root).sum := by
        dsimp [d]
        simp [List.map_map, Function.comp_def]
      have hdne : d ≠ 0 := by
        intro hd
        have hsumzero : (l.map P.root).sum = 0 := by
          rw [← hcoe]
          exact congrArg Subtype.val hd
        exact base.toPositiveSubsystem.sum_roots_ne_zero l
          (fun δ hδ => (base.mem_toPositiveSubsystem δ).2
            (base.isPos_of_mem_support (hl δ hδ))) hlne hsumzero
      have hdpos : 0 < B.posForm d d := P.posRootForm_posForm_pos_of_ne_zero ℤ hdne
      let rα := P.rootSpanMem ℤ α
      let rγ := P.rootSpanMem ℤ γ
      have hrγ : rγ = rα + d := by
        apply Subtype.ext
        simpa [hcoe] using hγ
      have hform : B.posForm rγ d = B.posForm rα d + B.posForm d d := by
        rw [hrγ]
        exact map_add (LinearMap.flip B.posForm d) rα d
      by_cases hneg : B.posForm rα d < 0
      · have hsum : B.posForm rα d =
            ((l.map fun δ => B.posForm rα (P.rootSpanMem ℤ δ)).sum) := by
          dsimp [d]
          simpa [List.map_map, Function.comp_def] using
            map_list_sum (B.posForm rα) (l.map fun δ => P.rootSpanMem ℤ δ)
        rw [hsum] at hneg
        obtain ⟨δ, hδl, hδneg⟩ :
            ∃ δ ∈ l, B.posForm rα (P.rootSpanMem ℤ δ) < 0 := by
          by_contra! h
          have : 0 ≤ (l.map fun δ => B.posForm rα (P.rootSpanMem ℤ δ)).sum :=
            List.sum_nonneg (by simpa using h)
          omega
        have hpairle : P.pairingIn ℤ α δ ≤ 0 :=
          (B.posForm_apply_root_root_le_zero_iff α δ).mp (le_of_lt hδneg)
        have hpairne : P.pairingIn ℤ α δ ≠ 0 := by
          intro hp
          have hformzero : B.posForm rα (P.rootSpanMem ℤ δ) = 0 := by
            apply FaithfulSMul.algebraMap_injective ℤ R
            rw [B.algebraMap_posForm, map_zero]
            exact (B.toInvariantForm.apply_root_root_zero_iff α δ).mpr (by
              rw [← P.algebraMap_pairingIn ℤ, hp, map_zero])
          omega
        have hpair : P.pairingIn ℤ α δ < 0 := lt_of_le_of_ne hpairle hpairne
        have hnotneg : P.root α ≠ -P.root δ := by
          intro hroot
          let := P.indexNeg
          have hidx : α = -δ := P.root.injective (by simpa using hroot)
          rw [hidx, RootPairing.Base.IsPos.neg_iff_not base] at hαpos
          exact hαpos (base.isPos_of_mem_support (hl δ hδl))
        exact ⟨δ, hδl, P.root_add_root_mem_of_pairingIn_neg hpair hnotneg⟩
      · have hγpos : 0 < B.posForm rγ d := by omega
        have hsum : B.posForm rγ d =
            ((l.map fun δ => B.posForm rγ (P.rootSpanMem ℤ δ)).sum) := by
          dsimp [d]
          simpa [List.map_map, Function.comp_def] using
            map_list_sum (B.posForm rγ) (l.map fun δ => P.rootSpanMem ℤ δ)
        rw [hsum] at hγpos
        obtain ⟨δ, hδl, hδpos⟩ :
            ∃ δ ∈ l, 0 < B.posForm rγ (P.rootSpanMem ℤ δ) := by
          by_contra! h
          have hnonneg : 0 ≤
              (l.map fun δ => -B.posForm rγ (P.rootSpanMem ℤ δ)).sum :=
            List.sum_nonneg (by simpa using h)
          have hsumle :
              (l.map fun δ => B.posForm rγ (P.rootSpanMem ℤ δ)).sum ≤ 0 := by
            rw [← neg_nonneg]
            calc
              -(l.map fun δ => B.posForm rγ (P.rootSpanMem ℤ δ)).sum =
                  (l.map fun δ => -B.posForm rγ (P.rootSpanMem ℤ δ)).sum := by
                rw [List.sum_neg, List.map_map]
                rfl
              _ ≥ 0 := hnonneg
          omega
        have hpair : 0 < P.pairingIn ℤ γ δ :=
          (B.zero_lt_apply_root_root_iff γ δ).mp hδpos
        have hγδ : γ ≠ δ := by
          intro hEq
          subst γ
          have herase : (l.map P.root).sum = P.root δ + ((l.erase δ).map P.root).sum := by
            exact (List.perm_cons_erase hδl |>.map P.root).sum_eq
          have hzero : (P.root α :: ((l.erase δ).map P.root)).sum = 0 := by
            simp only [List.sum_cons]
            rw [herase] at hγ
            calc
              P.root α + ((l.erase δ).map P.root).sum =
                  (P.root α + (P.root δ + ((l.erase δ).map P.root).sum)) - P.root δ := by
                abel
              _ = P.root δ - P.root δ := by rw [← hγ]
              _ = 0 := sub_self _
          exact (base.toPositiveSubsystem.sum_roots_ne_zero (α :: l.erase δ)
            (by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact (base.mem_toPositiveSubsystem x).2 hαpos
              · exact (base.mem_toPositiveSubsystem x).2
                  (base.isPos_of_mem_support (hl x (List.mem_of_mem_erase hx))))
            (by simp)) hzero
        obtain ⟨γ', hγ'⟩ := P.root_sub_root_mem_of_pairingIn_pos hpair hγδ
        let l' := l.erase δ
        have hl' : ∀ x ∈ l', x ∈ base.support := by
          intro x hx
          exact hl x (List.mem_of_mem_erase hx)
        have hlen' : l'.length < n := by
          rw [← hlen]
          have hpos : 0 < l.length := Nat.pos_of_ne_zero (by simpa using hlne)
          simpa [l', List.length_erase_of_mem hδl] using hpos
        by_cases hl'ne : l' = []
        · have hlone : l = [δ] := by
            exact (List.erase_eq_nil_iff.mp hl'ne).resolve_left hlne
          exact ⟨δ, hδl, ⟨γ, by simpa [hlone] using hγ⟩⟩
        · have hγ'' : P.root γ' = P.root α + (l'.map P.root).sum := by
            rw [hγ', hγ]
            have herase : (l.map P.root).sum = P.root δ + (l'.map P.root).sum := by
              simpa [l'] using (List.perm_cons_erase hδl |>.map P.root).sum_eq
            rw [herase]
            abel
          obtain ⟨x, hxl', hx⟩ := ih l'.length hlen' γ' l' hl' hl'ne hγ'' rfl
          exact ⟨x, List.mem_of_mem_erase hxl', hx⟩

end

section

/-- Every positive root can be extended by a sum of simple roots to a positive
root that admits no further simple-root extension. -/
public theorem exists_simpleExtension_terminal
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    (base : P.Base) (α : ι) (hαpos : base.IsPos α) :
    ∃ (γ : ι) (l : List ι), (∀ δ ∈ l, δ ∈ base.support) ∧
      P.root γ = P.root α + (l.map P.root).sum ∧ base.IsPos γ ∧
      ∀ δ ∈ base.support, P.root γ + P.root δ ∉ Set.range P.root := by
  classical
  let Reachable : Set ι := {γ | ∃ l : List ι,
    (∀ δ ∈ l, δ ∈ base.support) ∧ P.root γ = P.root α + (l.map P.root).sum}
  have hαReach : α ∈ Reachable := ⟨[], by simp, by simp⟩
  let candidates := Finset.univ.filter (· ∈ Reachable)
  have hcandidates : candidates.Nonempty := ⟨α, by simp [candidates, hαReach]⟩
  obtain ⟨γ, hγmem, hγmax⟩ := Finset.exists_max_image candidates base.height hcandidates
  have hγReach : γ ∈ Reachable := (Finset.mem_filter.mp hγmem).2
  obtain ⟨l, hl, hγ⟩ := hγReach
  have hγpos : base.IsPos γ := by
    rw [base.isPos_iff_root_mem_closure]
    rw [hγ]
    apply AddSubmonoid.add_mem
    · exact (base.isPos_iff_root_mem_closure α).mp hαpos
    · apply list_sum_mem
      intro x hx
      obtain ⟨δ, hδl, rfl⟩ := List.mem_map.mp hx
      exact AddSubmonoid.subset_closure ⟨δ, hl δ hδl, rfl⟩
  refine ⟨γ, l, hl, hγ, hγpos, ?_⟩
  intro δ hδ hsum
  obtain ⟨η, hη⟩ := hsum
  have hηReach : η ∈ Reachable := by
    refine ⟨l ++ [δ], ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hl x hx
      · rcases List.mem_singleton.mp hx with rfl
        exact hδ
    · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil, add_zero]
      rw [hη, hγ]
      abel
  have hηmem : η ∈ candidates := by simp [candidates, hηReach]
  have hheight := hγmax η hηmem
  rw [base.height_add hη, base.height_one_of_mem_support hδ] at hheight
  omega

end

section

/-- In an irreducible root system, every simple root occurs with nonzero
coefficient in a terminal positive root. -/
public theorem terminalPositiveRoot_simpleCoefficient_ne_zero
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible] (base : P.Base) (γ : ι)
    (hγpos : base.IsPos γ) (f : ι → ℕ) (hf : f.support ⊆ base.support)
    (hroot : P.root γ = ∑ δ ∈ base.support, f δ • P.root δ)
    (hterm : ∀ δ ∈ base.support, P.root γ + P.root δ ∉ Set.range P.root) :
    ∀ δ ∈ base.support, f δ ≠ 0 := by
  classical
  have hfne : f ≠ 0 := by
    intro hfzero
    apply P.ne_zero γ
    rw [hroot, hfzero]
    simp
  obtain ⟨i0, hi0⟩ : ∃ i, f i ≠ 0 := Function.ne_iff.mp hfne
  have hiSupport : i0 ∈ base.support := hf (Function.mem_support.mpr hi0)
  let ii : base.support := ⟨i0, hiSupport⟩
  let p : base.support → Prop := fun j => f j ≠ 0
  have hp0 : p ii := hi0
  have hpstep : ∀ i j : base.support, p i → base.cartanMatrix j i ≠ 0 → p j := by
    intro i j hi hj hfj
    have hpairNonneg : 0 ≤ P.pairingIn ℤ γ j := by
      by_contra h
      have hpairneg : P.pairingIn ℤ γ j < 0 := by omega
      have hnotneg : P.root γ ≠ -P.root j := by
        intro hEq
        let := P.indexNeg
        have hidx : γ = -j := P.root.injective (by simpa using hEq)
        rw [hidx, RootPairing.Base.IsPos.neg_iff_not base] at hγpos
        exact hγpos (base.isPos_of_mem_support j.property)
      exact hterm j j.property (P.root_add_root_mem_of_pairingIn_neg hpairneg hnotneg)
    have hpairEq : P.pairingIn ℤ γ j =
        ∑ k ∈ base.support, (f k : ℤ) * P.pairingIn ℤ k j := by
      apply FaithfulSMul.algebraMap_injective ℤ R
      rw [P.algebraMap_pairingIn]
      simp only [map_sum, map_mul]
      have h := congrArg (P.coroot' j) hroot
      simpa [map_sum, Nat.cast_smul_eq_nsmul, ← P.algebraMap_pairingIn ℤ] using h
    have htermle : ∀ k ∈ base.support,
        (f k : ℤ) * P.pairingIn ℤ k j ≤ 0 := by
      intro k hk
      by_cases hkj : k = j
      · subst k
        simp [hfj]
      · exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (base.pairingIn_le_zero_of_ne hkj hk j.property)
    have hijPair : P.pairingIn ℤ i j < 0 := by
      have hne : P.pairingIn ℤ i j ≠ 0 := by
        intro hzero
        have hzero' : P.pairingIn ℤ j i = 0 :=
          (P.pairingIn_eq_zero_iff (i := i) (j := j)).mp hzero
        have hzeroR : P.pairing j i = 0 := by
          rw [← P.algebraMap_pairingIn ℤ, hzero', map_zero]
        exact hj ((base.cartanMatrix_apply_eq_zero_iff_pairing).2 hzeroR)
      have hij : (i : ι) ≠ j := by
        intro hEq
        apply hi
        simpa [hEq] using hfj
      exact lt_of_le_of_ne (base.pairingIn_le_zero_of_ne hij i.property j.property) hne
    have hiTerm : (f i : ℤ) * P.pairingIn ℤ i j < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero hi) hijPair
    have hsumneg : (∑ k ∈ base.support, (f k : ℤ) * P.pairingIn ℤ k j) < 0 := by
      have hsum := Finset.sum_lt_sum (fun k hk => htermle k hk) ⟨i, i.property, hiTerm⟩
      simpa using hsum
    omega
  intro δ hδ
  exact base.induction_on_cartanMatrix p hp0 hpstep (i := ii) (j := ⟨δ, hδ⟩)

end

section

/-- An irreducible based root system has a unique terminal positive root. -/
public theorem terminalPositiveRoot_unique
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible] (base : P.Base) (α γ : ι)
    (hαpos : base.IsPos α) (hγpos : base.IsPos γ)
    (hαterm : ∀ δ ∈ base.support, P.root α + P.root δ ∉ Set.range P.root)
    (hγterm : ∀ δ ∈ base.support, P.root γ + P.root δ ∉ Set.range P.root) : α = γ := by
  classical
  let B := P.posRootForm ℤ
  obtain ⟨f, hf, hroot | hroot⟩ := base.exists_root_eq_sum_nat_or_neg γ
  swap
  · exfalso
    rw [base.isPos_iff] at hγpos
    have hh := base.height_eq_sum (f := fun j => -(f j : ℤ)) (by
      simpa [Finset.sum_neg_distrib, Nat.cast_smul_eq_nsmul] using hroot)
    have hnonneg : 0 ≤ ∑ j ∈ base.support, (f j : ℤ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    simp only [Finset.sum_neg_distrib] at hh
    omega
  have hfall := terminalPositiveRoot_simpleCoefficient_ne_zero P base γ hγpos f hf hroot hγterm
  have hpairNonneg : ∀ δ ∈ base.support, 0 ≤ P.pairingIn ℤ α δ := by
    intro δ hδ
    by_contra h
    have hneg : P.pairingIn ℤ α δ < 0 := by omega
    have hnotneg : P.root α ≠ -P.root δ := by
      intro hEq
      let := P.indexNeg
      have hidx : α = -δ := P.root.injective (by simpa using hEq)
      rw [hidx, RootPairing.Base.IsPos.neg_iff_not base] at hαpos
      exact hαpos (base.isPos_of_mem_support hδ)
    exact hαterm δ hδ (P.root_add_root_mem_of_pairingIn_neg hneg hnotneg)
  obtain ⟨δ0, hδ0, hpair0⟩ := hαpos.exists_mem_support_pos_pairingIn
  have hpair0' : 0 < P.pairingIn ℤ α δ0 := (P.zero_lt_pairingIn_iff' ℤ).mpr hpair0
  let rα := P.rootSpanMem ℤ α
  let rγ := P.rootSpanMem ℤ γ
  have hformNonneg : ∀ δ ∈ base.support, 0 ≤ B.posForm rα (P.rootSpanMem ℤ δ) := by
    intro δ hδ
    by_contra h
    have hle := (B.posForm_apply_root_root_le_zero_iff α δ).mp (le_of_lt (show B.posForm rα (P.rootSpanMem ℤ δ) < 0 by omega))
    have hpzero : P.pairingIn ℤ α δ = 0 :=
      le_antisymm hle (hpairNonneg δ hδ)
    have hne : P.pairingIn ℤ α δ ≠ 0 := by
      intro hz
      have hzform : B.posForm rα (P.rootSpanMem ℤ δ) = 0 := by
        apply FaithfulSMul.algebraMap_injective ℤ R
        rw [B.algebraMap_posForm, map_zero]
        exact (B.toInvariantForm.apply_root_root_zero_iff α δ).mpr (by rw [← P.algebraMap_pairingIn ℤ, hz, map_zero])
      omega
    exact hne hpzero
  have hform0 : 0 < B.posForm rα (P.rootSpanMem ℤ δ0) :=
    (B.zero_lt_apply_root_root_iff α δ0).2 hpair0'
  have hrγ : rγ = ∑ δ ∈ base.support, (f δ : ℤ) • P.rootSpanMem ℤ δ := by
    apply Subtype.ext
    simpa [Nat.cast_smul_eq_nsmul] using hroot
  have hformpos : 0 < B.posForm rα rγ := by
    rw [hrγ]
    simp only [map_sum, LinearMap.map_smul, smul_eq_mul]
    apply Finset.sum_pos'
    · intro δ hδ
      exact mul_nonneg (by positivity) (hformNonneg δ hδ)
    · exact ⟨δ0, hδ0, mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (hfall δ0 hδ0)) hform0⟩
  have hpairαγ : 0 < P.pairingIn ℤ α γ := (B.zero_lt_apply_root_root_iff α γ).1 hformpos
  by_contra hne
  obtain ⟨ρ, hρ⟩ := P.root_sub_root_mem_of_pairingIn_pos hpairαγ hne
  let := P.indexNeg
  rcases RootPairing.Base.IsPos.or_neg base ρ with hρpos | hnegρ
  · obtain ⟨n, g, hgSupport, hgSum, -⟩ := positiveRoot_sum_chain base hρpos
    let l := List.ofFn g
    have hl : ∀ δ ∈ l, δ ∈ base.support := by
      intro δ hδ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hδ
      exact hgSupport ⟨i, rfl⟩
    have hsum : P.root α = P.root γ + (l.map P.root).sum := by
      rw [hρ] at hgSum
      dsimp [l]
      rw [List.map_ofFn, List.sum_ofFn]
      change P.root α = P.root γ + ∑ m, P.root (g m)
      rw [← hgSum]
      abel
    obtain ⟨δ, hδl, hadd⟩ := positiveRootDifference_exists_simple_add P base γ α l hγpos hl (by
      intro hnil
      rw [hnil] at hsum
      simp at hsum
      apply hne
      apply P.root.injective
      simpa using hsum) hsum
    exact hγterm δ (hl δ hδl) hadd
  · have hnegρpos : base.IsPos (-ρ) := hnegρ
    obtain ⟨n, g, hgSupport, hgSum, -⟩ := positiveRoot_sum_chain base hnegρpos
    let l := List.ofFn g
    have hl : ∀ δ ∈ l, δ ∈ base.support := by
      intro δ hδ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hδ
      exact hgSupport ⟨i, rfl⟩
    have hsum : P.root γ = P.root α + (l.map P.root).sum := by
      dsimp [l]
      rw [List.map_ofFn, List.sum_ofFn]
      change P.root γ = P.root α + ∑ m, P.root (g m)
      rw [← hgSum]
      rw [show P.root (-ρ) = -P.root ρ by simp]
      rw [hρ]
      abel
    obtain ⟨δ, hδl, hadd⟩ := positiveRootDifference_exists_simple_add P base α γ l hαpos hl (by
      intro hnil
      apply hne
      have : γ = α := P.root.injective (by simpa [hnil] using hsum)
      exact this.symm) hsum
    exact hαterm δ (hl δ hδl) hadd

end

open Set

section

private lemma rootIndex_nonempty_of_isRootSystem_isIrreducible_general
    {ι R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsIrreducible] :
    Nonempty ι := by
  have : Nontrivial M := RootPairing.IsIrreducible.nontrivial P
  by_contra hnonempty
  have hrange : Set.range P.root = ∅ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (hnonempty ⟨i⟩).elim
    · simp
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hxspan : x ∈ Submodule.span R (Set.range P.root) := by
    rw [RootPairing.IsRootSystem.span_root_eq_top (P := P)]
    exact Submodule.mem_top
  rw [hrange, Submodule.span_empty] at hxspan
  exact hx hxspan

private lemma heightMaximum_isPos_general
    {ι R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (base : P.Base) [CharZero R]
    {highest : ι} (hmax : ∀ α, base.height α ≤ base.height highest) :
    base.IsPos highest := by
  let : Nonempty ι := ⟨highest⟩
  obtain ⟨j, hj⟩ := base.support_nonempty
  rw [base.isPos_iff]
  have h := hmax j
  rw [base.height_one_of_mem_support hj] at h
  omega

private lemma heightMaximum_isTerminal_general
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (base : P.Base) {highest : ι}
    (hmax : ∀ α, base.height α ≤ base.height highest) :
    ∀ δ ∈ base.support, P.root highest + P.root δ ∉ Set.range P.root := by
  intro δ hδ hsum
  obtain ⟨η, hη⟩ := hsum
  have hηheight := base.height_add hη
  have hmaxη := hmax η
  rw [hηheight, base.height_one_of_mem_support hδ] at hmaxη
  omega

private lemma heightMinimum_unique_general
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible] (base : P.Base)
    {lowest lowest' : ι}
    (hmin : ∀ α, base.height lowest ≤ base.height α)
    (hmin' : ∀ α, base.height lowest' ≤ base.height α) :
    lowest' = lowest := by
  let := P.indexNeg
  have hmax : ∀ α, base.height α ≤ base.height (-lowest) := by
    intro α
    have h := hmin (-α)
    have hnegα := base.height_reflectionPerm_self α
    have hneglow := base.height_reflectionPerm_self lowest
    change base.height (-α) = -base.height α at hnegα
    change base.height (-lowest) = -base.height lowest at hneglow
    omega
  have hmax' : ∀ α, base.height α ≤ base.height (-lowest') := by
    intro α
    have h := hmin' (-α)
    have hnegα := base.height_reflectionPerm_self α
    have hneglow := base.height_reflectionPerm_self lowest'
    change base.height (-α) = -base.height α at hnegα
    change base.height (-lowest') = -base.height lowest' at hneglow
    omega
  have hneg : -lowest' = -lowest := by
    exact terminalPositiveRoot_unique P base (-lowest') (-lowest)
      (heightMaximum_isPos_general base hmax')
      (heightMaximum_isPos_general base hmax)
      (heightMaximum_isTerminal_general base hmax')
      (heightMaximum_isTerminal_general base hmax)
  exact neg_injective hneg

/-- In a finite irreducible reduced crystallographic root system, height
relative to a base has a unique maximum. -/
public theorem RootPairing.Base.existsUnique_heightMaximum
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible] (base : P.Base) :
    ∃! highest : ι, ∀ α, base.height α ≤ base.height highest := by
  let : Nonempty ι := rootIndex_nonempty_of_isRootSystem_isIrreducible_general
    (P := P)
  obtain ⟨highest, hhighest⟩ := Finite.exists_max base.height
  have hhighestPos : base.IsPos highest := heightMaximum_isPos_general base hhighest
  have hhighestTerm : ∀ δ ∈ base.support,
      P.root highest + P.root δ ∉ Set.range P.root :=
    heightMaximum_isTerminal_general base hhighest
  have hhighestUnique : ∀ y, (∀ α, base.height α ≤ base.height y) → y = highest := by
    intro y hy
    exact terminalPositiveRoot_unique P base y highest
      (heightMaximum_isPos_general base hy) hhighestPos
      (heightMaximum_isTerminal_general base hy) hhighestTerm
  exact ⟨highest, hhighest, hhighestUnique⟩

/-- In a finite irreducible reduced crystallographic root system, height
relative to a base has a unique minimum. -/
public theorem RootPairing.Base.existsUnique_heightMinimum
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible] (base : P.Base) :
    ∃! lowest : ι, ∀ α, base.height lowest ≤ base.height α := by
  let : Nonempty ι := rootIndex_nonempty_of_isRootSystem_isIrreducible_general
    (P := P)
  obtain ⟨lowest, hlowest⟩ := Finite.exists_min base.height
  have hlowestUnique : ∀ y, (∀ α, base.height y ≤ base.height α) → y = lowest := by
    intro y hy
    exact (heightMinimum_unique_general (base := base) (lowest := y)
      (lowest' := lowest) hy hlowest).symm
  exact ⟨lowest, hlowest, hlowestUnique⟩

end
end Theory.AlgebraicGroup

