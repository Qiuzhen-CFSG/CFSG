module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.NormalizingActor

/-!
# Eliminating a central coprime action kernel

Suppose a finite group acts faithfully on an abelian group `V`. Let
`Q≤W=[W,S]`, with `Q` centralizing `W` and `S`, and with order coprime
to `|V|`. If `Q` fixes `[V,S]` pointwise, then `Q` is trivial.

Commuting the two actions in the fixed-displacement identity shows that
`S` fixes `[V,Q]`. This subgroup is `W`-invariant because `W` normalizes
`Q`, so `W=[W,S]` fixes it as well. Thus `Q` fixes its own commutator
subgroup; coprime commutator idempotence makes that subgroup trivial.
Faithfulness then eliminates `Q`.

This is the last odd-kernel elimination step of Stellmacher (1.6),
journal p.18; see `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative commutatorElement

universe u

public theorem eq_bot_of_central_coprime_fixing_commutator
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (W S Q : Subgroup G) (hQW : Q ≤ W) (hW : W = ⁅W, S⁆)
    (hQcommW : ⁅Q, W⁆ = ⊥) (hQcommS : ⁅Q, S⁆ = ⊥)
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card V))
    (hfix : Q ≤ fixingSubgroup G (commutatorAction S V : Set V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) : Q = ⊥ := by
  let M := commutatorAction Q V
  have hQS (q : Q) (s : S) : (s : G) * (q : G) = (q : G) * (s : G) :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQcommS q.property) s s.property
  have hSfixM : M ≤ FixedPoints.subgroup S V := by
    change commutatorAction Q V ≤ FixedPoints.subgroup S V
    rw [commutatorAction_eq_closure]
    apply (Subgroup.closure_le (K := FixedPoints.subgroup S V)).mpr
    rintro z ⟨q, v, rfl⟩ s
    have hdmem : v⁻¹ * (s • v) ∈ commutatorAction S V := by
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨s, v, rfl⟩
    have hd := (mem_fixingSubgroup_iff (M := G) (s := (commutatorAction S V : Set V))).mp
      (hfix q.property) _ hdmem
    have hcomm : q • (s • v) = s • (q • v) := by
      change (q : G) • ((s : G) • v) = (s : G) • ((q : G) • v)
      rw [← mul_smul, ← mul_smul, hQS]
    rw [smul_mul', smul_inv'] at hd
    change (q • v)⁻¹ * (q • (s • v)) = v⁻¹ * (s • v) at hd
    rw [hcomm] at hd
    have heq : s • (q • v) = (q • v) * (v⁻¹ * (s • v)) :=
      inv_mul_eq_iff_eq_mul.mp hd
    rw [smul_mul', smul_inv', heq]
    calc
      (s • v)⁻¹ * ((q • v) * (v⁻¹ * (s • v))) =
          ((s • v)⁻¹ * (s • v)) * (v⁻¹ * (q • v)) := by ac_rfl
      _ = v⁻¹ * (q • v) := by simp
  have hWnormQ : W ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQcommW)).trans
        (Subgroup.centralizer_le_normalizer (Q : Set G))
  let _ : IsInvariant W V M := commutatorAction_isInvariant_of_normalizing_actor W Q hWnormQ
  have hSfix : S ≤ fixingSubgroup G (M : Set V) := by
    intro s hs
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact hSfixM hv ⟨s, hs⟩
  have hWfix : W ≤ fixingSubgroup G (M : Set V) := by
    rw [hW]
    apply Subgroup.commutator_le.mpr
    intro w hw s hs
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hsfix := (mem_fixingSubgroup_iff (M := G) (s := (M : Set V))).mp (hSfix hs)
    have hsinvfix := (mem_fixingSubgroup_iff (M := G) (s := (M : Set V))).mp
      (hSfix (S.inv_mem hs))
    have hinv : w⁻¹ • v ∈ M :=
      (IsInvariant.invariant (A := W) (G := V) (H := M) (⟨w, hw⟩ : W)⁻¹ v).mp hv
    simp only [commutatorElement_def, mul_smul]
    rw [hsinvfix v hv, hsfix _ hinv, smul_inv_smul]
  have hQfixM : Q ≤ fixingSubgroup G (M : Set V) := hQW.trans hWfix
  have hcomm2 : commutatorAction₂ Q V = ⊥ := by
    apply le_antisymm _ bot_le
    apply (Subgroup.closure_le (K := (⊥ : Subgroup V))).mpr
    rintro z ⟨q, v, hv, rfl⟩
    have hqv := (mem_fixingSubgroup_iff (M := G) (s := (M : Set V))).mp
      (hQfixM q.property) v hv
    change v⁻¹ * ((q : G) • v) = 1
    rw [hqv, inv_mul_cancel]
  have hMbot : M = ⊥ := by
    have hidem := commutatorAction₂_eq_commutatorAction_of_solvable_coprime
      (G := V) (A := Q)
      (Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y) hcop
    exact hidem.symm.trans hcomm2
  apply le_antisymm _ bot_le
  intro q hq
  have hqfix : q ∈ fixingSubgroup G (Set.univ : Set V) := by
    rw [mem_fixingSubgroup_iff]
    intro v _
    have hd : v⁻¹ * (q • v) ∈ M := by
      change v⁻¹ * (q • v) ∈ commutatorAction Q V
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨q, hq⟩, v, rfl⟩
    have hd1 : v⁻¹ * (q • v) = 1 := hMbot.le hd
    exact (inv_mul_eq_one.mp hd1).symm
  rwa [hfaith] at hqfix

