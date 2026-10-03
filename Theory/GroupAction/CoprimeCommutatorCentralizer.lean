module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Mathlib.Tactic

/-!
# A coprime actor fixing another actor's commutator

Suppose `P,Q ≤ G` act faithfully on a finite abelian group `V`, with `|Q|`
coprime to `|V|`. If `[V,Q]` is `P`-invariant and `Q` fixes `[V,P]`
pointwise, then `P` and `Q` commute.

Coprime splitting gives `V=C_V(Q)×[V,Q]`. Each `P`-action commutator on
`[V,Q]` lies in both complementary subgroups and is trivial. For a vector
fixed by `Q`, the fixedness of its `P`-action commutator shows that its
`P`-image is still fixed by `Q`. The actors thus commute on both summands;
faithfulness turns equality of their actions into equality in `G`.

This is the coprime transfer used to centralize the odd action kernel in
Stellmacher (1.6), journal p.18, after proving `[V,S]≤U`;
see `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative

public theorem commutator_eq_bot_of_coprime_fixing_action_commutator
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (P Q : Subgroup G)
    [IsInvariant P V (commutatorAction Q V)]
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card V))
    (hfix : Q ≤ fixingSubgroup G (commutatorAction P V : Set V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    ⁅P, Q⁆ = ⊥ := by
  let C : Subgroup V := FixedPoints.subgroup Q V
  let M : Subgroup V := commutatorAction Q V
  have hcompl : IsCompl C M :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := Q)
      (Group.isSolvable_of_comm (fun x y => IsMulCommutative.is_comm.comm x y))
      hcop inferInstance
  have hdelta (p : P) (v : V) : v⁻¹ * (p • v) ∈ commutatorAction P V := by
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨p, v, rfl⟩
  have hQdelta (p : P) (q : Q) (v : V) :
      q • (v⁻¹ * (p • v)) = v⁻¹ * (p • v) := by
    exact (mem_fixingSubgroup_iff (M := G) (s := (commutatorAction P V : Set V))).mp
      (hfix q.property) _ (hdelta p v)
  have hPfixM (p : P) (v : V) (hv : v ∈ M) : p • v = v := by
    have hdC : v⁻¹ * (p • v) ∈ C := by
      rw [FixedPoints.mem_subgroup]
      exact fun q => hQdelta p q v
    have hdM : v⁻¹ * (p • v) ∈ M := M.mul_mem (M.inv_mem hv)
      ((IsInvariant.invariant (A := P) (G := V) (H := M) p v).mp hv)
    have hd1 : v⁻¹ * (p • v) = 1 := hcompl.disjoint.le_bot ⟨hdC, hdM⟩
    exact (inv_mul_eq_one.mp hd1).symm
  have hQfixPC (p : P) (q : Q) (v : V) (hv : v ∈ C) :
      q • (p • v) = p • v := by
    have hqv : q • v = v := (FixedPoints.mem_subgroup (M := Q) (α := V) (a := v)).mp hv q
    have hd := hQdelta p q v
    rw [smul_mul', smul_inv', hqv] at hd
    exact mul_left_cancel hd
  have hρinj : Function.Injective (MulDistribMulAction.toMulAut G V) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← fixingSubgroup_univ_eq_ker_toMulAut]
    exact hfaith
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  let pP : P := ⟨p, hp⟩
  let qQ : Q := ⟨q, hq⟩
  apply hρinj
  ext v
  change (q * p) • v = (p * q) • v
  simp only [mul_smul]
  have hvCM : v ∈ C ⊔ M := by rw [hcompl.sup_eq_top]; exact Subgroup.mem_top v
  let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
  obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hvCM
  have hqc : q • c = c := (FixedPoints.mem_subgroup (M := Q) (α := V) (a := c)).mp hc qQ
  have hpw : p • w = w := hPfixM pP w hw
  have hqpc : q • (p • c) = p • c := hQfixPC pP qQ c hc
  have hqwM : q • w ∈ M := by
    let _ : IsInvariant Q V M := commutatorAction_isInvariant
    exact (IsInvariant.invariant (A := Q) (G := V) (H := M) qQ w).mp hw
  have hpqw : p • (q • w) = q • w := hPfixM pP (q • w) hqwM
  simp only [smul_mul', hpw, hqc, hqpc, hpqw]

