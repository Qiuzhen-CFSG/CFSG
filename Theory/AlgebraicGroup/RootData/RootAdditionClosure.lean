module

public import Theory.AlgebraicGroup.RootData.Realization
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
This module converts additive support among realized root characters into
binary addition of realized roots.  `RootAdditionClosure D S` is the least
predicate containing `S` and closed under every value of `D.add`.

For a finite reduced crystallographic integral root pairing realizing `D`, a
list of roots whose sum is a root can be reordered into such binary additions.
Pair the list sum with the target coroot: some summand has positive pairing
with the target.  Unless that summand is already the target, the root-string
lemma makes their difference a root.  Erasing the summand then gives a shorter
list and the induction continues.  Thus zero-sum subcollections, including
opposite pairs, are discarded without a positivity assumption on the
generators.  Applying this argument to a list witnessing membership in a
character submonoid gives the main support theorem.

The integral roots need not span the full character lattice, so the argument
uses finiteness and crystallographic root strings rather than an integral
`RootPairing.IsRootSystem` instance.  This is the combinatorial bridge needed
by the generated-root support argument underlying GLS3 Theorem 1.11.2; the
initial closure and positive-height interfaces were developed in
`Scratch/ag-rootsystems-generated-root-addition-support/root/Closure.lean`.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The least predicate containing `S` and closed under every realized value
of `D.add`. -/
public inductive RootAdditionClosure
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (S : Set D.Root) : D.Root -> Prop
  | of_mem {alpha : D.Root} (halpha : alpha ∈ S) :
      RootAdditionClosure D S alpha
  | add {alpha beta gamma : D.Root}
      (halpha : RootAdditionClosure D S alpha)
      (hbeta : RootAdditionClosure D S beta)
      (hadd : D.add alpha beta = some gamma) :
      RootAdditionClosure D S gamma

/-- The generators belong to their root-addition closure. -/
public lemma rootAdditionClosure_mono_generators
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (S : Set D.Root) :
    S ⊆ {alpha | RootAdditionClosure D S alpha} := by
  intro alpha halpha
  exact RootAdditionClosure.of_mem halpha

/-- The root-addition closure is closed under every defined addition. -/
public lemma rootAdditionClosure_add
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (S : Set D.Root)
    {alpha beta gamma : D.Root}
    (halpha : RootAdditionClosure D S alpha)
    (hbeta : RootAdditionClosure D S beta)
    (hadd : D.add alpha beta = some gamma) :
    RootAdditionClosure D S gamma :=
  RootAdditionClosure.add halpha hbeta hadd

/-- Minimality of `RootAdditionClosure` among root sets containing `S` and
closed under `D.add`. -/
public theorem rootAdditionClosure_minimal
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (S A : Set D.Root)
    (hS : S ⊆ A)
    (hA : forall alpha, alpha ∈ A -> forall beta, beta ∈ A ->
      forall gamma, D.add alpha beta = some gamma -> gamma ∈ A) :
    {alpha | RootAdditionClosure D S alpha} ⊆ A := by
  intro alpha halpha
  induction halpha with
  | of_mem halpha => exact hS halpha
  | add halpha hbeta hadd ihAlpha ihBeta =>
      exact hA _ ihAlpha _ ihBeta _ hadd

private lemma exists_root_list_of_weight_list
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (S : Set D.Root) (weights : List (TorusWeight T))
    (hweights : forall chi, chi ∈ weights -> chi ∈ D.rootWeight '' S) :
    ∃ roots : List D.Root,
      (forall delta, delta ∈ roots -> delta ∈ S) ∧
        roots.map D.rootWeight = weights := by
  classical
  induction weights with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons chi weights ih =>
      obtain ⟨delta, hdeltaS, hdelta⟩ := hweights chi (by simp)
      obtain ⟨roots, hrootsS, hroots⟩ := ih (by
        intro psi hpsi
        exact hweights psi (by simp [hpsi]))
      refine ⟨delta :: roots, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdeltaS
        · exact hrootsS x hx
      · simp [hdelta, hroots]

/-- A finite list of allowed roots whose sum is a root can be combined by
successive realized binary root additions. -/
public theorem rootAdditionClosure_of_root_sum
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (hAdd : D.IsRootAdditionComplete)
    {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (hDatum : IsRootDatumRealization D P e weightEquiv)
    (S : Set D.Root) (roots : List D.Root) (gamma : D.Root)
    (hroots : forall delta, delta ∈ roots -> delta ∈ S)
    (hsum : P.root (e gamma) =
      (roots.map fun delta => P.root (e delta)).sum) :
    RootAdditionClosure D S gamma := by
  classical
  let _ := Fintype.ofFinite ι
  induction hlen : roots.length using Nat.strong_induction_on generalizing roots gamma with
  | h n ih =>
      have hpairSum : (2 : ℤ) =
          (roots.map fun delta => P.pairingIn ℤ (e delta) (e gamma)).sum := by
        calc
          (2 : ℤ) = P.coroot' (e gamma) (P.root (e gamma)) := by simp
          _ = P.coroot' (e gamma)
              ((roots.map fun delta => P.root (e delta)).sum) :=
            congrArg (P.coroot' (e gamma)) hsum
          _ = (roots.map fun delta =>
              P.pairingIn ℤ (e delta) (e gamma)).sum := by
            rw [map_list_sum]
            simp [List.map_map, Function.comp_def, ← P.algebraMap_pairingIn ℤ]
      obtain ⟨delta, hdelta, hpair⟩ :
          ∃ delta ∈ roots, 0 < P.pairingIn ℤ (e delta) (e gamma) := by
        by_contra! hall
        have hnonneg : 0 ≤
            (roots.map fun delta =>
              -P.pairingIn ℤ (e delta) (e gamma)).sum :=
          List.sum_nonneg (by simpa using hall)
        have hsumle :
            (roots.map fun delta => P.pairingIn ℤ (e delta) (e gamma)).sum ≤ 0 := by
          rw [← neg_nonneg]
          calc
            -(roots.map fun delta =>
                P.pairingIn ℤ (e delta) (e gamma)).sum =
                (roots.map fun delta =>
                  -P.pairingIn ℤ (e delta) (e gamma)).sum := by
              rw [List.sum_neg, List.map_map]
              rfl
            _ ≥ 0 := hnonneg
        omega
      by_cases hgammaDelta : e gamma = e delta
      · have : gamma = delta := e.injective hgammaDelta
        subst gamma
        exact RootAdditionClosure.of_mem (hroots delta hdelta)
      · have hpair' : 0 < P.pairingIn ℤ (e gamma) (e delta) :=
          (P.zero_lt_pairingIn_iff (P.posRootForm ℤ) (e delta) (e gamma)).mp hpair
        obtain ⟨etaIndex, hetaIndex⟩ :=
          P.root_sub_root_mem_of_pairingIn_pos hpair' hgammaDelta
        let eta : D.Root := e.symm etaIndex
        have heta : P.root (e eta) = P.root (e gamma) - P.root (e delta) := by
          simpa [eta] using hetaIndex
        let shorter := roots.erase delta
        have hshorterRoots : forall x, x ∈ shorter -> x ∈ S := by
          intro x hx
          exact hroots x (List.mem_of_mem_erase hx)
        have herase :
            (roots.map fun x => P.root (e x)).sum =
              P.root (e delta) + (shorter.map fun x => P.root (e x)).sum := by
          simpa [shorter] using
            (List.perm_cons_erase hdelta |>.map (fun x => P.root (e x))).sum_eq
        have hshorterSum : P.root (e eta) =
            (shorter.map fun x => P.root (e x)).sum := by
          rw [heta, hsum, herase]
          abel
        have hshorterLength : shorter.length < n := by
          rw [← hlen]
          simpa [shorter, List.length_erase_of_mem hdelta] using
            (List.length_pos_of_mem hdelta)
        have hetaClosure : RootAdditionClosure D S eta :=
          ih shorter.length hshorterLength shorter eta hshorterRoots hshorterSum rfl
        have hrootAdd : P.root (e gamma) = P.root (e eta) + P.root (e delta) := by
          rw [heta]
          abel
        have hadd : D.add eta delta = some gamma := by
          apply hAdd
          rw [← hDatum gamma, ← hDatum eta, ← hDatum delta,
            ← map_mul, ← ofAdd_add, hrootAdd]
        exact RootAdditionClosure.add hetaClosure
          (RootAdditionClosure.of_mem (hroots delta hdelta)) hadd

/-- Character-monoid support of an actual root is equivalent to a finite root
sum, hence forces membership in the least realized binary-addition closure. -/
public theorem IsActualBasedRootDatum.rootAdditionClosure_of_rootWeight_mem_closure
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (hAdd : D.IsRootAdditionComplete)
    {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (positiveRoots : Set D.Root)
    (hActual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (S : Set D.Root) (alpha : D.Root)
    (halpha : D.rootWeight alpha ∈ Submonoid.closure (D.rootWeight '' S)) :
    RootAdditionClosure D S alpha := by
  classical
  obtain ⟨weights, hweights, hweightProd⟩ :=
    Submonoid.exists_list_of_mem_closure halpha
  obtain ⟨roots, hrootsS, hrootWeights⟩ :=
    exists_root_list_of_weight_list D S weights hweights
  have hweightProd' : (roots.map D.rootWeight).prod = D.rootWeight alpha := by
    rw [hrootWeights]
    exact hweightProd
  have hofAdd :
      Multiplicative.ofAdd ((roots.map fun delta => P.root (e delta)).sum) =
        (roots.map fun delta =>
          Multiplicative.ofAdd (P.root (e delta))).prod := by
    clear hrootsS hrootWeights hweightProd'
    induction roots with
    | nil => simp
    | cons delta roots ih => simp [ih]
  have hsum : P.root (e alpha) =
      (roots.map fun delta => P.root (e delta)).sum := by
    apply Multiplicative.ofAdd.injective
    apply weightEquiv.injective
    calc
      weightEquiv (Multiplicative.ofAdd (P.root (e alpha))) =
          D.rootWeight alpha := hActual.2.1 alpha
      _ = (roots.map D.rootWeight).prod := hweightProd'.symm
      _ = (roots.map fun delta =>
          weightEquiv (Multiplicative.ofAdd (P.root (e delta)))).prod := by
            congr 1
            apply List.map_congr_left
            intro delta hdelta
            exact (hActual.2.1 delta).symm
      _ = weightEquiv ((roots.map fun delta =>
          Multiplicative.ofAdd (P.root (e delta))).prod) := by
            simpa [List.map_map, Function.comp_def] using
              (map_list_prod weightEquiv (roots.map fun delta =>
                Multiplicative.ofAdd (P.root (e delta)))).symm
      _ = weightEquiv (Multiplicative.ofAdd
          ((roots.map fun delta => P.root (e delta)).sum)) := by rw [hofAdd]
  exact rootAdditionClosure_of_root_sum D hAdd P e weightEquiv hActual.2.1
    S roots alpha hrootsS hsum

/-- Every root in the addition closure of the realized positive roots has
positive height. -/
public theorem RootGroupData.IsRealization.rootAdditionClosure_positive_height
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization)
    {alpha : D.Root} (halpha : RootAdditionClosure D D.positive alpha) :
    0 < D.height alpha := by
  have haddHeight := hD.2.2.2.2.2.2.2.2.2.1
  have hpositive := hD.2.2.2.2.2.2.2.2.2.2.1
  induction halpha with
  | of_mem halpha =>
      rw [hpositive] at halpha
      exact halpha
  | add halpha hbeta hadd ihAlpha ihBeta =>
      rw [haddHeight _ _ _ hadd]
      omega

end Theory.AlgebraicGroup
