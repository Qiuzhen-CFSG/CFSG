module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.ChevalleySource.Basic
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.ChevalleySource.RootGeometry
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RootPairsSource

/-!
# Commutators of the actual Spin D4 root points

Equal root lengths force every positive mixed root of two independent roots
to have coefficients (1,1). The existing native root exchange law therefore
gives the full ordered Chevalley commutator formula, with its literal maps and
coefficient convention. Source: GLS3 1.12.1(e).
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.SimplyConnected.Pinning.ChevalleySource
noncomputable section
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

private theorem valid_coefficients (r s : ULift.{u} RootIndex)
    (hli : AreLinearlyIndependentRoots (pinnedRootData k) (typeDRootPairing 2) Equiv.ulift r s)
    (q : ChevalleyCommutatorTerm (ULift.{u} RootIndex))
    (hq : IsValidChevalleyCommutatorTerm (pinnedRootData k) (typeDRootPairing 2) Equiv.ulift r s q) :
    q.i = 1 ∧ q.j = 1 :=
  mixed_root_coefficients r.down s.down q.root.down q.i q.j hq.1 hq.2.1
    (LinearIndependent.pair_iff.mpr hli) hq.2.2

private theorem expected_one (r s : ULift.{u} RootIndex)
    (hli : AreLinearlyIndependentRoots (pinnedRootData k) (typeDRootPairing 2) Equiv.ulift r s)
    (q : ChevalleyCommutatorTerm (ULift.{u} RootIndex)) :
    HasExpectedChevalleyCoefficient (pinnedRootData k) (typeDRootPairing 2) Equiv.ulift r s q (1:k) := by
  have htwo : ¬ IsChevalleyCoefficientExceptionalTwo (pinnedRootData k) (typeDRootPairing 2) Equiv.ulift r s q := by
    rintro ⟨hq, h | h | h⟩
    · have he := root_squaredLength_equal q.root.down r.down
      have hn : RootSquaredLength (typeDRootPairing 2) r.down ≠ 0 := by
        classical
        exact RootPairing.IsAnisotropic.rootForm_root_ne_zero _
      have heq := h.2.2.2
      change RootSquaredLength (typeDRootPairing 2) q.root.down = _ * RootSquaredLength (typeDRootPairing 2) r.down at heq
      exact hn (by linarith)
    · obtain ⟨v,hv,he⟩ := h.2.2.2.2
      have hc := valid_coefficients k r s hli v hv
      rcases he with he|he <;> omega
    · have hc := valid_coefficients k r s hli q hq
      omega
  have hthree : ¬ IsChevalleyCoefficientExceptionalThree (pinnedRootData k) (typeDRootPairing 2) Equiv.ulift r s q := by
    rintro ⟨hq,h|h⟩
    · have he := root_squaredLength_equal q.root.down r.down
      have hn : RootSquaredLength (typeDRootPairing 2) r.down ≠ 0 := by
        classical
        exact RootPairing.IsAnisotropic.rootForm_root_ne_zero _
      have heq := h.2.2.2
      change RootSquaredLength (typeDRootPairing 2) q.root.down = _ * RootSquaredLength (typeDRootPairing 2) r.down at heq
      exact hn (by linarith)
    · have hc := valid_coefficients k r s hli q hq
      rcases h.1 with h|h <;> omega
  exact ⟨fun h => (htwo h).elim, fun h => (hthree h).elim, fun _ _ => Or.inl rfl⟩

private theorem sum_commutes_left (r s t : RootIndex)
    (hli : LinearIndependent ℝ ![(typeDRootPairing 2).root r, (typeDRootPairing 2).root s])
    (ht : (typeDRootPairing 2).root t = (typeDRootPairing 2).root r + (typeDRootPairing 2).root s) (a b : k) :
    Commute (rootPoint k r a) (rootPoint k t b) := by
  apply RootPairs.rootPoint_commute k
  · intro hneg
    have he := congrArg (typeDRootPairing 2).root hneg
    rw [root_negativeRoot, ht] at he
    have hbad : (2:ℝ) • (typeDRootPairing 2).root r + (1:ℝ) • (typeDRootPairing 2).root s = 0 := by
      rw [one_smul, two_smul, add_assoc, he, add_neg_cancel]
    have hh := (LinearIndependent.pair_iff.mp hli) 2 1 hbad
    norm_num at hh
  · rintro ⟨v,hv⟩
    have hv' : (typeDRootPairing 2).root v = (2:ℝ) • (typeDRootPairing 2).root r + (1:ℝ) • (typeDRootPairing 2).root s := by
      rw [hv, ht, two_smul, one_smul, add_assoc]
    have hc := mixed_root_coefficients r s v 2 1 (by decide) (by decide) hli (by simpa only [Nat.cast_ofNat, Nat.cast_one] using hv')
    norm_num at hc

private theorem sum_commutator (r s t : RootIndex)
    (hli : LinearIndependent ℝ ![(typeDRootPairing 2).root r, (typeDRootPairing 2).root s])
    (ht : (typeDRootPairing 2).root t = (typeDRootPairing 2).root r + (typeDRootPairing 2).root s) (a b : k) :
    (rootPoint k r a)⁻¹ * (rootPoint k s b)⁻¹ * rootPoint k r a * rootPoint k s b =
      rootPoint k t (a*b) := by
  have hx := RootPairs.rootPoint_exchange k r s t ht a b
  have hc := sum_commutes_left k r s t hli ht a (a*b)
  calc
    _ = (rootPoint k r a)⁻¹ * (rootPoint k s b)⁻¹ *
        (rootPoint k r a * rootPoint k s b) := by group
    _ = (rootPoint k r a)⁻¹ * (rootPoint k s b)⁻¹ *
        (rootPoint k s b * rootPoint k t (a*b) * rootPoint k r a) := by rw [hx]
    _ = (rootPoint k r a)⁻¹ * rootPoint k t (a*b) * rootPoint k r a := by group
    _ = rootPoint k t (a*b) := by rw [hc.inv_left.eq]; group

public theorem commutator_formula (r s : ULift.{u} RootIndex)
    (hli : AreLinearlyIndependentRoots (pinnedRootData k) (typeDRootPairing 2) Equiv.ulift r s) :
    ∃ order : List (ChevalleyCommutatorTerm (ULift.{u} RootIndex)),
    ∃ c : ChevalleyCommutatorTerm (ULift.{u} RootIndex) → k,
      order.Nodup ∧ order.Pairwise (fun q v => q.i+q.j ≤ v.i+v.j) ∧
      (∀q, q ∈ order ↔ IsValidChevalleyCommutatorTerm (pinnedRootData k) (typeDRootPairing 2) Equiv.ulift r s q) ∧
      (∀q ∈ order, HasExpectedChevalleyCoefficient (pinnedRootData k) (typeDRootPairing 2) Equiv.ulift r s q (c q)) ∧
      ∀a b, ((data k).x r a)⁻¹ * ((data k).x s b)⁻¹ * (data k).x r a * (data k).x s b =
        (order.map fun q => (data k).x q.root (c q * a^q.i * b^q.j)).prod := by
  classical
  by_cases hs : ∃t : RootIndex, (typeDRootPairing 2).root t = (typeDRootPairing 2).root r.down + (typeDRootPairing 2).root s.down
  · obtain ⟨t,ht⟩ := hs
    let q : ChevalleyCommutatorTerm (ULift.{u} RootIndex) := ⟨1,1,ULift.up t⟩
    refine ⟨[q], fun _ => 1, by simp, by simp, ?_, ?_, ?_⟩
    · intro v
      simp only [List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨by dsimp [q]; decide, by dsimp [q]; decide, by
          change (typeDRootPairing 2).root t = ((1:ℕ):ℝ) • (typeDRootPairing 2).root r.down + ((1:ℕ):ℝ) • (typeDRootPairing 2).root s.down
          simpa only [Nat.cast_one, one_smul] using ht⟩
      · intro hv
        obtain ⟨hi,hj⟩ := valid_coefficients k r s hli v hv
        have he : v.root = ULift.up t := by
          apply ULift.ext
          apply (typeDRootPairing 2).root.injective
          have hvv := hv.2.2
          change (typeDRootPairing 2).root v.root.down = (v.i:ℝ) • (typeDRootPairing 2).root r.down + (v.j:ℝ) • (typeDRootPairing 2).root s.down at hvv
          have hv' : (typeDRootPairing 2).root v.root.down = (typeDRootPairing 2).root r.down + (typeDRootPairing 2).root s.down := by
            simpa only [hi,hj,Nat.cast_one,one_smul] using hvv
          exact hv'.trans ht.symm
        cases v
        simp_all [q]
    · intro v hv
      exact expected_one k r s hli v
    · intro a b
      simpa only [data, List.map_singleton,List.prod_singleton, q, one_mul, pow_one]
        using sum_commutator k r.down s.down t (LinearIndependent.pair_iff.mpr hli) ht a b
  · refine ⟨[],fun _=>1, by simp, by simp, ?_, by simp, ?_⟩
    · intro q
      simp only [List.not_mem_nil, false_iff]
      intro hq
      obtain ⟨hi,hj⟩ := valid_coefficients k r s hli q hq
      have hvv := hq.2.2
      change (typeDRootPairing 2).root q.root.down = (q.i:ℝ) • (typeDRootPairing 2).root r.down + (q.j:ℝ) • (typeDRootPairing 2).root s.down at hvv
      exact hs ⟨q.root.down, by simpa only [hi,hj,Nat.cast_one,one_smul] using hvv⟩
    · intro a b
      have hop : s.down ≠ negativeRoot r.down := by
        intro he
        have hbad : (1:ℝ) • (typeDRootPairing 2).root r.down + (1:ℝ) • (typeDRootPairing 2).root s.down = 0 := by
          rw [one_smul,one_smul,he,root_negativeRoot,add_neg_cancel]
        have hh := hli 1 1 hbad
        norm_num at hh
      have hc := RootPairs.rootPoint_commute k r.down s.down hop hs a b
      simp only [List.map_nil,List.prod_nil]
      change (rootPoint k r.down a)⁻¹ * (rootPoint k s.down b)⁻¹ *
        rootPoint k r.down a * rootPoint k s.down b = 1
      calc
        _ = (rootPoint k s.down b)⁻¹ * (rootPoint k r.down a)⁻¹ * rootPoint k r.down a * rootPoint k s.down b := by rw [hc.inv_inv.eq]
        _ = 1 := by group
end
end Triality.SimplyConnected.Pinning.ChevalleySource
