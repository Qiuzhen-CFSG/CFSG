module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates

/-!
# The change of lambda in Held's local coordinates

The sign of the action on the four pairs defines a binary character of the
actual centralizer H. Multiplying odd elements by the central involution pi
is an involutory automorphism. It fixes seven displayed generators and sends
lambda to pi*lambda. The pair action is checked using the 384 normal forms;
no abstract presentation or ambient recognition is assumed.

Composing the supplied centralizer isomorphism with this automorphism changes
lambda as in Held Lemma 2.5 while preserving the originally specified mu.
The existence of coordinates with pi not conjugate to lambda is conditional
on the precise nonfusion conclusion of Lemma 2.4, which remains to be proved.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Section 1 and Lemmas 2.4--2.5, pp.225--228.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

private def pairRead (g : H) (i : Fin 10) : Fin 4 := ⟨(g.1.1 i).val / 2 % 4, Nat.mod_lt _ (by decide)⟩
private def pairMap (g : H) (i : Fin 4) : Fin 4 := pairRead g ⟨2 * i.val, by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem preserves_first_eight (g : H) (i : Fin 8) :
    (g.1.1 ⟨i.val, by omega⟩).val < 8 := by
  obtain ⟨a, rfl⟩ := word_bijective.surjective g
  revert a i
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem pair_independent (g : H) (i : Fin 8) :
    pairMap g ⟨i.val / 2, by omega⟩ = pairRead g ⟨i.val, by omega⟩ := by
  obtain ⟨a, rfl⟩ := word_bijective.surjective g
  revert a i
  decide +kernel

private theorem pairMap_mul (g h : H) (i : Fin 4) :
    pairMap (g * h) i = pairMap g (pairMap h i) := by
  let k : Fin 10 := ⟨2 * i.val, by omega⟩
  have hk : (h.1.1 k).val < 8 := preserves_first_eight h ⟨2 * i.val, by omega⟩
  have hi := pair_independent g ⟨(h.1.1 k).val, hk⟩
  have hm : (h.1.1 k).val / 2 % 4 = (h.1.1 k).val / 2 := Nat.mod_eq_of_lt (by omega)
  simpa only [pairMap, pairRead, hm, k, Subgroup.coe_mul, Perm.mul_apply, Fin.eta] using hi.symm

private theorem pairMap_one (i : Fin 4) : pairMap 1 i = i := by
  apply Fin.ext
  simp [pairMap, pairRead]

private def pairPerm (g : H) : Perm (Fin 4) where
  toFun := pairMap g
  invFun := pairMap g⁻¹
  left_inv i := by rw [← pairMap_mul, inv_mul_cancel, pairMap_one]
  right_inv i := by rw [← pairMap_mul, mul_inv_cancel, pairMap_one]

private def pairHom : H →* Perm (Fin 4) where
  toFun := pairPerm
  map_one' := by apply Perm.ext; intro i; exact pairMap_one i
  map_mul' g h := by apply Perm.ext; intro i; exact pairMap_mul g h i

private def parity : H →* ℤˣ := Perm.sign.comp pairHom

private theorem parity_generators : ∀ i : Fin 8,
    parity (generators i) = if i = 6 then -1 else 1 := by
  decide +kernel

private theorem parity_pi : parity pi = 1 := parity_generators 0
private theorem parity_mu : parity mu = 1 := parity_generators 1
private theorem parity_lam : parity lam = -1 := parity_generators 6

private def twist (g : H) : H := if parity g = 1 then g else pi * g

private theorem twist_mul (g h : H) : twist (g * h) = twist g * twist h := by
  have hp : pi * pi = 1 := by decide +kernel
  have hcg : g * pi = pi * g := mem_center_iff.mp modelCentralInvolution_mem_center g
  have hm : pi * (g * h) = g * (pi * h) := by rw [← mul_assoc, ← hcg, mul_assoc]
  rcases Int.units_eq_one_or (parity g) with hg | hg <;>
    rcases Int.units_eq_one_or (parity h) with hh | hh <;>
    norm_num [twist, map_mul, hg, hh]
  · exact hm
  · simp only [mul_assoc]
  · rw [mul_assoc, ← hm, ← mul_assoc pi pi, hp, one_mul]


private theorem twist_twist (g : H) : twist (twist g) = g := by
  have hp : pi * pi = 1 := by decide +kernel
  by_cases h : parity g = 1
  · simp [twist, h]
  · simp [twist, h, map_mul, parity_pi, ← mul_assoc, hp]

/-- The source change of generator is an automorphism of the whole concrete H. -/
public def lambdaTwist : H ≃* H where
  toFun := twist
  invFun := twist
  left_inv := twist_twist
  right_inv := twist_twist
  map_mul' := twist_mul

public theorem lambdaTwist_generators : ∀ i : Fin 8,
    lambdaTwist (generators i) = if i = 6 then pi * lam else generators i := by
  intro i
  change twist (generators i) = _
  rw [twist, parity_generators]
  fin_cases i <;> simp [generators]

public theorem lambdaTwist_pi : lambdaTwist pi = pi := lambdaTwist_generators 0
public theorem lambdaTwist_mu : lambdaTwist mu = mu := lambdaTwist_generators 1
public theorem lambdaTwist_lam : lambdaTwist lam = pi * lam := lambdaTwist_generators 6

public theorem lambdaTwist_involutive : Function.Involutive lambdaTwist := twist_twist

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Re-mark the supplied isomorphism by the source change of lambda. -/
@[expose] public def twistEquiv : D.centralizer ≃* CentralizerModels.a10Centralizer := e.trans lambdaTwist

public theorem twistEquiv_embedding (x : H) :
    D.a10ModelEmbedding (twistEquiv D e) x = D.a10ModelEmbedding e (lambdaTwist x) := by rfl

public theorem twistEquiv_mu :
    D.a10NoncentralInvolution (twistEquiv D e) = D.a10NoncentralInvolution e := by
  change D.a10ModelEmbedding (twistEquiv D e) mu = D.a10ModelEmbedding e mu
  rw [twistEquiv_embedding, lambdaTwist_mu]

public theorem twistEquiv_lam :
    D.a10ModelEmbedding (twistEquiv D e) lam = D.a10ModelEmbedding e (pi * lam) := by
  rw [twistEquiv_embedding, lambdaTwist_lam]

/-- Lemma 2.5's change of coordinates, conditional precisely on Lemma 2.4.
The originally specified noncentral involution is unchanged. -/
public theorem exists_normalized_equiv
    (h : ¬ (IsConj D.z (D.a10ModelEmbedding e lam) ∧
      IsConj D.z (D.a10ModelEmbedding e (pi * lam)))) :
    ∃ e' : D.centralizer ≃* CentralizerModels.a10Centralizer,
      D.a10NoncentralInvolution e' = D.a10NoncentralInvolution e ∧
      ¬ IsConj D.z (D.a10ModelEmbedding e' lam) := by
  by_cases hl : IsConj D.z (D.a10ModelEmbedding e lam)
  · refine ⟨twistEquiv D e, twistEquiv_mu D e, ?_⟩
    rw [twistEquiv_lam]
    exact fun hp => h ⟨hl, hp⟩
  · exact ⟨e, rfl, hl⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
