module

public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

/-!
# Symmetric-four core actions for binary parabolics

For an actual isomorphism with S₄, the intrinsic two-core is elementary of
order four, its quotient is S₃, and the quotient conjugates the core faithfully
and irreducibly. The permutation identification uses the three nonidentity
core elements. The equation for the quotient action records its compatibility
with the actual inclusion and quotient map.

A finite permutation calculation shows that every nontrivial normal subgroup
of S₄ is self-centralizing. Applied to a normal subgroup of the abelian core,
this proves the required invariant-subgroup dichotomy. This calculation is
adapted from `Theory.GroupTheory.SymmetricFourSylowInvolution`.

These are conditional transport lemmas for the concrete linear parabolics in
Aschbacher–Smith I.5.4 and I.5.7; a concrete parabolic isomorphism must still be
supplied before they give a local-model result.
-/

namespace Matrix.PSL3Two.ParabolicCoreModel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem conjugate_centralizer_calculation :
    ∀ first : Equiv.Perm (Fin 4), first ≠ 1 →
      ∀ second : Equiv.Perm (Fin 4),
        (∀ conjugator : Equiv.Perm (Fin 4),
          (conjugator * first * conjugator⁻¹) * second =
            second * (conjugator * first * conjugator⁻¹)) →
        second = 1 ∨ ∃ conjugator : Equiv.Perm (Fin 4),
          second = conjugator * first * conjugator⁻¹ := by
  decide +kernel

private theorem normal_centralizer_le
    {K : Type*} [Group K] (equiv : K ≃* Equiv.Perm (Fin 4))
    (Q : Subgroup K) [Q.Normal] (first : K) (hfirst : first ∈ Q)
    (hne : first ≠ 1) : Subgroup.centralizer (Q : Set K) ≤ Q := by
  intro second hsecond
  have hcalc := conjugate_centralizer_calculation (equiv first)
    (by simpa using hne) (equiv second)
  have hcomm : ∀ conjugator : Equiv.Perm (Fin 4),
      (conjugator * equiv first * conjugator⁻¹) * equiv second =
        equiv second * (conjugator * equiv first * conjugator⁻¹) := by
    intro conjugator
    have hmem := Subgroup.Normal.conj_mem (inferInstance : Q.Normal)
      first hfirst (equiv.symm conjugator)
    have heq := Subgroup.mem_centralizer_iff.mp hsecond _ hmem
    simpa only [map_mul, map_inv, equiv.apply_symm_apply] using congrArg equiv heq
  rcases hcalc hcomm with hone | ⟨conjugator, hconj⟩
  · have : second = 1 := equiv.injective (by simpa using hone)
    exact this ▸ Q.one_mem
  · have : second = equiv.symm conjugator * first * (equiv.symm conjugator)⁻¹ := by
      apply equiv.injective
      simpa only [map_mul, map_inv, equiv.apply_symm_apply] using hconj
    rw [this]
    exact Subgroup.Normal.conj_mem inferInstance first hfirst _


@[expose] public section

variable {G : Type*} [Group G] [Finite G]

theorem core_data (e : G ≃* Equiv.Perm (Fin 4)) :
    IsElementaryAbelian 2 (pCore 2 G) ∧ Nat.card (pCore 2 G) = 4 := by
  obtain ⟨hel, hc⟩ := symmetric_four_model_twoCore_data (Or.inl ⟨e⟩)
  refine ⟨hel, ?_⟩
  have hG : Nat.card G = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  rcases hc with hc | hc <;> omega

theorem core_selfCentralizing (e : G ≃* Equiv.Perm (Fin 4)) :
    Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
  have hc := (core_data e).2
  let : Nontrivial (pCore 2 G) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : pCore 2 G)
  exact normal_centralizer_le e _ x x.property (fun h => hx (Subtype.ext h))

theorem normal_le_core (e : G ≃* Equiv.Perm (Fin 4))
    (N : Subgroup G) [N.Normal] (hN : N ≤ pCore 2 G) :
    N = ⊥ ∨ N = pCore 2 G := by
  classical
  by_cases hn : N = ⊥
  · exact Or.inl hn
  right
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  have hcent := normal_centralizer_le e N x x.property (fun h => hx1 (Subtype.ext h))
  let := (core_data e).1
  apply le_antisymm hN
  apply le_trans _ hcent
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact congrArg Subtype.val
    (IsMulCommutative.is_comm.comm (⟨z, hN hz⟩ : pCore 2 G) ⟨y, hy⟩)

section Conjugation
omit [Finite G]
variable (Q : Subgroup G) [Q.Normal] [IsElementaryAbelian 2 Q]

theorem le_conj_ker : Q ≤ (MulAut.conjNormal : G →* MulAut Q).ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  ext y
  change x * (y : G) * x⁻¹ = y
  have hc := congrArg Subtype.val
    (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : Q) y)
  change x * (y : G) = (y : G) * x at hc
  rw [hc, mul_inv_cancel_right]

noncomputable def quotientConj : G ⧸ Q →* MulAut Q :=
  QuotientGroup.lift Q MulAut.conjNormal (le_conj_ker Q)

theorem quotientConj_mk (g : G) (x : Q) :
    ((quotientConj Q (QuotientGroup.mk' Q g)) x : G) = g * x * g⁻¹ := rfl

theorem conj_ker_eq (hcent : Subgroup.centralizer (Q : Set G) ≤ Q) :
    (MulAut.conjNormal : G →* MulAut Q).ker = Q := by
  apply le_antisymm _ (le_conj_ker Q)
  intro g hg
  apply hcent
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have he := congrArg (fun f : MulAut Q => (f ⟨x, hx⟩ : G)) (MonoidHom.mem_ker.mp hg)
  change g * x * g⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

theorem quotientConj_injective (hcent : Subgroup.centralizer (Q : Set G) ≤ Q) :
    Function.Injective (quotientConj Q) := by
  rw [← MonoidHom.ker_eq_bot_iff, quotientConj, QuotientGroup.ker_lift,
    conj_ker_eq Q hcent, QuotientGroup.map_mk'_self]

end Conjugation

noncomputable def autPermHom (K : Type*) [Group K] :
    MulAut K →* Equiv.Perm {x : K // x ≠ 1} where
  toFun f := Equiv.Perm.subtypePerm f.toEquiv (fun x => by simp)
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl

theorem autPermHom_injective (K : Type*) [Group K] :
    Function.Injective (autPermHom K) := by
  intro f g h
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · exact congrArg Subtype.val (Equiv.congr_fun h ⟨x, hx⟩)

noncomputable def fourAutEquiv (K : Type*) [Group K] [Finite K] [IsKleinFour K] :
    MulAut K ≃* Equiv.Perm (Fin 3) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hc : Nat.card {x : K // x ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  have hcard : Nat.card (MulAut K) = Nat.card (Equiv.Perm {x : K // x ≠ 1}) := by
    rw [IsKleinFour.card_mulAut, Nat.card_eq_fintype_card (α := Equiv.Perm _),
      Fintype.card_perm, ← Nat.card_eq_fintype_card, hc]
    decide
  exact (MulEquiv.ofBijective (autPermHom K)
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨autPermHom_injective K, hcard⟩)).trans
    (Equiv.permCongrHom (Finite.equivFinOfCardEq hc))


noncomputable def coreQuotientAutEquiv (e : G ≃* Equiv.Perm (Fin 4)) :
    G ⧸ pCore 2 G ≃* MulAut (pCore 2 G) := by
  let := (core_data e).1
  have hc := (core_data e).2
  let : Nontrivial (pCore 2 G) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (pCore 2 G) := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  have hG : Nat.card G = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hquot : Nat.card (G ⧸ pCore 2 G) = 6 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 G)
    rw [hc, hG] at h
    omega
  exact MulEquiv.ofBijective (quotientConj (pCore 2 G))
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨quotientConj_injective _ (core_selfCentralizing e),
        hquot.trans (IsKleinFour.card_mulAut _).symm⟩)

theorem coreQuotientAutEquiv_mk (e : G ≃* Equiv.Perm (Fin 4)) (g : G)
    (x : pCore 2 G) :
    ((coreQuotientAutEquiv e (QuotientGroup.mk' (pCore 2 G) g)) x : G) =
      g * x * g⁻¹ := rfl

noncomputable def coreQuotientEquiv (e : G ≃* Equiv.Perm (Fin 4)) :
    G ⧸ pCore 2 G ≃* Equiv.Perm (Fin 3) := by
  let := (core_data e).1
  have hc := (core_data e).2
  let : Nontrivial (pCore 2 G) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (pCore 2 G) := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  exact (coreQuotientAutEquiv e).trans (fourAutEquiv _)

theorem core_action_irreducible (e : G ≃* Equiv.Perm (Fin 4))
    (W : Subgroup (pCore 2 G))
    (hW : ∀ q : G ⧸ pCore 2 G, ∀ x ∈ W, coreQuotientAutEquiv e q x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  let Q := pCore 2 G
  let N := W.map Q.subtype
  have hN : N ≤ Q := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  let : N.Normal := ⟨by
    rintro x ⟨y, hy, rfl⟩ g
    refine Subgroup.mem_map.mpr ⟨coreQuotientAutEquiv e (QuotientGroup.mk' Q g) y,
      hW _ y hy, ?_⟩
    exact coreQuotientAutEquiv_mk e g y⟩
  rcases normal_le_core e N hN with hn | hn
  · exact Or.inl ((W.map_eq_bot_iff_of_injective Q.subtype_injective).mp hn)
  · right
    apply Subgroup.map_injective Q.subtype_injective
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using hn

end

end Matrix.PSL3Two.ParabolicCoreModel
