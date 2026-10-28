module
public import Theory.GroupAction.SymmetricSixChiefBudget.Quotient

/-!
# Centralization from an index-two fixed subgroup above S₆

For a finite group mapping onto S₆ with a two-group kernel, an actor
containing a marked even involution cannot have index at most two on a
noncentral binary chief factor. The fixed-index inequalities along an
actual chief series therefore make every factor central. The two-residual
then centralizes the entire normal two-group, including when it is
nonabelian. Passing through the literal normal quotient gives the same
conclusion modulo its prescribed lower subgroup.

Source application: Aschbacher--Smith, Lemma 13.8.33, printed p.966,
the centralization of H_C/V_H. The ambient source application supplies
the original conjugate seed span and its index-two intersection.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement.SymmetricSixBudget
variable {H : Type*} [Group H] [Finite H]

/-- An even involution cannot act with index at most two on a noncentral
binary chief factor above S₆. Thus every factor in the original normal
two-subgroup is central. -/
theorem noncentralCount_eq_zero_of_index_two
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : U ≤ q.ker)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 2)
    (s : SeriesOn U) : s.noncentralCount = 0 := by
  apply s.noncentralCount_eq_zero_iff.mpr
  intro i
  by_contra hi
  have hU2 := hp.to_le hU
  let := s.factor_elementary hU2 i
  let := s.factor_nontrivial i
  let μ : MulDistribMulAction H (s.Factor i) := MulDistribMulAction.compHom _ (s.action i)
  let := μ
  have hl := simple_group_fixedIndex_lower q hq hp A a ha heven haA
    (s.factor_irreducible i) (fun ht => hi ((s.central_iff_action i).mpr ht))
  change 4 ≤ sectionIndex A (s.lower i) (s.upper i) at hl
  have hm := sectionIndex_mul_lower_le A (s.lower i) (s.upper i) (s.series.isChief i).lt.le
  have hpidx : 1 ≤ (centralizer (A : Set H)).relIndex (s.lower i).val :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hu := (centralizer (A : Set H)).relIndex_le_of_le_right (s.upper_le i)
    index_ne_zero_of_finite
  have hh : 4 ≤ (centralizer (A : Set H)).relIndex (s.upper i).val :=
    (le_mul_of_one_le_right (by positivity) hpidx).trans
      ((Nat.mul_le_mul_right _ hl).trans hm)
  omega

/-- Index at most two forces the two-residual to centralize the actual
normal two-subgroup, without an abelianness hypothesis. -/
theorem residual_commutator_eq_bot_of_index_two
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : U ≤ q.ker)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 2) :
    ⁅U, pResidual 2 H⁆ = ⊥ := by
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hs := noncentralCount_eq_zero_of_index_two q hq hp U hU A a ha heven haA hindex s
  have hlast : IsPGroup 2 s.series.last.val := by
    rw [s.last_eq]
    exact hp.to_le hU
  have hc := s.series.residual_commutator_le_head_of_central_steps
    hlast (s.noncentralCount_eq_zero_iff.mp hs)
  rw [s.last_eq, s.head_eq] at hc
  exact le_bot_iff.mp hc

/-- The residual centralizes the literal normal section V/Z when an actor
above an even involution has centralizer-modulo index at most two. -/
theorem residual_commutator_le_of_modulo_index_two
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (hindex : (centralizerModulo V A Z).relIndex V ≤ 2) :
    ⁅V, pResidual 2 H⁆ ≤ Z := by
  let π := QuotientGroup.mk' Z
  let qbar := QuotientGroup.lift Z q (hZV.trans hV)
  have hqbar : Function.Surjective qbar :=
    QuotientGroup.lift_surjective_of_surjective Z q hq _
  have hker : qbar.ker = q.ker.map π := QuotientGroup.ker_lift Z q _
  have hpbar : IsPGroup 2 qbar.ker := by rw [hker]; exact hp.map π
  let : (V.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  have hVbar : V.map π ≤ qbar.ker := by rw [hker]; exact map_mono hV
  have hAbar : (A.map π).map qbar = A.map q := by rw [map_map]; rfl
  have hidxbar : (centralizer (A.map π : Set (H ⧸ Z))).relIndex (V.map π) ≤ 2 := by
    rwa [centralizerModulo_relIndex_eq] at hindex
  have hc := residual_commutator_eq_bot_of_index_two qbar hqbar hpbar
    (V.map π) hVbar (A.map π) a ha heven (hAbar.symm ▸ haA) hidxbar
  have hres : (pResidual 2 H).map π = pResidual 2 (H ⧸ Z) := map_pResidual_quotient 2 Z
  have hm : (⁅V, pResidual 2 H⁆).map π ≤ ⊥ := by
    rw [map_commutator, hres, hc]
  have hk := map_le_iff_le_comap.mp hm
  simpa only [MonoidHom.comap_bot, π, QuotientGroup.ker_mk'] using hk

/-- Source form using an actual subgroup of index at most two, whose
commutators with the specified actor lie in Z. -/
theorem residual_commutator_le_of_index_two
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A.map q)
    (K : Subgroup H) (hc : ⁅V ⊓ K, A⁆ ≤ Z) (hindex : K.relIndex V ≤ 2) :
    ⁅V, pResidual 2 H⁆ ≤ Z :=
  residual_commutator_le_of_modulo_index_two q hq hp V Z hZV hV A a ha heven haA
    ((centralizerModulo_relIndex_le_of_commutator V A Z K hc).trans hindex)
end NoncentralChiefRefinement.SymmetricSixBudget
