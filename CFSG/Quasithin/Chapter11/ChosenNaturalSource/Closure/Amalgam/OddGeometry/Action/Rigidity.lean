module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Centralization
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF

/-!
# Centralizer rigidity on the actual conjugate closure

Intersect a subgroup of index at most two in Uᵍ with each generating conjugate
of V. Each intersection has binary corank at most one. Since s(G,V)>1 and s
is conjugation invariant, E.3.6 extends its centralization by a two-group to
every generator, hence to all of Uᵍ. In particular nontrivial motion on Uᵍ
is already nontrivial on U₀. Together with OddPair.axis this also excludes a
completed odd pair directly, without a chief-section classification.

This does not construct the missing Sp₄ core-intersection commutator bound.
The parameter value is preceding 11.2.2(3), supplied by
qt-d-1222-natural-weak-closure-source. The source assembly remains with
qt-d-1222-natural-closure-amalgam. Symplectic.lean applies the movement result
to the actual normalized endpoint and its literal point-radical action.
Source: Aschbacher--Smith, E.3.6, printed p.232, and 11.5.8, printed p.784.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
open Chapter12.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- Centralization of an index-at-most-two subgroup extends to the literal
conjugate closure, by applying E.3.6 to each of its generating conjugates. -/
theorem conjugate_closure_centralizes_of_index
    (hs : letI := D.elementary; globalS V = (E.input.field.degree : ℕ∞))
    (g : G) (B A : Subgroup G)
    (hi : B.relIndex ((localClosure E).map (MulAut.conj g).toMonoidHom) ≤ 2)
    (hA : IsPGroup 2 A) (hc : B ≤ centralizer (A : Set G)) :
    (localClosure E).map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G) := by
  let := D.elementary
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  rintro x ⟨k,hk,v,hv,rfl⟩
  let W := V.map (MulAut.conj (g*k)).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hW : W ≤ (localClosure E).map (MulAut.conj g).toMonoidHom := by
    rintro y ⟨v,hv,rfl⟩
    refine ⟨k*v*k⁻¹, subset_closure ⟨k,hk,v,hv,rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hindex : (B ⊓ W).relIndex W ≤ 2 := by
    rw [inf_relIndex_right]
    exact (B.relIndex_le_of_le_right hW (by
      change (B.subgroupOf _).index ≠ 0
      exact index_ne_zero_of_finite)).trans hi
  have hcor : (subgroupCorank W (B ⊓ W) : ℕ∞) < globalS W := by
    have hbound : subgroupCorank W (B ⊓ W) ≤ 1 :=
      (Nat.log_mono_right hindex).trans (by decide : Nat.log 2 2 ≤ 1)
    rw [globalS_map_equiv, hs]
    exact_mod_cast lt_of_le_of_lt hbound E.input.nonbinary
  have he := centralizer_inf_eq_of_corank_lt_globalS inf_le_right hcor hA
  have hcent : A ≤ centralizer (W : Set G) := by
    have hh : A ≤ A ⊓ centralizer ((B ⊓ W : Subgroup G) : Set G) :=
      le_inf le_rfl ((le_centralizer_iff.mp hc).trans (centralizer_le inf_le_left))
    rw [he] at hh
    exact hh.trans inf_le_right
  have hw : (MulAut.conj (g*k)) v ∈ centralizer (A : Set G) :=
    le_centralizer_iff.mp hcent (mem_map_of_mem (MulAut.conj (g*k)).toMonoidHom hv)
  change (MulAut.conj g) (k*v*k⁻¹) ∈ centralizer (A : Set G)
  simpa only [MulAut.conj_apply, mul_inv_rev, mul_assoc] using hw

/-- Applying rigidity to the E.3.6 axis excludes a completed OddPair.
Existence of that pair is still the obligation of the source assembly. -/
theorem false_of_odd_pair_rigidity
    (h : LocalInputs E) (hab : IsMulCommutative E.W)
    (hs : letI := D.elementary; globalS V = (E.input.field.degree : ℕ∞))
    (g : G) (p : OddPair E g) : False := by
  let := D.elementary
  have hc := (OddPair.axis E h hab hs p).1
  have hfull := conjugate_closure_centralizes_of_index E hs g (U₀ E g) V
    p.second_index (IsElementaryAbelian.isPGroup 2 V) hc
  exact p.moves_closure (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp hfull))

/-- Motion on the conjugate closure is already motion on its core intersection. -/
theorem moves_core_intersection
    (hs : letI := D.elementary; globalS V = (E.input.field.degree : ℕ∞))
    (g : G)
    (hi : (U₀ E g).relIndex ((localClosure E).map (MulAut.conj g).toMonoidHom) ≤ 2)
    (hn : ⁅V, (localClosure E).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ⁅V, U₀ E g⁆ ≠ ⊥ := by
  let := D.elementary
  intro hz
  have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  have hfull := conjugate_closure_centralizes_of_index E hs g (U₀ E g) V
    hi (IsElementaryAbelian.isPGroup 2 V) hc
  exact hn (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hfull))

/-- Both index bounds and actual motion force the core intersections to
fail to commute. The symplectic geometry must contradict this conclusion. -/
theorem core_intersections_noncommuting
    (hs : letI := D.elementary; globalS V = (E.input.field.degree : ℕ∞))
    (g : G) (hfirst : (U₁ E g).relIndex (localClosure E) ≤ 2)
    (hsecond : (U₀ E g).relIndex ((localClosure E).map (MulAut.conj g).toMonoidHom) ≤ 2)
    (hn : ⁅V, (localClosure E).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ⁅U₁ E g, U₀ E g⁆ ≠ ⊥ := by
  let := D.elementary
  intro hz
  have hc : U₀ E g ≤ centralizer ((U₁ E g ⊓ V : Subgroup G) : Set G) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
      (centralizer_le inf_le_left)
  have hr : (subgroupCorank V (U₁ E g ⊓ V) : ℕ∞) < globalS V := by
    rw [hs]
    exact_mod_cast lt_of_le_of_lt (intersection_corank_le_one E g hfirst)
      E.input.nonbinary
  have hp : IsPGroup 2 (U₀ E g) := (isPGroup_pCoreIn 2 (KT E)).to_inf_right
  have he := centralizer_inf_eq_of_corank_lt_globalS inf_le_right hr hp
  have hh : U₀ E g ≤ U₀ E g ⊓ centralizer ((U₁ E g ⊓ V : Subgroup G) : Set G) :=
    le_inf le_rfl hc
  rw [he] at hh
  exact moves_core_intersection E hs g hsecond hn
    (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hh.trans inf_le_right)))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
