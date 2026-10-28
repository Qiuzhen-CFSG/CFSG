module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Setup
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Rigidity

/-!
# Centralizing the odd critical pair's axis

Write U=⟨V^(KT)⟩, U₁=U∩O₂((KT)^g), and U₀=U^g∩O₂(KT).
An index bound of two for U₁ in U restricts to a binary corank bound of one
for U₁∩V in V. If the commutator of U₁ and U₀ lies in the disjoint
field lines, E.3.6 promotes centralization of U₁∩V to centralization of V.

This proves the centralization step from its exact intermediate premises;
the critical-pair argument must still construct the index bound, line
disjointness and commutator containment. In particular we do not identify
this U with the earlier closure of V₃ in Geometry.U.
Source: Aschbacher--Smith, 11.5.8, printed p.784, using E.3.6 and 11.2.2(3).
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- Left conjugation; the source right-coset exponent is its inverse. -/
def U₁ (g : G) : Subgroup G :=
  localClosure E ⊓ ((KT E).map (MulAut.conj g).toMonoidHom).pCoreIn 2

def U₀ (g : G) : Subgroup G :=
  (localClosure E).map (MulAut.conj g).toMonoidHom ⊓ (KT E).pCoreIn 2

/-- Output specification for the odd critical-pair argument. All groups are
the original subgroup images. In particular, the last field asserts motion
on Uᵍ, not the existence or exclusion of a transvection on a chief factor. -/
structure OddPair (g : G) : Prop where
  seed_le_actor : V ≤ (KT E).map (MulAut.conj g).toMonoidHom
  seed_not_core : ¬ V ≤ ((KT E).map (MulAut.conj g).toMonoidHom).pCoreIn 2
  mutual_commutator : ⁅localClosure E, (localClosure E).map (MulAut.conj g).toMonoidHom⁆ ≤
    localClosure E ⊓ (localClosure E).map (MulAut.conj g).toMonoidHom
  first_index : (U₁ E g).relIndex (localClosure E) ≤ 2
  second_index : (U₀ E g).relIndex ((localClosure E).map (MulAut.conj g).toMonoidHom) ≤ 2
  lines_disjoint : E.V₁ ⊓ E.V₁.map (MulAut.conj g).toMonoidHom = ⊥
  core_commutator : ⁅U₁ E g, U₀ E g⁆ ≤
    E.V₁ ⊓ E.V₁.map (MulAut.conj g).toMonoidHom
  moves_closure : ⁅V, (localClosure E).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥

/-- The first index-two bound restricts to the actual original module V. -/
theorem intersection_corank_le_one (g : G)
    (hi : (U₁ E g).relIndex (localClosure E) ≤ 2) :
    subgroupCorank V (U₁ E g ⊓ V) ≤ 1 := by
  have hindex : (U₁ E g ⊓ V).relIndex V ≤ 2 := by
    rw [inf_relIndex_right]
    have hne : (U₁ E g).relIndex (localClosure E) ≠ 0 := by
      change ((U₁ E g).subgroupOf (localClosure E)).index ≠ 0
      exact index_ne_zero_of_finite
    exact ((U₁ E g).relIndex_le_of_le_right
      (show V ≤ localClosure E from le_conjugateSpanBy V (KT E)) hne).trans hi
  exact (Nat.log_mono_right hindex).trans (by decide : Nat.log 2 2 ≤ 1)

/-- E.3.6 on the literal U₀ and U₁ of the odd branch. The source value
s(G,V)=n and n>1 discharge its strict corank hypothesis. -/
theorem odd_axis_centralizes (h : LocalInputs E) (hab : IsMulCommutative E.W)
    (hs : letI := D.elementary; globalS V = (E.input.field.degree : ℕ∞)) (g : G)
    (hi : (U₁ E g).relIndex (localClosure E) ≤ 2)
    (hlines : E.V₁ ⊓ E.V₁.map (MulAut.conj g).toMonoidHom = ⊥)
    (hcomm : ⁅U₁ E g, U₀ E g⁆ ≤
      E.V₁ ⊓ E.V₁.map (MulAut.conj g).toMonoidHom) :
    U₀ E g ≤ centralizer (V : Set G) := by
  let := D.elementary
  let _ : IsElementaryAbelian 2 (localClosure E) := localClosure_elementary E h hab
  have hc : ⁅U₁ E g, U₀ E g⁆ = ⊥ := bot_unique (hlines ▸ hcomm)
  have hcent : U₀ E g ≤ centralizer (U₁ E g ⊓ V : Set G) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (centralizer_le inf_le_left)
  have hr : (subgroupCorank V (U₁ E g ⊓ V) : ℕ∞) < globalS V := by
    rw [hs]
    exact_mod_cast lt_of_le_of_lt (intersection_corank_le_one E g hi)
      E.input.nonbinary
  have hp : IsPGroup 2 (U₀ E g) :=
    ((IsElementaryAbelian.isPGroup 2 (localClosure E)).map
      (MulAut.conj g).toMonoidHom).to_inf_left
  have he := centralizer_inf_eq_of_corank_lt_globalS inf_le_right hr hp
  exact (le_inf le_rfl hcent).trans (he.le.trans inf_le_right)

/-- The source odd-pair output gives a centralizing subgroup of index at
most two, while V acts nontrivially on the literal conjugate closure.
Passing to a surviving chief section is a separate obligation. -/
theorem OddPair.axis (h : LocalInputs E) (hab : IsMulCommutative E.W)
    (hs : letI := D.elementary; globalS V = (E.input.field.degree : ℕ∞))
    {g : G} (p : OddPair E g) :
    U₀ E g ≤ centralizer (V : Set G) ∧
      (U₀ E g).relIndex ((localClosure E).map (MulAut.conj g).toMonoidHom) ≤ 2 ∧
      ⁅V, (localClosure E).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  ⟨odd_axis_centralizes E h hab hs g p.first_index p.lines_disjoint p.core_commutator,
    p.second_index, p.moves_closure⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam
