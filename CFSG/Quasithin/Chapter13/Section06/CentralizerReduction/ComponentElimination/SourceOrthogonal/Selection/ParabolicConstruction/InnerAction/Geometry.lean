module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.Marking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction.Lift
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FourComponent.Flags
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Adjacent
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.GroupTheory.SolvableResidual.PerfectQuotient

/-!
# Adjacent-node geometry for the inner-action branch

The minimal parabolic marked by the literal plus image is enlarged by
adding an adjacent node. In binary dimensions four and five the enlarged
cut stabilizer has quotient SL₃(2) by its own two-core. Its solvable residual
surjects onto this same geometric quotient, and the quotient above the
residual is a two-group. No equality of the parabolic and its residual is
used.

The source application transports the cut stabilizer back through the
prescribed model isomorphism and the basis obtained from the actual source
parabolic. It retains both marking equalities and the inclusion in K⁺.
Existence needs no inner-action assumption; `InnerAction.Lift` supplies the
invariance of the lifted residual under that assumption. The parent owns
local-family membership, star-quasisimplicity and the final contradiction.

Only intrinsic flag calculations from Chapter 13 Section 8 are reused.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.23,
printed p.933/PDF p.950, using the minimal-parabolic argument on p.932.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction.Geometry
open ComponentSelection BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
open BinaryLinear.SmallParabolicLevi
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private instance : Group.IsPerfect (SL(3, ZMod 2)) := by
  let := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  exact Group.IsPerfect.ofSurjective (f := (slEquivLinear 3).symm.toMonoidHom)
    (slEquivLinear 3).symm.surjective

private theorem minimal_le_two_node {m : ℕ} (b : Basis m) (i j : Fin m) :
    minimalParabolic b i ≤ cutStabilizer b ({i, j} : Set (Fin m))ᶜ := by
  apply (cutStabilizer_le_iff _ _ _).mpr
  exact Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

/-- Every marked minimal parabolic has an adjacent two-node overgroup with
the actual intrinsic two-core quotient SL₃(2). -/
theorem exists_adjacent_quotient {m : ℕ} (hm : m = 3 ∨ m = 4)
    (b : Basis m) (i : Fin m) :
    ∃ j : Fin m, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
      minimalParabolic b i ≤ cutStabilizer b ({i, j} : Set (Fin m))ᶜ ∧
      Nonempty ((cutStabilizer b ({i, j} : Set (Fin m))ᶜ ⧸
        pCore 2 (cutStabilizer b ({i, j} : Set (Fin m))ᶜ)) ≃* SL(3, ZMod 2)) := by
  rcases hm with rfl | rfl
  · let j := fourAdjacentNode i
    refine ⟨j, fourAdjacentNode_adjacent i,
      minimal_le_two_node b i j, ⟨?_⟩⟩
    exact (fourEnlargedQuotientEquiv b i).trans
      (linearThreeEquivProjective.symm.trans (slEquivLinear 3).symm)
  · exact ⟨TwoNodes.adjacentNode i, TwoNodes.adjacentNode_adjacent i,
      minimal_le_two_node b i _, ⟨TwoNodes.adjacentQuotientEquiv b i⟩⟩

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem perfectQuotient (P : Subgroup X)
    (e : (P ⧸ pCore 2 P) ≃* SL(3, ZMod 2)) : Group.IsPerfect (P ⧸ pCore 2 P) :=
  Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- Restrict the supplied parabolic quotient to the residual and embed it
back in the original ambient group. -/
noncomputable def embeddedResidualQuotientEquiv (P : Subgroup X)
    (e : (P ⧸ pCore 2 P) ≃* SL(3, ZMod 2)) :
    ((solvableResidual P).map P.subtype ⧸
      pCore 2 ((solvableResidual P).map P.subtype)) ≃* SL(3, ZMod 2) := by
  let := perfectQuotient P e
  let a := ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).symm
  exact (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    ((solvableResidualPCoreQuotientEquiv 2).trans e)

/-- The residual equivalence agrees with the supplied quotient on representatives. -/
theorem embeddedResidualQuotientEquiv_mk (P : Subgroup X)
    (e : (P ⧸ pCore 2 P) ≃* SL(3, ZMod 2)) (d : solvableResidual P) :
    embeddedResidualQuotientEquiv P e
      (QuotientGroup.mk' _ ((solvableResidual P).equivMapOfInjective
        P.subtype P.subtype_injective d)) = e (QuotientGroup.mk' _ d.val) := by
  change e (QuotientGroup.mk' _ (((solvableResidual P).equivMapOfInjective
    P.subtype P.subtype_injective).symm
      ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective d)).val) = _
  rw [MulEquiv.symm_apply_apply]

/-- The two-core supplements the solvable residual of this parabolic. -/
theorem quotient_residual_isTwoGroup (P : Subgroup X)
    (e : (P ⧸ pCore 2 P) ≃* SL(3, ZMod 2)) :
    IsPGroup 2 (P ⧸ solvableResidual P) := by
  let := perfectQuotient P e
  exact quotient_solvableResidual_isPGroup_of_perfect_pCore_quotient 2

/-- The literal adjacent-node stabilizer, its solvable quotient, and its
embedded residual modulo the residual's own two-core. -/
theorem exists_adjacent_residual {m : ℕ} (hm : m = 3 ∨ m = 4)
    (b : Basis m) (i : Fin m) :
    ∃ j : Fin m, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
      let Q := cutStabilizer b ({i, j} : Set (Fin m))ᶜ
      minimalParabolic b i ≤ Q ∧ IsPGroup 2 (Q ⧸ solvableResidual Q) ∧
        Nonempty (((solvableResidual Q).map Q.subtype ⧸
          pCore 2 ((solvableResidual Q).map Q.subtype)) ≃* SL(3, ZMod 2)) := by
  obtain ⟨j, hj, hQ, ⟨e⟩⟩ := exists_adjacent_quotient hm b i
  exact ⟨j, hj, hQ, quotient_residual_isTwoGroup _ e, ⟨embeddedResidualQuotientEquiv _ e⟩⟩

variable {G : Type*} [Group G] [Finite G]

/-- Construct the source overgroup through the prescribed SL model and its
actual basis marking, retaining the original and enlarged cut stabilizers. -/
theorem exists_source_geometric_parabolic_marking
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hLK : Lv L v ≤ K)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : m = 3 ∨ m = 4)
    (e : plusImage K L T z v hL hz K ≃* SL(m + 1, ZMod 2)) :
    ∃ (b : Basis m) (i j : Fin m) (P : Subgroup (Gplus K L T z v hL hz)),
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
      ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
        (plusImage K L T z v hL hz K)).map
        (e.trans (slEquivLinear (m + 1))).toMonoidHom = minimalParabolic b i ∧
      (P.subgroupOf (plusImage K L T z v hL hz K)).map
        (e.trans (slEquivLinear (m + 1))).toMonoidHom =
        cutStabilizer b ({i, j} : Set (Fin m))ᶜ ∧
      plusImage K L T z v hL hz (sourceParabolic K L T v) ≤ P ∧
      P ≤ plusImage K L T z v hL hz K ∧
      IsPGroup 2 (P ⧸ solvableResidual P) ∧
      Nonempty (((solvableResidual P).map P.subtype ⧸
        pCore 2 ((solvableResidual P).map P.subtype)) ≃* SL(3, ZMod 2)) := by
  obtain ⟨b, i, hmark, _⟩ := exists_sourceParabolic_marking K L T z v hL hz
    hlocal hLK hc hmove hm e
  obtain ⟨j, hj, hmin, ⟨eQ⟩⟩ := exists_adjacent_quotient hm b i
  let C := plusImage K L T z v hL hz K
  let E := e.trans (slEquivLinear (m + 1))
  let Q := cutStabilizer b ({i, j} : Set (Fin m))ᶜ
  let R := Q.map E.symm.toMonoidHom
  let P := R.map C.subtype
  have hPC : P ≤ C := map_subtype_le R
  have hPQ : (P.subgroupOf C).map E.toMonoidHom = Q := by
    rw [show P.subgroupOf C = R from comap_map_eq_self_of_injective C.subtype_injective R]
    exact (map_symm_eq_iff_map_eq R (e := E) (H := Q)).mp rfl
  have hSC : plusImage K L T z v hL hz (sourceParabolic K L T v) ≤ C :=
    map_mono (comap_mono (sup_le hLK inf_le_right))
  have hSP : plusImage K L T z v hL hz (sourceParabolic K L T v) ≤ P := by
    have hh : (plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf C ≤
        P.subgroupOf C := by
      apply (map_le_map_iff_of_injective (f := E.toMonoidHom) E.injective).mp
      rw [hPQ, hmark]
      exact hmin
    have hh' := map_mono (f := C.subtype) hh
    simpa only [map_subgroupOf_eq_of_le hSC, map_subgroupOf_eq_of_le hPC] using hh'
  let a : P ≃* Q := ((E.symm.subgroupMap Q).trans
    (R.equivMapOfInjective C.subtype C.subtype_injective)).symm
  let eP : (P ⧸ pCore 2 P) ≃* SL(3, ZMod 2) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eQ
  exact ⟨b, i, j, P, hj, hmark, hPQ, hSP, hPC,
    quotient_residual_isTwoGroup P eP, ⟨embeddedResidualQuotientEquiv P eP⟩⟩

/-- The geometric premises consumed by `false_of_inner_geometric_parabolic`.
No assumption on the action of Tᵥ on the diagram is needed for existence. -/
theorem exists_source_geometric_parabolic
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hLK : Lv L v ≤ K)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : m = 3 ∨ m = 4)
    (e : plusImage K L T z v hL hz K ≃* SL(m + 1, ZMod 2)) :
    ∃ P : Subgroup (Gplus K L T z v hL hz),
      plusImage K L T z v hL hz (sourceParabolic K L T v) ≤ P ∧
      P ≤ plusImage K L T z v hL hz K ∧
      IsPGroup 2 (P ⧸ solvableResidual P) ∧
      Nonempty (((solvableResidual P).map P.subtype ⧸
        pCore 2 ((solvableResidual P).map P.subtype)) ≃* SL(3, ZMod 2)) := by
  obtain ⟨b, i, j, P, _, _, _, hSP, hPC, htwo, eP⟩ :=
    exists_source_geometric_parabolic_marking K L T z v hL hz hlocal hLK hc hmove hm e
  exact ⟨P, hSP, hPC, htwo, eP⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction.Geometry

end
