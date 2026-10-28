module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SourceGeometry
public import Theory.SpecificGroups.PSL3Two.Parabolics.CosetGeometry
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# Standard markings of the original local quotients

Conjugating a chosen local quotient equivalence aligns the actual common
Sylow subgroup with the standard model. The two source maximal parabolics
then map to the standard pair, in either order. This proves the precise
quotient marking needed for the Fano and polar residue comparisons; no
orientation or compatibility of an arbitrary marking is assumed.

Source: Aschbacher–Smith I.5.4(1–2), printed p.420.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G K : Type*} [Group G] [Group K] [Finite K]
variable {D : Diagram} (S : DSystem D G)

theorem exists_standard_quotientMark (i j k : Fin 3)
    (hlocal : RankTwoParabolics (S.family i) (S.T.subgroupOf (S.family i))
      (localParabolic S.family i j) (localParabolic S.family i k))
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K)
    (A B : Subgroup K)
    (hmodel : ∀ T : Sylow 2 K, ∃ g : K, ∀ U : Subgroup K,
      (IsCoatom U ∧ (T : Subgroup K) ≤ U) ↔
        U = (MulAut.conj g).mapSubgroup A ∨ U = (MulAut.conj g).mapSubgroup B) :
    ∃ e' : (S.family i ⧸ pCore 2 (S.family i)) ≃* K,
      ((localParabolic S.family i j).map (S.localQuotientMap i e') = A ∧
        (localParabolic S.family i k).map (S.localQuotientMap i e') = B) ∨
      ((localParabolic S.family i j).map (S.localQuotientMap i e') = B ∧
        (localParabolic S.family i k).map (S.localQuotientMap i e') = A) := by
  let f := S.localQuotientMap i e
  have hm := hlocal.map f (S.localQuotientMap_surjective i e)
    (S.localQuotientMap_ker_le i e)
  obtain ⟨T, hT⟩ := S.localQuotient_sylow i e
  obtain ⟨g, hg⟩ := hmodel T
  have hP : (T : Subgroup K) ≤ (localParabolic S.family i j).map f := by
    rw [hT, ← hm.borel_eq]
    exact inf_le_left
  have hR : (T : Subgroup K) ≤ (localParabolic S.family i k).map f := by
    rw [hT, ← hm.borel_eq]
    exact inf_le_right
  have hp := (hg _).mp ⟨hm.left_maximal, hP⟩
  have hr := (hg _).mp ⟨hm.right_maximal, hR⟩
  let a := MulAut.conj g
  let e' := e.trans a.symm
  have hnormalize (P : Subgroup (S.family i)) (U : Subgroup K)
      (hP : P.map f = a.mapSubgroup U) : P.map (S.localQuotientMap i e') = U := by
    change P.map (a.symm.toMonoidHom.comp f) = U
    rw [← map_map, hP]
    exact a.mapSubgroup.symm_apply_apply U
  refine ⟨e', ?_⟩
  rcases hp with hp | hp <;> rcases hr with hr | hr
  · exact (hm.distinct (hp.trans hr.symm)).elim
  · exact Or.inl ⟨hnormalize _ _ hp, hnormalize _ _ hr⟩
  · exact Or.inr ⟨hnormalize _ _ hp, hnormalize _ _ hr⟩
  · exact (hm.distinct (hp.trans hr.symm)).elim

/-- The plane quotient sends its original two parabolics to the standard Fano pair. -/
theorem plane_standard_quotientMark :
    ∃ e : (S.family 2 ⧸ pCore 2 (S.family 2)) ≃* Matrix.PSL3Two.PSL,
      ((localParabolic S.family 2 0).map (S.localQuotientMap 2 e) =
          Matrix.PSL3Two.pointParabolic ∧
        (localParabolic S.family 2 1).map (S.localQuotientMap 2 e) =
          Matrix.PSL3Two.lineParabolic) ∨
      ((localParabolic S.family 2 0).map (S.localQuotientMap 2 e) =
          Matrix.PSL3Two.lineParabolic ∧
        (localParabolic S.family 2 1).map (S.localQuotientMap 2 e) =
          Matrix.PSL3Two.pointParabolic) := by
  obtain ⟨e⟩ := S.plane_quotient
  apply S.exists_standard_quotientMark 2 0 1 S.plane_parabolics e
  intro T
  obtain ⟨g, _, _, _, h⟩ := Matrix.PSL3Two.Fano.sylow_parabolics_conjugate T
  exact ⟨g, h⟩

variable (S₃ : DSystem .C3 G)

/-- The original point quotient is marked by the standard A₆ or S₆ polar pair. -/
theorem point_standard_quotientMark :
    (∃ e : (S₃.family 0 ⧸ pCore 2 (S₃.family 0)) ≃*
        Theory.SpecificGroups.SymmetricSix.A6,
      ((localParabolic S₃.family 0 1).map (S₃.localQuotientMap 0 e) =
          Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer ∧
        (localParabolic S₃.family 0 2).map (S₃.localQuotientMap 0 e) =
          Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer) ∨
      ((localParabolic S₃.family 0 1).map (S₃.localQuotientMap 0 e) =
          Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer ∧
        (localParabolic S₃.family 0 2).map (S₃.localQuotientMap 0 e) =
          Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer)) ∨
    (∃ e : (S₃.family 0 ⧸ pCore 2 (S₃.family 0)) ≃*
        Theory.SpecificGroups.SymmetricSix.S6,
      ((localParabolic S₃.family 0 1).map (S₃.localQuotientMap 0 e) =
          Theory.SpecificGroups.SymmetricSix.duadStabilizer ∧
        (localParabolic S₃.family 0 2).map (S₃.localQuotientMap 0 e) =
          Theory.SpecificGroups.SymmetricSix.synthemeStabilizer) ∨
      ((localParabolic S₃.family 0 1).map (S₃.localQuotientMap 0 e) =
          Theory.SpecificGroups.SymmetricSix.synthemeStabilizer ∧
        (localParabolic S₃.family 0 2).map (S₃.localQuotientMap 0 e) =
          Theory.SpecificGroups.SymmetricSix.duadStabilizer)) := by
  rcases S₃.point_C3 rfl with h | h
  · obtain ⟨e⟩ := h
    left
    apply S₃.exists_standard_quotientMark 0 1 2 S₃.point_parabolics e
    intro T
    obtain ⟨g, _, h⟩ := Theory.SpecificGroups.SymmetricSix.a6_coatoms_over_sylow T
    exact ⟨g, h⟩
  · obtain ⟨e⟩ := h
    right
    apply S₃.exists_standard_quotientMark 0 1 2 S₃.point_parabolics e
    intro T
    obtain ⟨g, _, h⟩ := Theory.SpecificGroups.SymmetricSix.coatoms_over_sylow T
    exact ⟨g, h⟩

end Quasithin.I5.DSystem
