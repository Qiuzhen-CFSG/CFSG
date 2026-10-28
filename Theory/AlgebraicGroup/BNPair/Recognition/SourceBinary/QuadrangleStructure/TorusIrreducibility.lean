module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.RootCommutators
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LinearLocalRoots
public import Theory.SpecificGroups.SL2.SylowCharacteristicImage
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Cartan irreducibility and the nonzero quadrangle commutator

For an actual binary linear local permutation group, every nonzero
Cartan-invariant subgroup of the canonical root is the whole root.
Adjoin the complementary section to the subgroup. The resulting subgroup
of U is normalized by B: the simple root is abelian, the complementary
section is normal in its parabolic, and H normalizes both factors.
In the actual local closure, N(U) lies in B. The proved SL2 Sylow-normalizer
lemma therefore makes its local image the full Sylow image. The section
maps to one, whereas the simple root maps injectively, giving equality
before projection. Conjugation transports the result to every rootAt.

In a quadrangle, the root-commutator bound and Cartan invariance now turn
nontriviality into the exact crossed-root equality. No derived-order or
scalar-label premise is used, and PSL2(2) is included. The local model
marking and the earlier section 2/5 kernel containment remain explicit;
this theorem does not identify an original F.1 rank-one model with L_i.

Source: Fong--Seitz I (3G), (5C), and (6A), pp.14--16,26,37--38;
the normalizer action is the standard binary SL2 diagonal-square action.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem simpleRoot_sup_remainder (i : Fin 2) :
    simpleRoot Q split i ⊔ simpleRemainder Q split i = split.U := by
  apply le_antisymm (sup_le (simpleRoot_le Q split i) inf_le_left)
  intro x hx
  have hx' : x ∈ (simpleRoot Q split i : Set (X ⧸ Q.D)) *
      (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
    rw [simpleRoot_mul_remainder]; exact hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hx'
  exact mul_mem_sup ha hb

/-- The Cartan acts irreducibly on an actual binary linear root. -/
theorem simpleRoot_eq_of_torus_invariant {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : localGroup Q split i ≃* PSL(2,F))
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ simpleRoot Q split i) (hne : A ≠ ⊥)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D))) :
    A = simpleRoot Q split i := by
  let C := localClosure Q split i
  let V := simpleRemainder Q split i
  let W := A ⊔ V
  have hUC : split.U ≤ C := le_sup_left
  have hVC : V ≤ C := inf_le_left.trans hUC
  have hAC : A ≤ C := hA.trans ((simpleRoot_le Q split i).trans hUC)
  have hWU : W ≤ split.U := sup_le (hA.trans (simpleRoot_le Q split i)) inf_le_left
  have hB : Q.tits.B ≤ normalizer (W : Set (X ⧸ Q.D)) := by
    have hVP := remainder_parabolic_normalizes Q split i hV
    have hUN : simpleRoot Q split i ≤ normalizer (W : Set (X ⧸ Q.D)) := by
      have hcomm := simpleRoot_commutator_eq_bot_of_linear Q split i μ
      have hAN : simpleRoot Q split i ≤ normalizer (A : Set (X ⧸ Q.D)) :=
        ((commutator_eq_bot_iff_le_centralizer.mp
          (bot_unique ((commutator_mono le_rfl hA).trans hcomm.le))).trans
          (Subgroup.centralizer_le_normalizer _))
      exact (le_inf hAN ((simpleRoot_le Q split i).trans
        (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans hVP)))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hVN : V ≤ normalizer (W : Set (X ⧸ Q.D)) := le_sup_right.trans W.le_normalizer
    have hHU : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) :=
      (le_inf hH (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans hVP))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    rw [← split.factorization, ← simpleRoot_sup_remainder Q split i]
    exact sup_le (sup_le hUN hVN) hHU
  let T : Sylow 2 C := split.sylow.subtype hUC
  let ν := μ.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let f : C →* SL(2,F) := ν.toMonoidHom.comp (localAction Q split i).rangeRestrict
  have hf : Function.Surjective f := ν.surjective.comp (MonoidHom.rangeRestrict_surjective _)
  have hk (c : C) : f c = 1 ↔ (c : X ⧸ Q.D) ∈ localKernel Q i := by
    have hν : f c = 1 ↔ (localAction Q split i).rangeRestrict c = 1 := by
      exact ν.map_eq_one_iff
    rw [hν, Subtype.ext_iff]
    change localAction Q split i c = 1 ↔ _
    change c ∈ (localAction Q split i).ker ↔ _
    rw [localAction_ker]; rfl
  have hnormal : normalizer (T : Set C) ≤ normalizer (W.subgroupOf C : Set C) := by
    change normalizer (split.U.subgroupOf C : Set C) ≤ _
    rw [← subgroupOf_normalizer_eq hUC, split.normalizer_eq]
    exact (comap_mono hB).trans (W.le_normalizer_comap C.subtype)
  have hWne : ¬ W.subgroupOf C ≤ f.ker := by
    intro he
    apply hne
    apply eq_bot_iff.mpr
    intro a ha
    have hv := (hk ⟨a,hAC ha⟩).mp (he (show (⟨a,hAC ha⟩ : C) ∈ W.subgroupOf C from (show A ≤ W from le_sup_left) ha))
    exact (disjoint_iff.mp (simpleRoot_disjoint_localKernel Q split i)).le ⟨hA ha,hv⟩
  have heq := Matrix.SpecialLinearGroup.normalizer_invariant_image_eq_sylow T f hf
    (W.subgroupOf C) (subgroupOf_mono C hWU) hWne hnormal
  have hVmap : (V.subgroupOf C).map f = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro v hv
    exact (hk v).mpr (hV hv)
  have heqA : (A.subgroupOf C).map f = ((simpleRoot Q split i).subgroupOf C).map f := by
    change (W.subgroupOf C).map f = (split.U.subgroupOf C).map f at heq
    rw [show W = A ⊔ V from rfl, subgroupOf_sup hAC hVC, Subgroup.map_sup, hVmap, sup_bot_eq,
      ← simpleRoot_sup_remainder Q split i,
      subgroupOf_sup ((simpleRoot_le Q split i).trans hUC) hVC,
      Subgroup.map_sup, hVmap, sup_bot_eq] at heq
    exact heq
  apply le_antisymm hA
  intro u hu
  have hm : f ⟨u,(simpleRoot_le Q split i hu |> hUC)⟩ ∈ (A.subgroupOf C).map f := by
    rw [heqA]
    exact mem_map_of_mem f hu
  obtain ⟨a,ha,he⟩ := hm
  have hkernel : (a : X ⧸ Q.D)⁻¹*u ∈ localKernel Q i := by
    apply (hk (a⁻¹ * ⟨u,hUC (simpleRoot_le Q split i hu)⟩)).mp
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hone : (a : X ⧸ Q.D)⁻¹*u = 1 :=
    (disjoint_iff.mp (simpleRoot_disjoint_localKernel Q split i)).le
      ⟨(simpleRoot Q split i).mul_mem ((simpleRoot Q split i).inv_mem (hA ha)) hu,hkernel⟩
  have hua : u = (a : X ⧸ Q.D) := (inv_mul_eq_one.mp hone).symm
  exact hua ▸ ha
/-- The same irreducibility holds after conjugation by any Weyl representative. -/
theorem rootAt_eq_of_torus_invariant {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : localGroup Q split i ≃* PSL(2,F))
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (w : Weyl Q)
    (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ rootAt Q split i w) (hne : A ≠ ⊥)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D))) :
    A = rootAt Q split i w := by
  let n := representative w
  let A' := rightConjugate A ((n : X ⧸ Q.D)⁻¹)
  have hA' : A' ≤ simpleRoot Q split i := by
    have hc := comap_mono (f := (MulAut.conj ((n : X ⧸ Q.D)⁻¹)).toMonoidHom) hA
    change A' ≤ rightConjugate (rootAt Q split i w) ((n⁻¹ : Q.tits.N) : X ⧸ Q.D) at hc
    rw [rootAt_right Q split i w w⁻¹ n⁻¹ (by rw [map_inv, representative_spec]),
      mul_inv_cancel,rootAt_one] at hc
    exact hc
  have hne' : A' ≠ ⊥ := by
    intro hz
    apply hne
    have he := congrArg (fun B => rightConjugate B (n : X ⧸ Q.D)) hz
    change rightConjugate (rightConjugate A ((n : X ⧸ Q.D)⁻¹)) (n : X ⧸ Q.D) = _ at he
    rw [← rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at he
    exact he.trans (by simp only [rightConjugate, comap_equiv_eq_map_symm', Subgroup.map_bot])
  have he := simpleRoot_eq_of_torus_invariant Q split i μ hV A' hA' hne'
    (torus_normalizes_rightConjugate A hH n⁻¹)
  have hh := congrArg (fun B => rightConjugate B (n : X ⧸ Q.D)) he
  change rightConjugate (rightConjugate A ((n : X ⧸ Q.D)⁻¹)) (n : X ⧸ Q.D) = _ at hh
  rw [← rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at hh
  exact hh

/-- A nonzero opposite-root commutator fills its intervening binary linear root.
The source scalar action is derived from the actual local permutation marking. -/
theorem cross_root_commutator_eq_of_nonzero {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split i ≃* PSL(2,F))
    (hne : ⁅simpleRoot Q split j, rootAt Q split j (Q.simple i)⁆ ≠ ⊥) :
    ⁅simpleRoot Q split j, rootAt Q split j (Q.simple i)⁆ = rootAt Q split i (Q.simple j) := by
  apply rootAt_eq_of_torus_invariant Q split i μ hVi (Q.simple j) _
    (cross_root_commutator_le Q split hm j i hij.symm hVj) hne
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (torus_normalizes_simpleRoot Q split j hn),
    mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split j (Q.simple i) hn)]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
