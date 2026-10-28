module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.SpecialRadical
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryRootCenter
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.TorusIrreducibility

/-!
# The exact unitary center commutator on the marked quadrangle

A nonzero Cartan-invariant subgroup of the canonical root center maps
into the center of the actual local Sylow. Adjoining the complementary
section makes its preimage Borel-invariant. Sylow normalizer lifting and
the unitary inverse-norm action fill the image center. Faithfulness on
the canonical root then gives equality before projection. Right
conjugation transports the assertion to every crossed root.

The special beta radical makes the opposite linear-root commutator
nonzero, and the quadrangle commutator calculus bounds it by the crossed
unitary-root center. Thus the action argument proves the exact second
commutator equality of (6A)(c), including q = 2. The actual faithful
local PSU3 marking is an earlier-source input. The full SU3 actor and
the other mixed commutator are separate obligations, not conclusions
of this center-action calculation.

Source: Fong--Seitz I (3G), (5C), (6A)(c), pp.14--16,26,37;
DGS (11.8)(f), p.176. UnitaryCenterEquality applies the result to the
original cores through the same marked endpoint and overlap maps.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
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

/-- Normalizer irreducibility in the faithful local group lifts to the actual root center. -/
theorem simpleRoot_center_eq_of_torus_invariant {M : Type*} [Group M]
    (hmodel : ∀ (T : Sylow 2 M) (D : Subgroup M),
      D ≤ (center T).map (T : Subgroup M).subtype → D ≠ ⊥ →
      normalizer (T : Set M) ≤ normalizer (D : Set M) →
      D = (center T).map (T : Subgroup M).subtype)
    (i : Fin 2) (μ : localGroup Q split i ≃* M)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (A : Subgroup (X ⧸ Q.D)) (hAZ : A ≤ (center (simpleRoot Q split i)).map (simpleRoot Q split i).subtype) (hne : A ≠ ⊥)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D))) :
    A = (center (simpleRoot Q split i)).map (simpleRoot Q split i).subtype := by
  have hA : A ≤ simpleRoot Q split i := hAZ.trans (map_subtype_le _)
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
      have hAN : simpleRoot Q split i ≤ normalizer (A : Set (X ⧸ Q.D)) := by
        apply le_trans _ (Subgroup.centralizer_le_normalizer _)
        intro u hu
        apply mem_centralizer_iff.mpr
        intro a ha
        obtain ⟨z,hz,rfl⟩ := hAZ ha
        exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨u,hu⟩)).symm
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
  let f : C →* M := μ.toMonoidHom.comp (localAction Q split i).rangeRestrict
  have hf : Function.Surjective f := μ.surjective.comp (MonoidHom.rangeRestrict_surjective _)
  have hk (c : C) : f c = 1 ↔ (c : X ⧸ Q.D) ∈ localKernel Q i := by
    have hμ : f c = 1 ↔ (localAction Q split i).rangeRestrict c = 1 := by
      exact μ.map_eq_one_iff
    rw [hμ, Subtype.ext_iff]
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
  have hVmap : (V.subgroupOf C).map f = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro v hv
    exact (hk v).mpr (hV hv)
  have hroot : ((simpleRoot Q split i).subgroupOf C).map f = (T : Subgroup C).map f := by
    change _ = (split.U.subgroupOf C).map f
    rw [← simpleRoot_sup_remainder Q split i,
      subgroupOf_sup ((simpleRoot_le Q split i).trans hUC) hVC,
      Subgroup.map_sup, hVmap, sup_bot_eq]
  have hWA : (W.subgroupOf C).map f = (A.subgroupOf C).map f := by
    rw [show W = A ⊔ V from rfl,subgroupOf_sup hAC hVC,Subgroup.map_sup,hVmap,sup_bot_eq]
  have hZmap (u : X ⧸ Q.D)
      (hu : u ∈ (center (simpleRoot Q split i)).map (simpleRoot Q split i).subtype) :
      f ⟨u,hUC (simpleRoot_le Q split i ((map_subtype_le _) hu))⟩ ∈
        (center (T.mapSurjective hf)).map (T.mapSurjective hf : Subgroup M).subtype := by
    obtain ⟨z,hz,rfl⟩ := hu
    have hmem : f ⟨z,hUC (simpleRoot_le Q split i z.property)⟩ ∈ (T : Subgroup C).map f := by
      rw [←hroot]
      exact mem_map_of_mem f z.property
    refine ⟨⟨_,hmem⟩,mem_center_iff.mpr (fun t => ?_),rfl⟩
    have ht : (t : M) ∈ ((simpleRoot Q split i).subgroupOf C).map f := by
      rw [hroot]; exact t.property
    obtain ⟨v,hv,he⟩ := ht
    apply Subtype.ext
    change (t : M) * f _ = f _ * (t : M)
    rw [←he,←map_mul,←map_mul]
    apply congrArg f
    apply Subtype.ext
    exact congrArg (fun z : simpleRoot Q split i => (z : X ⧸ Q.D))
      (mem_center_iff.mp hz ⟨v,hv⟩)
  have heqA : (A.subgroupOf C).map f =
      (center (T.mapSurjective hf)).map (T.mapSurjective hf : Subgroup M).subtype := by
    rw [←hWA]
    apply hmodel (T.mapSurjective hf)
    · rw [hWA]
      rintro _ ⟨a,ha,rfl⟩
      exact hZmap a (hAZ ha)
    · exact fun hz => hWne ((Subgroup.map_eq_bot_iff _).mp hz)
    · change normalizer ((T : Subgroup C).map f : Set M) ≤ _
      rw [← T.normalizer_map_surjective f hf]
      exact (map_mono hnormal).trans ((W.subgroupOf C).le_normalizer_map f)
  apply le_antisymm hAZ
  intro u hu
  have hm : f ⟨u,(simpleRoot_le Q split i ((map_subtype_le _) hu) |> hUC)⟩ ∈ (A.subgroupOf C).map f := by
    rw [heqA]
    exact hZmap u hu
  obtain ⟨a,ha,he⟩ := hm
  have hkernel : (a : X ⧸ Q.D)⁻¹*u ∈ localKernel Q i := by
    apply (hk (a⁻¹ * ⟨u,hUC (simpleRoot_le Q split i ((map_subtype_le _) hu))⟩)).mp
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hone : (a : X ⧸ Q.D)⁻¹*u = 1 :=
    (disjoint_iff.mp (simpleRoot_disjoint_localKernel Q split i)).le
      ⟨(simpleRoot Q split i).mul_mem ((simpleRoot Q split i).inv_mem (hA ha)) ((map_subtype_le _) hu),hkernel⟩
  have hua : u = (a : X ⧸ Q.D) := (inv_mul_eq_one.mp hone).symm
  exact hua ▸ ha

/-- The intrinsic center follows right conjugation, embedded in the same ambient group. -/
theorem rightConjugate_center (A : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    rightConjugate ((center A).map A.subtype) n =
      (center (rightConjugate A n)).map (rightConjugate A n).subtype := by
  have he : rightConjugate A n = A.map (MulAut.conj n).symm.toMonoidHom :=
    comap_equiv_eq_map_symm' _ _
  rw [he,map_center_image_of_injective A (MulAut.conj n).symm.toMonoidHom
    (MulAut.conj n).symm.injective]
  change ((center A).map A.subtype).comap (MulAut.conj n).toMonoidHom = _
  rw [comap_equiv_eq_map_symm',map_map]

/-- Center irreducibility transports to every crossed root, before projection. -/
theorem rootAt_center_eq_of_torus_invariant {M : Type*} [Group M]
    (hmodel : ∀ (T : Sylow 2 M) (D : Subgroup M),
      D ≤ (center T).map (T : Subgroup M).subtype → D ≠ ⊥ →
      normalizer (T : Set M) ≤ normalizer (D : Set M) →
      D = (center T).map (T : Subgroup M).subtype)
    (i : Fin 2) (μ : localGroup Q split i ≃* M)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (w : Weyl Q)
    (A : Subgroup (X ⧸ Q.D))
    (hA : A ≤ (center (rootAt Q split i w)).map (rootAt Q split i w).subtype)
    (hne : A ≠ ⊥)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D))) :
    A = (center (rootAt Q split i w)).map (rootAt Q split i w).subtype := by
  let n := representative w
  let A' := rightConjugate A ((n : X ⧸ Q.D)⁻¹)
  have hA' : A' ≤ (center (simpleRoot Q split i)).map (simpleRoot Q split i).subtype := by
    have hc := comap_mono (f := (MulAut.conj ((n : X ⧸ Q.D)⁻¹)).toMonoidHom) hA
    change A' ≤ rightConjugate ((center (rootAt Q split i w)).map
      (rootAt Q split i w).subtype) ((n⁻¹ : Q.tits.N) : X ⧸ Q.D) at hc
    rw [rightConjugate_center,rootAt_right Q split i w w⁻¹ n⁻¹
      (by rw [map_inv, representative_spec]),mul_inv_cancel,rootAt_one] at hc
    exact hc
  have hne' : A' ≠ ⊥ := by
    intro hz
    apply hne
    have he := congrArg (fun B => rightConjugate B (n : X ⧸ Q.D)) hz
    change rightConjugate (rightConjugate A ((n : X ⧸ Q.D)⁻¹)) (n : X ⧸ Q.D) = _ at he
    rw [←rightConjugate_mul,inv_mul_cancel,rightConjugate_one] at he
    exact he.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot])
  have he := simpleRoot_center_eq_of_torus_invariant Q split hmodel i μ hV A' hA' hne'
    (torus_normalizes_rightConjugate A hH n⁻¹)
  have hh := congrArg (fun B => rightConjugate B (n : X ⧸ Q.D)) he
  change rightConjugate (rightConjugate A ((n : X ⧸ Q.D)⁻¹)) (n : X ⧸ Q.D) = _ at hh
  rw [←rightConjugate_mul,inv_mul_cancel,rightConjugate_one,rightConjugate_center] at hh
  exact hh

/-- The center-side equality of (6A)(c), in the SAME ambient marked quotient. -/
theorem unitary_cross_root_commutator_eq_center
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (hZ : (center (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype ≤
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype := by
  apply rootAt_center_eq_of_torus_invariant Q split
    (unitary_sylow_center_irreducible J hn hcard hfixed hJ) j μ hVj (Q.simple i) _
    (cross_root_commutator_le_center Q split hm i j hij hVi hVj)
    (cross_root_commutator_ne_bot_of_special_radical Q split hm i j hij hVi hVj hA hZ)
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (torus_normalizes_simpleRoot Q split i ht),
    mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split i (Q.simple j) ht)]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
