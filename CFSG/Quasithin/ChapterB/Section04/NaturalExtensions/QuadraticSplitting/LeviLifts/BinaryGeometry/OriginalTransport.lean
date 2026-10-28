module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry.Models
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
/-!
# Original natural coordinates for the binary Levi

For a degree-one defining field, the quotient marking identifies the literal
axis stabilizer and pointwise line fixer with the binary coordinate Levi.
That Levi consists exactly of matrices whose distinguished row and column
are those of the identity, so inverse transpose preserves it and reverses
its elementary roots.

The original natural submodule is transported separately. In the direct
marking, change its coordinates by the recorded matrix B. In the dual marking,
change them by the inverse transpose of B. The resulting actors are respectively
the quotient actor and its inverse transpose. Restricting these actual actor
and vector equivalences gives `nonempty_originalCoordinates`, including the
root alternatives required by `coordinates_of_block_and_original` in the
parent BinaryGeometry module. No splitting or choice of fixed lift is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.4.9(1), printed pp.92–93: the original natural
module restricted to the Levi fixing the chosen quotient line and axis.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open Representation.OneCohomology.SLHigherNatural Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry
open QuasisimpleSource
variable {F : BinaryField} {n : ℕ}

private theorem transpose_inv' {k : Type*} [CommRing k]
    (x : Matrix.SpecialLinearGroup (Fin n) k) :
    transpose x⁻¹ = (transpose x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  rw [coe_mul, coe_transpose, coe_transpose, ← Matrix.transpose_mul,
    ← coe_mul, mul_inv_cancel, coe_one, Matrix.transpose_one]

/-- Compatibility with the transpose-of-inverse convention in the quotient marking. -/
private theorem graphSL_eq (x : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    BinaryLinear.OuterCyclic.graphSL n x = transpose x⁻¹ :=
  (transpose_inv' x).symm

private theorem graphSL_involutive (x : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    BinaryLinear.OuterCyclic.graphSL n (BinaryLinear.OuterCyclic.graphSL n x) = x :=
  (BinaryLinear.OuterCyclic.graphSL n).left_inv x

private theorem natural_single (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (i k : Fin n) : specialLinearNatural n g (Pi.single i 1) k = g.val k i := by
  simp [specialLinearNatural_apply, Matrix.mulVec_single]

/-- Both the row and the column are fixed because the line is fixed pointwise. -/
private theorem mem_standardLevi_iff (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (j : Fin n) : g ∈ standardLevi n j ↔
    (∀ i, g.val j i = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) j i) ∧
    (∀ i, g.val i j = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j) := by
  constructor
  · rintro ⟨haxis, _, hline⟩
    have hc : ∀ i, g.val i j = (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) i := by
      intro i
      have h := congrFun (hline (Pi.single j 1) (Submodule.subset_span (Set.mem_singleton _))) i
      simpa only [natural_single] using h
    constructor
    · intro i
      by_cases hi : i = j
      · subst i
        simpa using hc j
      · have h := (haxis (Pi.single i 1)).mpr (by
          change (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) j = 0
          simp [Ne.symm hi])
        change specialLinearNatural n g (Pi.single i 1) j = 0 at h
        simpa [natural_single, Matrix.one_apply, Ne.symm hi] using h
    · intro i
      simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using hc i
  · rintro ⟨hr, hc⟩
    constructor
    · intro v
      change specialLinearNatural n g v j = 0 ↔ v j = 0
      have hv : specialLinearNatural n g v j = v j := by
        change (∑ i, g.val j i * v i) = v j
        calc
          _ = ∑ i, (1 : Matrix (Fin n) (Fin n) (ZMod 2)) j i * v i :=
            Finset.sum_congr rfl (fun i _ => congrArg (· * v i) (hr i))
          _ = v j := congrFun (Matrix.one_mulVec v) j
      rw [hv]
    · refine ⟨Subgroup.mem_top _, ?_⟩
      intro v hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul]
      congr 1
      funext i
      simpa [natural_single, Matrix.one_apply, Pi.single_apply, eq_comm] using hc i

private theorem transpose_mem_standardLevi {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    {j : Fin n} (h : g ∈ standardLevi n j) : transpose g ∈ standardLevi n j := by
  rw [mem_standardLevi_iff] at h ⊢
  constructor
  · intro i
    simpa [Matrix.one_apply, eq_comm] using h.2 i
  · intro i
    simpa [Matrix.one_apply, eq_comm] using h.1 i

private theorem graphSL_mem_standardLevi (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (j : Fin n) : BinaryLinear.OuterCyclic.graphSL n g ∈ standardLevi n j ↔
    g ∈ standardLevi n j := by
  have hf : ∀ x ∈ standardLevi n j, BinaryLinear.OuterCyclic.graphSL n x ∈ standardLevi n j := by
    intro x hx
    rw [graphSL_eq]
    exact transpose_mem_standardLevi ((standardLevi n j).inv_mem hx)
  refine ⟨fun h => ?_, hf g⟩
  simpa only [graphSL_involutive] using hf _ h

private theorem graphSL_root {a b : Fin n} (hab : a ≠ b) :
    BinaryLinear.OuterCyclic.graphSL n (transvection hab 1) = transvection hab.symm 1 := by
  rw [graphSL_eq, transvection_inv]
  apply Subtype.ext
  simp [transvection_coe, Matrix.transpose_add, Matrix.transpose_single]

private theorem fieldEquiv_graph (hF : F.degree = 1)
    (x : Matrix.SpecialLinearGroup (Fin n) F.Carrier) :
    (naturalFieldEquiv hF n).groupEquiv (transpose x⁻¹) =
      BinaryLinear.OuterCyclic.graphSL n ((naturalFieldEquiv hF n).groupEquiv x) := by
  rw [graphSL_eq, ← map_inv]
  rfl

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {d : DoubleNatural F n ρ}

private noncomputable def quotientBinary (m : QuotientCoordinates d) (hF : F.degree = 1) :
    ActionEquiv d.space.quotientRepresentation (specialLinearNatural (k := ZMod 2) n) where
  groupEquiv := m.action.groupEquiv.trans (naturalFieldEquiv hF n).groupEquiv
  linearEquiv := m.action.linearEquiv.trans (naturalFieldEquiv hF n).linearEquiv
  intertwines g v := by
    change (naturalFieldEquiv hF n).linearEquiv (m.action.linearEquiv (_)) = _
    rw [m.action.intertwines, (naturalFieldEquiv hF n).intertwines]
    rfl

private theorem field_single (hF : F.degree = 1) (j : Fin n) (c : F.Carrier) :
    (naturalFieldEquiv hF n).linearEquiv (c • Pi.single j 1) =
      fieldEquiv hF c • Pi.single j 1 := by
  funext i
  change fieldEquiv hF (c * (Pi.single j (1 : F.Carrier) : Fin n → F.Carrier) i) =
    fieldEquiv hF c * (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) i
  by_cases hi : i = j <;> simp [hi]

private theorem quotientBinary_axis (m : QuotientCoordinates d) (hF : F.degree = 1)
    (j : Fin n) (v : V ⧸ d.space.toSubmodule) :
    (quotientBinary m hF).linearEquiv v ∈ standardAxis n j ↔ v ∈ m.axis j := by
  change fieldEquiv hF (m.action.linearEquiv v j) = 0 ↔ m.action.linearEquiv v j = 0
  exact (fieldEquiv hF).map_eq_zero_iff

private theorem quotientBinary_line (m : QuotientCoordinates d) (hF : F.degree = 1)
    (j : Fin n) (v : V ⧸ d.space.toSubmodule) :
    (quotientBinary m hF).linearEquiv v ∈ standardLine n j ↔ v ∈ m.line j := by
  change (naturalFieldEquiv hF n).linearEquiv (m.action.linearEquiv v) ∈
    Submodule.span (ZMod 2) {Pi.single j 1} ↔
    m.action.linearEquiv v ∈ Submodule.span F.Carrier {Pi.single j 1}
  rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(fieldEquiv hF).symm c, (naturalFieldEquiv hF n).linearEquiv.injective ?_⟩
    rw [field_single, RingEquiv.apply_symm_apply]
    exact hc
  · rintro ⟨c, hc⟩
    refine ⟨fieldEquiv hF c, ?_⟩
    rw [← field_single, hc]

/-- The quotient-defined subgroup is exactly the standard Levi under field transport. -/
private theorem quotientBinary_mem_Levi (m : QuotientCoordinates d) (hF : F.degree = 1)
    (j : Fin n) (g : G) :
    (quotientBinary m hF).groupEquiv g ∈ standardLevi n j ↔ g ∈ m.K j := by
  constructor
  · rintro ⟨ha, _, hl⟩
    refine ⟨?_, Subgroup.mem_top _, ?_⟩
    · intro v
      rw [← quotientBinary_axis m hF, ← quotientBinary_axis m hF,
        (quotientBinary m hF).intertwines]
      exact ha _
    · intro v hv
      apply (quotientBinary m hF).linearEquiv.injective
      rw [(quotientBinary m hF).intertwines]
      exact hl _ ((quotientBinary_line m hF j v).mpr hv)
  · rintro ⟨ha, _, hl⟩
    refine ⟨?_, Subgroup.mem_top _, ?_⟩
    · intro w
      obtain ⟨v, rfl⟩ := (quotientBinary m hF).linearEquiv.surjective w
      rw [← (quotientBinary m hF).intertwines, quotientBinary_axis, quotientBinary_axis]
      exact ha v
    · intro w hw
      obtain ⟨v, rfl⟩ := (quotientBinary m hF).linearEquiv.surjective w
      rw [← (quotientBinary m hF).intertwines, hl v ((quotientBinary_line m hF j v).mp hw)]

/-- Change coordinates on the original natural submodule, retaining its actual action. -/
private noncomputable def originalConjugate (d : DoubleNatural F n ρ) (hF : F.degree = 1)
    (C : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    ActionEquiv d.space.toRepresentation (specialLinearNatural (k := ZMod 2) n) where
  groupEquiv := (d.natural.groupEquiv.trans (naturalFieldEquiv hF n).groupEquiv).trans
    (MulAut.conj C)
  linearEquiv := (d.natural.linearEquiv.trans (naturalFieldEquiv hF n).linearEquiv).trans
    (toLin' C)
  intertwines g v := by
    change specialLinearNatural n C ((naturalFieldEquiv hF n).linearEquiv
      (d.natural.linearEquiv (d.space.toRepresentation g v))) =
      specialLinearNatural n (C * (naturalFieldEquiv hF n).groupEquiv
        (d.natural.groupEquiv g) * C⁻¹)
        (specialLinearNatural n C ((naturalFieldEquiv hF n).linearEquiv (d.natural.linearEquiv v)))
    rw [d.natural.intertwines, (naturalFieldEquiv hF n).intertwines]
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

private theorem originalConjugate_direct (m : QuotientCoordinates d) (hF : F.degree = 1)
    (h : ∀ g, m.action.groupEquiv g =
      m.basisChange * d.natural.groupEquiv g * m.basisChange⁻¹) (g : G) :
    (originalConjugate d hF ((naturalFieldEquiv hF n).groupEquiv m.basisChange)).groupEquiv g =
      (quotientBinary m hF).groupEquiv g := by
  change (naturalFieldEquiv hF n).groupEquiv m.basisChange *
    (naturalFieldEquiv hF n).groupEquiv (d.natural.groupEquiv g) *
    ((naturalFieldEquiv hF n).groupEquiv m.basisChange)⁻¹ =
    (naturalFieldEquiv hF n).groupEquiv (m.action.groupEquiv g)
  rw [h g, map_mul, map_mul, map_inv]

private theorem originalConjugate_dual (m : QuotientCoordinates d) (hF : F.degree = 1)
    (h : ∀ g, m.action.groupEquiv g =
      m.basisChange * transpose ((d.natural.groupEquiv g)⁻¹) * m.basisChange⁻¹) (g : G) :
    (originalConjugate d hF (BinaryLinear.OuterCyclic.graphSL n
      ((naturalFieldEquiv hF n).groupEquiv m.basisChange))).groupEquiv g =
      BinaryLinear.OuterCyclic.graphSL n ((quotientBinary m hF).groupEquiv g) := by
  change BinaryLinear.OuterCyclic.graphSL n ((naturalFieldEquiv hF n).groupEquiv m.basisChange) *
    (naturalFieldEquiv hF n).groupEquiv (d.natural.groupEquiv g) *
    (BinaryLinear.OuterCyclic.graphSL n ((naturalFieldEquiv hF n).groupEquiv m.basisChange))⁻¹ =
    BinaryLinear.OuterCyclic.graphSL n ((naturalFieldEquiv hF n).groupEquiv (m.action.groupEquiv g))
  simp only [h g, map_mul, map_inv, fieldEquiv_graph, graphSL_involutive]

/-- Restrict both actual equivalences to the literal actor subgroups. -/
private noncomputable def restrictOriginal (m : QuotientCoordinates d) (j : Fin n)
    (e : ActionEquiv d.space.toRepresentation (specialLinearNatural (k := ZMod 2) n))
    (he : ∀ g, e.groupEquiv g ∈ standardLevi n j ↔ g ∈ m.K j) :
    ActionEquiv (d.space.toRepresentation.comp (m.K j).subtype) (standardAction n j) where
  groupEquiv :=
    { toFun g := ⟨e.groupEquiv g, (he g).mpr g.property⟩
      invFun g := ⟨e.groupEquiv.symm g, (he _).mp (by rw [e.groupEquiv.apply_symm_apply]; exact g.property)⟩
      left_inv g := Subtype.ext (e.groupEquiv.symm_apply_apply g)
      right_inv g := Subtype.ext (e.groupEquiv.apply_symm_apply g)
      map_mul' g h := Subtype.ext (e.groupEquiv.map_mul g h) }
  linearEquiv := e.linearEquiv
  intertwines g v := e.intertwines g v

/-- Transport the original natural submodule to the literal binary Levi, in either coherent
orientation of the quotient marking. -/
theorem nonempty_originalCoordinates (m : QuotientCoordinates d) (hF : F.degree = 1)
    (_hn : 4 ≤ n) (j : Fin n) : Nonempty (OriginalCoordinates m j) := by
  classical
  rcases m.marking with h | h
  · let e := originalConjugate d hF ((naturalFieldEquiv hF n).groupEquiv m.basisChange)
    have he (g : G) : e.groupEquiv g = (quotientBinary m hF).groupEquiv g :=
      originalConjugate_direct m hF h g
    have hm (g : G) : e.groupEquiv g ∈ standardLevi n j ↔ g ∈ m.K j := by
      rw [he, quotientBinary_mem_Levi]
    refine ⟨⟨restrictOriginal m j e hm, ?_⟩⟩
    intro a b hab haj hbj
    left
    apply Subtype.ext
    change e.groupEquiv (m.action.groupEquiv.symm (transvection hab 1)) = transvection hab 1
    rw [he]
    change (naturalFieldEquiv hF n).groupEquiv
      (m.action.groupEquiv (m.action.groupEquiv.symm (transvection hab 1))) = _
    rw [MulEquiv.apply_symm_apply, naturalFieldEquiv_root]
  · let e := originalConjugate d hF (BinaryLinear.OuterCyclic.graphSL n
      ((naturalFieldEquiv hF n).groupEquiv m.basisChange))
    have he (g : G) : e.groupEquiv g =
        BinaryLinear.OuterCyclic.graphSL n ((quotientBinary m hF).groupEquiv g) :=
      originalConjugate_dual m hF h g
    have hm (g : G) : e.groupEquiv g ∈ standardLevi n j ↔ g ∈ m.K j := by
      rw [he, graphSL_mem_standardLevi, quotientBinary_mem_Levi]
    refine ⟨⟨restrictOriginal m j e hm, ?_⟩⟩
    intro a b hab haj hbj
    right
    apply Subtype.ext
    change e.groupEquiv (m.action.groupEquiv.symm (transvection hab 1)) = transvection hab.symm 1
    rw [he]
    change BinaryLinear.OuterCyclic.graphSL n ((naturalFieldEquiv hF n).groupEquiv
      (m.action.groupEquiv (m.action.groupEquiv.symm (transvection hab 1)))) = _
    rw [MulEquiv.apply_symm_apply, naturalFieldEquiv_root, graphSL_root]

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts.BinaryGeometry
