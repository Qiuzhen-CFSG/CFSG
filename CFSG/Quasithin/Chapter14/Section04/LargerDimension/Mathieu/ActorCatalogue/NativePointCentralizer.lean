module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SylowOrbit
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Structure

/-!
# Native Sylow-fixed binary point centralizers

The proved one-dimensional Sylow fixed space and genuine conjugation put
every nonzero Sylow-fixed binary vector in the orbit of vector 1327. The
reference stabilizer equivalence then identifies its literal centralizer
with the native Mathieu quintet group. This supplies the elementary abelian
intrinsic two-core of order 32 and the actual quotient isomorphism to S₅,
including its equation on the five-tetrad action.

The Sylow image fixes a letter in this quotient. Its point-stabilizer
preimage is the Borel containing the original Sylow with relative index
three, and its two-residual fixes the original binary vector. The quotient
map and the chosen letter are retained. The uniform theorems require only
a nonzero vector fixed by the given Sylow; the earlier conditional transport
interfaces remain available. Source/group assembly for the rest of 14.4.12
is separate.

Source: Aschbacher--Smith, 14.4.12, printed pp.1011--1012, H.12.1, printed
pp.393--394, and the native local structure in H.14.3, printed p.397
(1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native

private theorem quintet_core_elementary :
    IsElementaryAbelian 2 (pCore 2 MathieuCode.M22Quintet.Q) := by
  have h : IsElementaryAbelian 2
      (MathieuCode.M22Quintet.K.subgroupOf MathieuCode.M22Quintet.Q) :=
    IsElementaryAbelian.subgroupOf (map_subtype_le _)
  change IsElementaryAbelian 2 (((pCore 2 MathieuCode.M22Quintet.Q).map
    MathieuCode.M22Quintet.Q.subtype).comap MathieuCode.M22Quintet.Q.subtype) at h
  rwa [comap_map_eq_self_of_injective MathieuCode.M22Quintet.Q.subtype_injective] at h

private theorem quintet_core_card : Nat.card (pCore 2 MathieuCode.M22Quintet.Q) = 32 := by
  have h := Sporadic.Mathieu.M22ChapterH.Quintet.core_card
  change Nat.card ((pCore 2 MathieuCode.M22Quintet.Q).map
    MathieuCode.M22Quintet.Q.subtype) = 32 at h
  rwa [card_map_of_injective MathieuCode.M22Quintet.Q.subtype_injective] at h

/-- The genuine quintet theorem supplies the intrinsic core assertions once
an actual stabilizer equivalence has been constructed. -/
theorem pointCentralizer_core_of_quintet_equiv (v : Space)
    (e : pointCentralizer v ≃* MathieuCode.M22Quintet.Q) :
    IsElementaryAbelian 2 (pCore 2 (pointCentralizer v)) ∧
      Nat.card (pCore 2 (pointCentralizer v)) = 32 := by
  have hm := pCore_map_iso 2 e.symm
  constructor
  · let := quintet_core_elementary
    rw [← hm]
    exact IsElementaryAbelian.map e.symm.toMonoidHom
  · rw [← hm, card_map_of_injective e.symm.injective, quintet_core_card]

/-- Transport the actual five-tetrad action through an honest carrier
comparison and the two intrinsic quotient maps. -/
noncomputable def pointCentralizerQuotientOfQuintetEquiv (v : Space)
    (e : pointCentralizer v ≃* MathieuCode.M22Quintet.Q) :
    coreQuotient (pointCentralizer v) ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    Sporadic.Mathieu.M22ChapterH.Quintet.quotientEquiv

@[simp] theorem pointCentralizerQuotientOfQuintetEquiv_mk (v : Space)
    (e : pointCentralizer v ≃* MathieuCode.M22Quintet.Q) (x : pointCentralizer v) :
    pointCentralizerQuotientOfQuintetEquiv v e
        (QuotientGroup.mk' (pCore 2 (pointCentralizer v)) x) =
      MathieuCode.M22Quintet.CocodeTransfer.NaturalQuotient.q (e x) := rfl

/-- Conditional assembly at the native centralizer, with the literal Borel
and its residual retained. The remaining premise is a carrier equivalence,
not a group-family tag or equality of orders. -/
theorem pointCentralizer_borel_of_quintet_equiv (S : Sylow 2 Model) (v : Space)
    (hv : ∀ s : S, action s.val v = v)
    (e : pointCentralizer v ≃* MathieuCode.M22Quintet.Q) :
    IsElementaryAbelian 2 (pCore 2 (pointCentralizer v)) ∧
      Nat.card (pCore 2 (pointCentralizer v)) = 32 ∧
      ∃ (q : pointCentralizer v →* Equiv.Perm (Fin 5)) (i : Fin 5),
        Function.Surjective q ∧ q.ker = pCore 2 (pointCentralizer v) ∧
        (S : Subgroup Model) ≤ pointBorel v q i ∧
        pointBorel v q i ≤ pointCentralizer v ∧
        (S : Subgroup Model).relIndex (pointBorel v q i) = 3 ∧
        ∀ x : borelActor (pointBorel v q i), action x.val v = v := by
  obtain ⟨he, hc⟩ := pointCentralizer_core_of_quintet_equiv v e
  let f := pointCentralizerQuotientOfQuintetEquiv v e
  obtain ⟨i, hS, hC, hi⟩ := exists_pointBorel_of_equiv S v hv f
  exact ⟨he, hc, pointQuotient v f, i, pointQuotient_surjective v f,
    pointQuotient_ker v f, hS, hC, hi, borelActor_fixes v _ i⟩

/-- Reduction to one reference stabilizer and the independently proved
Sylow-fixed-vector orbit. Final assembly must supply both premises. -/
theorem pointCentralizer_borel_of_reference (S : Sylow 2 Model) (v : Space)
    (hv : ∀ s : S, action s.val v = v)
    (e : pointCentralizer referenceVector ≃* MathieuCode.M22Quintet.Q)
    (ho : ∃ g : Model, action g referenceVector = v) :
    IsElementaryAbelian 2 (pCore 2 (pointCentralizer v)) ∧
      Nat.card (pCore 2 (pointCentralizer v)) = 32 ∧
      ∃ (q : pointCentralizer v →* Equiv.Perm (Fin 5)) (i : Fin 5),
        Function.Surjective q ∧ q.ker = pCore 2 (pointCentralizer v) ∧
        (S : Subgroup Model) ≤ pointBorel v q i ∧
        pointBorel v q i ≤ pointCentralizer v ∧
        (S : Subgroup Model).relIndex (pointBorel v q i) = 3 ∧
        ∀ x : borelActor (pointBorel v q i), action x.val v = v := by
  obtain ⟨g, rfl⟩ := ho
  exact pointCentralizer_borel_of_quintet_equiv S _ hv
    ((pointCentralizerConjEquiv g referenceVector).symm.trans e)

/-- The native Sylow fixed line has a unique nonzero binary vector.
Conjugating this line therefore transports the vector itself to 1327. -/
theorem sylow_fixedVector_mem_referenceOrbit (S : Sylow 2 Model) (v : Space) (hne : v ≠ 0)
    (hv : ∀ s : S, action s.val v = v) :
    ∃ g : Model, action g referenceVector = v := by
  obtain ⟨g, _, hg⟩ := ModuleGeometry.Native.exists_sylow_coordinates S
  have hm : ModuleGeometry.Native.actionEquiv g v ∈
      ModuleGeometry.Native.binaryLine ModuleGeometry.Native.markedVector := by
    rw [← hg]
    exact Submodule.mem_map_of_mem hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have hn : ModuleGeometry.Native.actionEquiv g v ≠ 0 := by
    intro hz
    exact hne ((ModuleGeometry.Native.actionEquiv g).injective (hz.trans (map_zero _).symm))
  have he : ModuleGeometry.Native.actionEquiv g v = ModuleGeometry.Native.markedVector := by
    have ha01 := (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide +kernel) a
    rcases ha01 with rfl | rfl
    · simp only [zero_smul] at ha
      exact (hn ha.symm).elim
    · simpa only [one_smul] using ha.symm
  change action g v = referenceVector at he
  refine ⟨g⁻¹, ?_⟩
  rw [← he, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply]

/-- An actual carrier equivalence for each nonzero Sylow-fixed binary vector,
using conjugation followed by the proved reference stabilizer comparison. -/
noncomputable def pointCentralizerEquiv (S : Sylow 2 Model) (v : Space) (hne : v ≠ 0)
    (hv : ∀ s : S, action s.val v = v) :
    pointCentralizer v ≃* MathieuCode.M22Quintet.Q := by
  let g := (sylow_fixedVector_mem_referenceOrbit S v hne hv).choose
  have hg : action g referenceVector = v :=
    (sylow_fixedVector_mem_referenceOrbit S v hne hv).choose_spec
  rw [← hg]
  exact (pointCentralizerConjEquiv g referenceVector).symm.trans referencePointCentralizerEquiv

/-- The elementary E₃₂ is the intrinsic two-core of the binary stabilizer. -/
theorem pointCentralizer_core (S : Sylow 2 Model) (v : Space) (hne : v ≠ 0)
    (hv : ∀ s : S, action s.val v = v) :
    IsElementaryAbelian 2 (pCore 2 (pointCentralizer v)) ∧
      Nat.card (pCore 2 (pointCentralizer v)) = 32 :=
  pointCentralizer_core_of_quintet_equiv v (pointCentralizerEquiv S v hne hv)

theorem pointCentralizer_core_elementary (S : Sylow 2 Model) (v : Space) (hne : v ≠ 0)
    (hv : ∀ s : S, action s.val v = v) :
    IsElementaryAbelian 2 (pCore 2 (pointCentralizer v)) :=
  (pointCentralizer_core S v hne hv).1

/-- The native order input used by `source_WStar_eq_twoCore`. -/
theorem pointCentralizer_core_card (S : Sylow 2 Model) (v : Space) (hne : v ≠ 0)
    (hv : ∀ s : S, action s.val v = v) :
    Nat.card (pCore 2 (pointCentralizer v)) = 32 :=
  (pointCentralizer_core S v hne hv).2

/-- The literal intrinsic two-core quotient, with no structural premise. -/
noncomputable def pointCentralizerQuotientEquiv (S : Sylow 2 Model) (v : Space) (hne : v ≠ 0)
    (hv : ∀ s : S, action s.val v = v) :
    coreQuotient (pointCentralizer v) ≃* Equiv.Perm (Fin 5) :=
  pointCentralizerQuotientOfQuintetEquiv v (pointCentralizerEquiv S v hne hv)

/-- The quotient equivalence retains the actual five-tetrad permutation map. -/
@[simp] theorem pointCentralizerQuotientEquiv_mk
    (S : Sylow 2 Model) (v : Space) (hne : v ≠ 0)
    (hv : ∀ s : S, action s.val v = v) (x : pointCentralizer v) :
    pointCentralizerQuotientEquiv S v hne hv
        (QuotientGroup.mk' (pCore 2 (pointCentralizer v)) x) =
      MathieuCode.M22Quintet.CocodeTransfer.NaturalQuotient.q
        (pointCentralizerEquiv S v hne hv x) :=
  pointCentralizerQuotientOfQuintetEquiv_mk v (pointCentralizerEquiv S v hne hv) x

/-- Pull back a letter stabilizer through the constructed quotient map.
The resulting Borel has index three over S, and its residual fixes v. -/
theorem exists_pointBorel (S : Sylow 2 Model) (v : Space) (hne : v ≠ 0)
    (hv : ∀ s : S, action s.val v = v) :
    let q := pointQuotient v (pointCentralizerQuotientEquiv S v hne hv)
    ∃ i : Fin 5, (S : Subgroup Model) ≤ pointBorel v q i ∧
      pointBorel v q i ≤ pointCentralizer v ∧
      (S : Subgroup Model).relIndex (pointBorel v q i) = 3 ∧
      ∀ x : borelActor (pointBorel v q i), action x.val v = v := by
  obtain ⟨i, hS, hC, hi⟩ := exists_pointBorel_of_equiv S v hv
    (pointCentralizerQuotientEquiv S v hne hv)
  exact ⟨i, hS, hC, hi, borelActor_fixes v _ i⟩

/-- The complete native point-centralizer and Borel calculation used in
14.4.12. Only the nonzero Sylow-fixed-vector premises remain. -/
theorem pointCentralizer_borel (S : Sylow 2 Model) (v : Space) (hne : v ≠ 0)
    (hv : ∀ s : S, action s.val v = v) :
    IsElementaryAbelian 2 (pCore 2 (pointCentralizer v)) ∧
      Nat.card (pCore 2 (pointCentralizer v)) = 32 ∧
      ∃ (q : pointCentralizer v →* Equiv.Perm (Fin 5)) (i : Fin 5),
        Function.Surjective q ∧ q.ker = pCore 2 (pointCentralizer v) ∧
        (S : Subgroup Model) ≤ pointBorel v q i ∧
        pointBorel v q i ≤ pointCentralizer v ∧
        (S : Subgroup Model).relIndex (pointBorel v q i) = 3 ∧
        ∀ x : borelActor (pointBorel v q i), action x.val v = v :=
  pointCentralizer_borel_of_quintet_equiv S v hv (pointCentralizerEquiv S v hne hv)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
