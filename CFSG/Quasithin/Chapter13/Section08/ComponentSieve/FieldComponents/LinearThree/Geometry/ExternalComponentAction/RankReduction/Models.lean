module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PrimeRankHom
public import Mathlib.LinearAlgebra.Pi
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.GroupTheory.CComponent.ThreeResidual

/-!
# Intrinsic facts for the exact list in 13.8.21(2)

Except for L₃(2), each listed quotient is centerless, contains an elementary
nine, and has outer order prime to three. For the linear groups use the actual
L₄(2) ≃ A₈ comparison, extension of linear maps to dimension five, and the
proved inner/graph automorphism coverage. The alternating cases use the checked
outer groups. In the actual octonion-derived G₂(2)' an explicit cubic and its
commutator give an elementary nine. Full-group conjugation coverage, still an
explicit input, makes its outer group a quotient of the group of order two.

These are the intrinsic model facts consumed by the first external-component
reduction of Aschbacher–Smith 13.8.21(1), combined manuscript of 1 March 2004,
printed p.956. They neither classify components nor prove the outstanding
G₂(2)' automorphism coverage. Both the list and that coverage remain explicit.

The octonion calculations adapt the coordinates in
`Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank`. The matrix models and
exceptional comparisons are from the licensed ATLAS port; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.RankReduction
private instance finiteLinear (n : ℕ) : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
  Finite.of_equiv SL(n, ZMod 2) (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv
private theorem center_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center B at he
  rw [h, mem_bot] at he
  exact e.map_eq_one_iff.mp he

private def fiveCoordinates : (Fin 5 → ZMod 2) ≃ₗ[ZMod 2]
    ZMod 2 × (Fin 4 → ZMod 2) :=
  (LinearEquiv.piCongrLeft (ZMod 2) (fun _ : Option (Fin 4) => ZMod 2)
    (finSuccEquiv 4)).trans (LinearEquiv.piOptionEquivProd (ZMod 2))

private def extendFour : BinaryLinear.OuterCyclic.LinearGroup 4 →*
    BinaryLinear.OuterCyclic.LinearGroup 5 where
  toFun g := fiveCoordinates.trans
    (((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr g).trans fiveCoordinates.symm)
  map_one' := by ext v i; simp [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]
  map_mul' g h := by
    ext v i
    simp [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]

private theorem extendFour_injective : Function.Injective extendFour := by
  intro g h he
  apply LinearEquiv.ext
  intro v
  have hh := congrArg (fun k : BinaryLinear.OuterCyclic.LinearGroup 5 =>
    (fiveCoordinates (k (fiveCoordinates.symm (0,v)))).2) he
  simpa [extendFour, LinearEquiv.trans_apply] using hh

private theorem binary_rank (n : ℕ) (hn : n = 4 ∨ n = 5) :
    2 ≤ primeRank 3 PSL(n, ZMod 2) := by
  have h4 : 2 ≤ primeRank 3 PSL(4, ZMod 2) := by
    rw [primeRank_congr 3 Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  rcases hn with rfl | rfl
  · exact h4
  · rw [primeRank_congr 3 (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))]
    rw [primeRank_congr 3 (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))] at h4
    exact h4.trans (Theory.GroupTheory.primeRank_le_of_injective 3 extendFour extendFour_injective)

private theorem binary_outer_two (n : ℕ) (hn : n = 4 ∨ n = 5) :
    IsPGroup 2 (MulAut.Outer PSL(n, ZMod 2)) := by
  have h : IsPGroup 2 (MulAut.Outer (BinaryLinear.OuterCyclic.LinearGroup n)) := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective _ x
    let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup n))
    obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.inner_graph hn a
    have hi : q (MulAut.conj g) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨g,rfl⟩
    refine ⟨1, ?_⟩
    change q a ^ 2 = 1
    rcases hg with rfl | rfl
    · rw [hi, one_pow]
    · rw [map_mul, hi, mul_one, ← map_pow, BinaryLinear.OuterCyclic.graphLinear_sq, map_one]
  exact h.of_equiv (MulAut.outerCongr
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n))).symm

private theorem binary_center (n : ℕ) (hn : 0 < n) : center PSL(n, ZMod 2) = ⊥ :=
  center_bot_transport (BinaryLinear.OuterCyclic.projectiveEquivSL hn)
    (BinaryLinear.OuterCyclic.binary_center_eq_bot hn)

/-- The surviving model has three-rank exactly one, by its order 168. -/
theorem rank_psl3 : primeRank 3 Matrix.PSL3Two.PSL = 1 := by
  let P : Sylow 3 Matrix.PSL3Two.PSL := Classical.choice inferInstance
  have hc : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, Matrix.PSL3Two.card_PSL]
    decide +kernel
  have hu := P.primeRank_le_one_of_isCyclic (isCyclic_of_prime_card hc)
  have hp : primeRank 3 Matrix.PSL3Two.PSL ≠ 0 := by
    intro hz
    have := (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)
    rw [Matrix.PSL3Two.card_PSL] at this
    exact this (by decide)
  omega
section Octonion
open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open Atlas.G2.LieAutomorphismExtensions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private theorem model_ext (g h : Model (ZMod 2))
    (he : ∀ i j, g.val (basisVector i) j = h.val (basisVector i) j) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact linearMap_ext _ _ (fun i => funext (he i))
private def x : Model (ZMod 2) := BinaryCore.movingActor
private def c : Model (ZMod 2) := rootD 1 * rootF 1 * weylS * rootF 1
private def y : Model (ZMod 2) := c * x * c⁻¹
private def z : Model (ZMod 2) := x * y * x⁻¹ * y⁻¹
private theorem z_cube : z ^ 3 = 1 := by
  apply model_ext
  exact (by decide +kernel : ∀ i j, (z ^ 3).val (basisVector i) j = (1 : Model (ZMod 2)).val (basisVector i) j)
private theorem x_z : x * z = z * x := by
  apply model_ext
  exact (by decide +kernel : ∀ i j, (x*z).val (basisVector i) j = (z*x).val (basisVector i) j)
private def xd : BinaryDerived := ⟨x, BinaryParabolicPair.movingActor_mem_derived⟩
private def zd : BinaryDerived := ⟨z, Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩
private theorem xd_cube : xd ^ 3 = 1 := Subtype.ext BinaryCore.movingActor_cube
private theorem zd_cube : zd ^ 3 = 1 := Subtype.ext z_cube
private theorem xd_zd : Commute xd zd := Subtype.ext x_z
private abbrev E := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
private theorem pow_add_three (g : BinaryDerived) (hg : g^3=1) (a b : ZMod 3) :
    g ^ (a+b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hg).symm
private def eval (a : E) : BinaryDerived := xd ^ a.1.toAdd.val * zd ^ a.2.toAdd.val
private def embedding : E →* BinaryDerived where
  toFun := eval
  map_one' := by change xd ^ 0 * zd ^ 0 = 1; simp
  map_mul' a b := by
    change xd ^ (a.1.toAdd + b.1.toAdd).val * zd ^ (a.2.toAdd + b.2.toAdd).val = _
    rw [pow_add_three xd xd_cube, pow_add_three zd zd_cube]
    exact (xd_zd.pow_pow b.1.toAdd.val a.2.toAdd.val).mul_mul_mul_comm _ _
private theorem embedding_injective : Function.Injective embedding := by
  intro a b h
  have he := congrArg (fun g : BinaryDerived => fun i j => g.val.val (basisVector i) j) h
  exact (by decide +kernel : Function.Injective (fun a : E =>
    fun (i j : Fin 8) => (eval a).val.val (basisVector i) j)) he
private theorem g2_rank_two : 2 ≤ primeRank 3 BinaryDerived := by
  apply primeRank_ge_of_elementary_embedding (A := E) (p := 3) (e := 2) _ _ embedding embedding_injective
  · exact (by decide : ∀ a : E, a ^ 3 = 1)
  · simp [E, Nat.card_eq_fintype_card]
private theorem g2_outer_two (hcover : Function.Surjective binaryConjugation) :
    IsPGroup 2 (MulAut.Outer BinaryDerived) := by
  have hc : Nat.card (Model (ZMod 2) ⧸ BinaryDerived) = 2 ^ 1 := by
    rw [← index_eq_card, binaryDerived_eq]
    exact BinaryException.index_H
  have ht := IsPGroup.of_card hc
  apply ht.of_surjective (MulAut.outerAction BinaryDerived)
  intro q
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨g,rfl⟩ := hcover a
  exact ⟨QuotientGroup.mk g, rfl⟩

end Octonion

open Atlas.G2.LieAutomorphismExtensions

private theorem coprime_three_of_two {A : Type*} [Group A] [Finite A] (h : IsPGroup 2 A) :
    Nat.Coprime 3 (Nat.card A) := by
  obtain ⟨n,hn⟩ := h.exists_card_dvd_pow
  exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn

/-- The exact actual-model list of 13.8.21(2); no list classification is asserted. -/
def SmallQuotient (A : Type*) [Group A] : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ Nonempty (A ≃* PSL(n, ZMod 2))) ∨
    Nonempty (A ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (A ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (A ≃* commutator (Atlas.G2.Model (ZMod 2)))

private theorem transport_facts {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (hz : center B = ⊥) (hr : 2 ≤ primeRank 3 B)
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer B))) :
    center A = ⊥ ∧ 2 ≤ primeRank 3 A ∧
      Nat.Coprime 3 (Nat.card (MulAut.Outer A)) := by
  refine ⟨center_bot_transport e hz, ?_, ?_⟩
  · rwa [primeRank_congr 3 e]
  · rwa [Nat.card_congr (MulAut.outerCongr e).toEquiv]

/-- The precise intrinsic input needed from the binary automorphism owner.
Surjectivity suffices; injectivity and a full automorphism identification
are unnecessary for the rank reduction. -/
theorem g2_outer_coprime_of_coverage (hcover : Function.Surjective binaryConjugation) :
    Nat.Coprime 3 (Nat.card (MulAut.Outer BinaryDerived)) :=
  coprime_three_of_two (g2_outer_two hcover)

/-- All listed models except L₃(2) are centerless, have three-rank at least
two, and have outer order prime to three. Only the last fact for the actual
G₂(2)' remains an explicit model premise. -/
theorem small_quotient_alternative_of_outer_coprime {A : Type*} [Group A] [Finite A]
    (houter : Nat.Coprime 3 (Nat.card (MulAut.Outer BinaryDerived)))
    (h : SmallQuotient A) :
    Nonempty (A ≃* Matrix.PSL3Two.PSL) ∨
      center A = ⊥ ∧ 2 ≤ primeRank 3 A ∧
        Nat.Coprime 3 (Nat.card (MulAut.Outer A)) := by
  unfold SmallQuotient at h
  rcases h with h | h | h | h
  · obtain ⟨n,hn,hn',⟨e⟩⟩ := h
    have hncase : n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hncase with rfl | hncase
    · exact Or.inl ⟨e⟩
    · exact Or.inr (transport_facts e (binary_center n (by omega)) (binary_rank n hncase)
        (coprime_three_of_two (binary_outer_two n hncase)))
  · obtain ⟨e⟩ := h
    apply Or.inr
    apply transport_facts e (alternatingGroup.center_eq_bot (by simp))
      (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide))
    rw [AlternatingSix.ShadowLocal.outer_card]
    decide
  · obtain ⟨e⟩ := h
    exact Or.inr (transport_facts e (alternatingGroup.center_eq_bot (by simp))
      (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide))
      (coprime_three_of_two alternatingGroup.SevenComponent.outer_two))
  · obtain ⟨e⟩ := h
    exact Or.inr (transport_facts e Theory.SpecificGroups.g2_derived_two_center_eq_bot
      g2_rank_two houter)

/-- Full-group conjugation coverage discharges the sole outer-order premise
in the exact-list reduction. -/
theorem small_quotient_alternative {A : Type*} [Group A] [Finite A]
    (hcover : Function.Surjective binaryConjugation) (h : SmallQuotient A) :
    Nonempty (A ≃* Matrix.PSL3Two.PSL) ∨
      center A = ⊥ ∧ 2 ≤ primeRank 3 A ∧
        Nat.Coprime 3 (Nat.card (MulAut.Outer A)) :=
  small_quotient_alternative_of_outer_coprime (g2_outer_coprime_of_coverage hcover) h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.RankReduction
