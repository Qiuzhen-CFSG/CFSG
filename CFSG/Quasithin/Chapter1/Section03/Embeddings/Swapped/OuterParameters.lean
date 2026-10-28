module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Sylow
public import Theory.SpecificGroups.PSL2.OuterSolvable.Actions
public import Theory.GroupTheory.SolvableOuterQuotient
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Outer-group parameter restrictions for the swapped case

The proved inner–field description of binary PSL₂ makes the defining-field
automorphism group surject onto the actual outer automorphism group. Prime-field
Galois theory bounds its order by the defining degree. Consequently, even outer
order forces even degree. The corresponding concrete Suzuki coverage gives odd
outer order, and hence excludes Suzuki once the separate swapped-action argument
has established even outer order.

These calculations use the actual automorphism quotients and multiplicative
model equivalences. They do not infer the embedding alternatives from group orders.
Borel normalization and the action comparison are still needed by the consumer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.510. The imported
inner–field descriptions are GLS3, Theorem 2.5.12 and GLS4, Chapter 4, Lemma 3.1.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow

private theorem fieldAut_card_dvd_degree {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) : Nat.card (F ≃+* F) ∣ n := by
  let _ := ZMod.algebra F 2
  let j : (F ≃+* F) →* (F ≃ₐ[ZMod 2] F) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (fun z => by
        exact congrArg (fun f : ZMod 2 →+* F => f z)
          (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod 2) F))
            (algebraMap (ZMod 2) F)))
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }
  have hj : Function.Injective j := fun σ τ h => RingEquiv.ext fun x =>
    congrArg (fun f : F ≃ₐ[ZMod 2] F => f x) h
  have hd := Subgroup.card_dvd_of_injective j hj
  have hdim : Module.finrank (ZMod 2) F = n := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    simpa only [Nat.card_zmod, hF] using hc.symm
  simpa only [IsGalois.card_aut_eq_finrank, hdim] using hd

private theorem binary_outer_card_dvd {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (MulAut.Outer (Theory.PSL2.Group F)) ∣ n := by
  let I := MulAut.innerSubgroup (Theory.PSL2.Group F)
  let f := (QuotientGroup.mk' I).comp (Theory.PSL2.OuterSolvable.projectiveFieldAutHom (K := F))
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective I q
    obtain ⟨g, σ, ha⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage a
    have hσ : BenderSuzuki.ZD.Linear.fieldAut σ =
        Theory.PSL2.OuterSolvable.projectiveFieldAutHom σ := by
      rw [Theory.PSL2.OuterSolvable.projectiveFieldAutHom_eq_fieldAut]
      rfl
    rw [hσ] at ha
    refine ⟨σ, ?_⟩
    have hg : QuotientGroup.mk' I (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    change QuotientGroup.mk' I (Theory.PSL2.OuterSolvable.projectiveFieldAutHom σ) = _
    rw [ha, map_mul, hg, one_mul]
  exact (Subgroup.card_dvd_of_surjective f hf).trans (fieldAut_card_dvd_degree hF)

/-- The outer-group order of the actual binary PSL₂ model divides its defining degree. -/
theorem binary_model_outer_card_dvd {Q : Type*} [Group Q]
    {n : ℕ} (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) :
    Nat.card (MulAut.Outer Q) ∣ n := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
  exact binary_outer_card_dvd hF

/-- Even outer order forces the even-degree restriction in Proposition 1.3.4(1). -/
theorem binary_degree_even_of_outer_even {Q : Type*} [Group Q]
    {n : ℕ} (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (he : Even (Nat.card (MulAut.Outer Q))) : Even n := by
  exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp he).trans (binary_model_outer_card_dvd hmodel))

/-- The concrete Suzuki model, transported by an actual isomorphism, has odd outer order. -/
theorem suzuki_model_outer_odd {Q : Type*} [Group Q]
    {m : ℕ} (hm : 1 ≤ m) (e : Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    Odd (Nat.card (MulAut.Outer Q)) := by
  rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
  exact BenderSuzuki.MatrixGroups.suzuki_odd_outer_index m hm

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow
