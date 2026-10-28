module
public import Theory.SpecificGroups.Triality.OddDegreeFieldActors
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.Carrier

/-!
# Marked prime-degree triality subfields

For an actual coefficient automorphism of order p with n = p*m and p prime
to three, embed the genuine triality carrier at degree m into its fixed group.
The scalar fixed field has degree 3*m. Entrywise Geck maps intertwine the
original graph-field twist; the pinned arm swap corrects its orientation
when p is two modulo three. The existing elementary central quotient
comparison then transports fixedness to the original carrier.

This is the fixed-subfield step in Aschbacher–Smith A.3.18, pp.51–53,
with the diagram and coefficient conventions of GLS3 §§2.2 and 2.5.
ExceptionalCyclotomic uses it to exclude the remaining triality actors.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.OuterOdd Triality.Standard.EvenField
open Triality.Standard.ConcreteBruhat.FixedDescent
open Theory.AlgebraicGroup.StandardRootSystem
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
namespace TrialityCyclotomic
local instance matrixIndexDecidableEq :
    DecidableEq ((typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2+2)) := instDecidableEqSum

private theorem exists_fixed_embedding_aux {K F₀ : Type*}
    [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    [Field F₀] [Algebra (ZMod 2) F₀]
    (n m p : ℕ) (hp : 0 < p) (hnm : n = p*m)
    (hK : Module.finrank (ZMod 2) K = 3*n)
    (hF₀ : Module.finrank (ZMod 2) F₀ = 3*m)
    (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ j : F₀ →+* K, ∀ t, σ (j t) = j t := by
  let H := zpowers σ
  let F := FixedPoints.subfield H K
  let : Finite H := Finite.of_injective
    (fun a : H => (a.val : K → K)) (fun a b h => Subtype.ext (DFunLike.coe_injective h))
  let : Fintype H := Fintype.ofFinite H
  have hd : Module.finrank F K = p := by
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, Nat.card_zpowers, hσ]
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Module (ZMod 2) F := Algebra.toModule
  have ht := Module.finrank_mul_finrank (ZMod 2) F K
  rw [hd, hK, hnm] at ht
  have hF : Module.finrank (ZMod 2) F = 3*m := by nlinarith
  have hdiv : Module.finrank (ZMod 2) F₀ ∣ Module.finrank (ZMod 2) F := by
    rw [hF₀, hF]
  obtain ⟨j⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdiv
  exact ⟨F.subtype.comp j.toRingHom, fun t => (j t).property ⟨σ, mem_zpowers σ⟩⟩

private theorem exists_fixed_embedding (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    {p : ℕ} (hnm : n = p*m)
    (σ : CoefficientAut (binaryParameters n hn)) (hσ : orderOf σ = p) :
    ∃ j : ExtensionField (binaryParameters m hm) →+* ExtensionField (binaryParameters n hn),
      ∀ t, σ (j t) = j t :=
  exists_fixed_embedding_aux (K := GaloisField 2 (3*n)) (F₀ := GaloisField 2 (3*m))
    n m p (by nlinarith) hnm (GaloisField.finrank 2 (by omega))
    (GaloisField.finrank 2 (by omega)) σ hσ

private theorem frobenius_mod (m : ℕ) (hm : 0 < m) (p : ℕ) :
    coefficientFrobenius m hm (p*m) = coefficientFrobenius m hm ((p%3)*m) := by
  change iterateFrobeniusEquiv _ 2 (p*m) = iterateFrobeniusEquiv _ 2 ((p%3)*m)
  simp only [iterateFrobeniusEquiv_eq_pow]
  have horder := orderOf_primeFrobenius m hm
  have he := (pow_mod_orderOf (frobeniusEquiv (GaloisField 2 (3*m)) 2) (p*m)).symm
  rw [horder, Nat.mul_mod_mul_right] at he
  exact he

private theorem reverse_fixed (m : ℕ) (hm : 0 < m)
    (x : fixedSubgroup (binaryParameters m hm)) :
    diagramAutomorphism (binaryParameters m hm)
      (splitFrobenius m hm (2*m) (reverseDiagram (binaryParameters m hm) x)) =
      reverseDiagram (binaryParameters m hm) x := by
  let P := binaryParameters m hm
  have hh : inverseGraphHalf m hm (2*m) x = x := by
    change diagramAutomorphism P (diagramAutomorphism P (splitFrobenius m hm (2*m) x)) = x
    have hF : splitFrobenius m hm (2*m) = fieldAutomorphism P * fieldAutomorphism P := by
      apply MulEquiv.ext
      intro g
      apply Subtype.ext
      apply Units.ext
      ext i j
      change g.val.val i j ^ (2^(2*m)) = (g.val.val i j ^ (2^m)) ^ (2^m)
      simp only [two_mul, pow_add, pow_mul]
    rw [hF]
    change diagramAutomorphism P (diagramAutomorphism P
      (fieldAutomorphism P (fieldAutomorphism P x))) = x
    have hx : diagramAutomorphism P (fieldAutomorphism P x) = x :=
      (diagram_field_commute P x).trans x.property
    calc
      _ = diagramAutomorphism P (fieldAutomorphism P
          (diagramAutomorphism P (fieldAutomorphism P x))) :=
        congrArg (diagramAutomorphism P) (diagram_field_commute P (fieldAutomorphism P x))
      _ = diagramAutomorphism P (fieldAutomorphism P x) :=
        congrArg (fun z => diagramAutomorphism P (fieldAutomorphism P z)) hx
      _ = x := hx
  exact (reverseDiagram_half m hm (2*m) x.val).symm.trans (congrArg (reverseDiagram P) hh)

private theorem frobenius_base (m : ℕ) (hm : 0 < m) :
    splitFrobenius m hm m = fieldAutomorphism (binaryParameters m hm) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

private def splitMap {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    (j : ExtensionField (binaryParameters m hm) →+* ExtensionField (binaryParameters n hn)) :
    SplitGroup (binaryParameters m hm) →* SplitGroup (binaryParameters n hn) :=
  RootPairing.SimpleGeckGroup.map j

private theorem splitMap_injective {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    (j : ExtensionField (binaryParameters m hm) →+* ExtensionField (binaryParameters n hn)) :
    Function.Injective (splitMap j) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  ext i t
  exact j.injective (congrArg (fun z : SplitGroup (binaryParameters n hn) => z.val.val i t) h)

private theorem splitMap_graphField {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    {p : ℕ} (hnm : n = p*m)
    (j : ExtensionField (binaryParameters m hm) →+* ExtensionField (binaryParameters n hn))
    (x : SplitGroup (binaryParameters m hm)) :
    graphFieldAutomorphism (binaryParameters n hn) (splitMap j x) =
      splitMap j (diagramAutomorphism (binaryParameters m hm)
        (splitFrobenius m hm ((p%3)*m) x)) := by
  let P := binaryParameters m hm
  let Q := binaryParameters n hn
  have hF : fieldAutomorphism Q (splitMap j x) = splitMap j (splitFrobenius m hm n x) := by
    apply Subtype.ext
    apply Units.ext
    ext i t
    exact (map_pow j (x.val.val i t) (2^n)).symm
  have hd : diagramAutomorphism Q (splitMap j (splitFrobenius m hm n x)) =
      splitMap j (diagramAutomorphism P (splitFrobenius m hm n x)) :=
    RootPairing.SimpleGeckGroup.diagramEquiv_map _ _ _ j _
  have he := ((diagram_field_commute Q (splitMap j x)).symm.trans
    (congrArg (diagramAutomorphism Q) hF)).trans hd
  have hm' : splitFrobenius m hm n = splitFrobenius m hm ((p%3)*m) := by
    rw [hnm]
    exact congrArg (splitCoefficientAction P) (frobenius_mod m hm p)
  exact he.trans (congrArg
    (fun a : MulAut (SplitGroup P) => splitMap j (diagramAutomorphism P (a x))) hm')

private theorem exists_fixed_splitMap {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    {p : ℕ} (hp3 : ¬ 3 ∣ p) (hnm : n = p*m)
    (j : ExtensionField (binaryParameters m hm) →+* ExtensionField (binaryParameters n hn))
    (σ : CoefficientAut (binaryParameters n hn)) (hj : ∀ t, σ (j t) = j t) :
    ∃ k : SplitGroup (binaryParameters m hm) →* SplitGroup (binaryParameters n hn),
      Function.Injective k ∧
      (∀ x : fixedSubgroup (binaryParameters m hm), k x ∈ fixedSubgroup (binaryParameters n hn)) ∧
      ∀ x, coefficientSplit (binaryParameters n hn) σ (k x) = k x := by
  let P := binaryParameters m hm
  let Q := binaryParameters n hn
  have hs (x : SplitGroup P) : coefficientSplit Q σ (splitMap j x) = splitMap j x := by
    apply Subtype.ext
    apply Units.ext
    ext i t
    exact hj (x.val.val i t)
  have hmod : p%3=1 ∨ p%3=2 := by omega
  rcases hmod with h1 | h2
  · refine ⟨splitMap j, splitMap_injective j, ?_, hs⟩
    intro x
    change graphFieldAutomorphism Q (splitMap j x) = splitMap j x
    have hnum : (p%3)*m = m := by rw [h1, one_mul]
    have he := (congrArg (fun t => splitFrobenius m hm t x.val) hnum).trans
      (DFunLike.congr_fun (frobenius_base m hm) x.val)
    exact (splitMap_graphField hnm j x.val).trans
      (congrArg (splitMap j) ((congrArg (diagramAutomorphism P) he).trans
        ((diagram_field_commute P x.val).trans x.property)))
  · refine ⟨(splitMap j).comp (reverseDiagram P).toMonoidHom,
      (splitMap_injective j).comp (reverseDiagram P).injective, ?_, fun x => hs _⟩
    intro x
    change graphFieldAutomorphism Q (splitMap j (reverseDiagram P x)) = splitMap j (reverseDiagram P x)
    have he := congrArg (fun t => splitFrobenius m hm (t*m) (reverseDiagram P x.val)) h2
    exact (splitMap_graphField hnm j (reverseDiagram P x.val)).trans
      (congrArg (splitMap j) ((congrArg (diagramAutomorphism P) he).trans
        (reverse_fixed m hm x)))

private theorem exists_fixed_injection (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    {p : ℕ} (hp3 : ¬ 3 ∣ p) (hnm : n = p*m)
    (σ : CoefficientAut (binaryParameters n hn)) (hσ : orderOf σ = p) :
    ∃ k : fixedSubgroup (binaryParameters m hm) →* fixedSubgroup (binaryParameters n hn),
      Function.Injective k ∧ ∀ x, coefficientSplit (binaryParameters n hn) σ (k x).val = (k x).val := by
  let j := Classical.choose (exists_fixed_embedding (p := p) n hn m hm hnm σ hσ)
  have hj := Classical.choose_spec (exists_fixed_embedding (p := p) n hn m hm hnm σ hσ)
  let k := Classical.choose (exists_fixed_splitMap hp3 hnm j σ hj)
  have hk := Classical.choose_spec (exists_fixed_splitMap hp3 hnm j σ hj)
  let l := (k.comp (fixedSubgroup (binaryParameters m hm)).subtype).codRestrict
    (fixedSubgroup (binaryParameters n hn)) hk.2.1
  exact ⟨l, fun x y h => Subtype.ext (hk.1 (congrArg Subtype.val h)), fun x => hk.2.2 x⟩

private theorem fixed_embedding_transport {G₀ G₁ F₀ F₁ : Type*}
    [Group G₀] [Group G₁] [Group F₀] [Group F₁]
    (e₀ : G₀ ≃* F₀) (e₁ : G₁ ≃* F₁) (a : MulAut G₁) (b : MulAut F₁)
    (hab : ∀ x, e₁ (a x) = b (e₁ x))
    (j : F₀ →* F₁) (hj : Function.Injective j) (hfix : ∀ x, b (j x) = j x) :
    ∃ k : G₀ →* G₁, Function.Injective k ∧ ∀ x, a (k x) = k x := by
  let k := e₁.symm.toMonoidHom.comp (j.comp e₀.toMonoidHom)
  refine ⟨k, e₁.symm.injective.comp (hj.comp e₀.injective), ?_⟩
  intro x
  apply e₁.injective
  rw [hab]
  change b (e₁ (e₁.symm (j (e₀ x)))) = e₁ (e₁.symm (j (e₀ x)))
  rw [e₁.apply_symm_apply, hfix]

/-- A marked prime-order coefficient actor fixes an embedded genuine triality
carrier over the field of degree n/p, with the diagram orientation retained. -/
theorem exists_fixed_carrier_embedding (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    {p : ℕ} (hp3 : ¬ 3 ∣ p) (hnm : n = p*m)
    (σ : CoefficientAut (binaryParameters n hn)) (hσ : orderOf σ = p) :
    ∃ k : BinaryCarrier m hm →* BinaryCarrier n hn,
      Function.Injective k ∧ ∀ x, coefficientAction (binaryParameters n hn) σ (k x) = k x := by
  let j := Classical.choose (exists_fixed_injection (p := p) n hn m hm hp3 hnm σ hσ)
  have hj := (Classical.choose_spec (exists_fixed_injection (p := p) n hn m hm hp3 hnm σ hσ)).1
  have hfix := (Classical.choose_spec (exists_fixed_injection (p := p) n hn m hm hp3 hnm σ hσ)).2
  exact fixed_embedding_transport (carrierFixedEquiv (binaryParameters m hm) rfl)
    (carrierFixedEquiv (binaryParameters n hn) rfl)
    (coefficientAction (binaryParameters n hn) σ) (coefficientFixed (binaryParameters n hn) σ)
    (carrierFixedEquiv_coefficient (binaryParameters n hn) rfl σ) j hj
    (fun x => Subtype.ext (hfix x))

end TrialityCyclotomic
end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
