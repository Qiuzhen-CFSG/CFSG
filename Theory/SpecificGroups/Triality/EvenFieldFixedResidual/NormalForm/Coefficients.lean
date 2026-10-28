module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.Basic
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.ParameterRigidity.Torus
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Separation of coefficient and inner triality automorphisms

A coefficient automorphism preserves the actual positive subgroup and fixes
all pinned Weyl words. If its action on the genuine central quotient is inner,
the conjugating element therefore belongs to both opposite Borels, hence to
the actual torus. Torus conjugation scales each folded simple-root parameter.
Since a field automorphism fixes one, the arm-root scalar is one; injectivity
of that root curve then detects every element of the cubic coefficient field.

This proves separation without simplicity, perfectness, or global automorphism
coverage. It is the scalar step needed to normalize the outer involutions in
Aschbacher–Smith, Notation 16.1.3 and Lemma 16.1.4(4), printed p.1171.
Sources: GLS3 §§2.3–2.5, especially 2.5.12 and 2.5.13,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace Triality.Standard.EvenField.NormalForm
open OuterOdd OuterOdd.Coverage OuterOdd.Coverage.RootGeometry
open Parabolics ConcreteBruhat

private theorem coefficient_positive_mem (P : Parameters) (e : CoefficientAut P)
    {x : SplitGroup P} (hx : x ∈ positiveSubgroup P) :
    coefficientSplit P e x ∈ positiveSubgroup P := by
  have h : positiveSubgroup P ≤ (positiveSubgroup P).comap
      (coefficientSplit P e).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, t, rfl⟩
    change coefficientSplit P e (positiveRoot P i t) ∈ positiveSubgroup P
    rw [positiveRoot, coefficientSplit_positive]
    exact positiveRoot_mem_positiveSubgroup P i (e t)
  exact h hx

private theorem coefficient_unipotent_mem (P : Parameters) (e : CoefficientAut P)
    {x : Carrier P} (hx : x ∈ unipotent P) :
    coefficientAction P e x ∈ unipotent P := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨coefficientElementary P e y, ?_, rfl⟩
  exact coefficient_positive_mem P e hy

/-- Coefficient automorphisms preserve the original descended positive subgroup. -/
theorem coefficientAction_unipotent (P : Parameters) (e : CoefficientAut P) :
    (unipotent P).map (coefficientAction P e).toMonoidHom = unipotent P := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact coefficient_unipotent_mem P e hx
  · intro x hx
    refine ⟨coefficientAction P e⁻¹ x, coefficient_unipotent_mem P e⁻¹ hx, ?_⟩
    change (coefficientAction P e * coefficientAction P e⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

private theorem coefficient_simple (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (i : Node) :
    coefficientAction P e (simpleRepresentative P hp i) = simpleRepresentative P hp i := by
  simp only [simpleRepresentative_eq_root_word, map_mul, coefficientAction_rootElement, map_one]

private theorem coefficient_weyl (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (w : DihedralGroup 6) :
    coefficientAction P e (weylRepresentative P hp w) = weylRepresentative P hp w := by
  have hs (i : Node) : coefficientAction P e (toCarrier P (simpleElementary P hp i)) =
      toCarrier P (simpleElementary P hp i) := coefficient_simple P hp e i
  cases w <;> simp only [weylRepresentative, weylElementary, map_mul, map_pow, hs]

private theorem coefficient_map_opposite (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) :
    (oppositeUnipotent P hp).map (coefficientAction P e).toMonoidHom =
      oppositeUnipotent P hp := by
  have hc : (coefficientAction P e).toMonoidHom.comp
      (MulAut.conj (weylRepresentative P hp (.r 3))).toMonoidHom =
      (MulAut.conj (weylRepresentative P hp (.r 3))).toMonoidHom.comp
      (coefficientAction P e).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, coefficient_weyl]
  rw [oppositeUnipotent, Subgroup.map_map, hc, ← Subgroup.map_map, coefficientAction_unipotent]

/-- No nonidentity cubic coefficient automorphism acts by inner conjugation. -/
theorem coefficient_eq_one_of_inner (n : ℕ) (hn : 0 < n)
    (e : CoefficientAut (binaryParameters n hn)) (g : BinaryCarrier n hn)
    (h : coefficientAction (binaryParameters n hn) e = MulAut.conj g) : e = 1 := by
  let P := binaryParameters n hn
  have hgB : g ∈ borel P := by
    rw [← normalizer_unipotent_eq_borel P rfl]
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [← h]
    exact coefficientAction_unipotent P e
  have hgO : g ∈ oppositeBorel P rfl := by
    rw [← normalizer_oppositeUnipotent P rfl]
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [← h]
    exact coefficient_map_opposite P rfl e
  have hgT : g ∈ torus P := by
    apply TwoLocalGeometry.ApartmentStabilizer.borel_opposition_intersection n hn hgB
    change (weylRepresentative P rfl (.r 3))⁻¹ * g *
      weylRepresentative P rfl (.r 3) ∈ borel P
    obtain ⟨x, hx, he⟩ := hgO
    change weylRepresentative P rfl (.r 3) * x *
      (weylRepresentative P rfl (.r 3))⁻¹ = g at he
    rw [← he]
    have hcancel : (weylRepresentative P rfl (.r 3))⁻¹ *
        (weylRepresentative P rfl (.r 3) * x * (weylRepresentative P rfl (.r 3))⁻¹) *
        weylRepresentative P rfl (.r 3) = x := by group
    rw [hcancel]
    exact hx
  obtain ⟨v, hv⟩ := (TorusCoordinates.torusMulEquiv P rfl).surjective ⟨g, hgT⟩
  have hvg : (TorusCoordinates.torusMulEquiv P rfl v).val = g := congrArg Subtype.val hv
  have he (t : ExtensionField P) :
      e t = (ParameterRigidity.nodeCharacter P v .arms).val * t := by
    apply rootElement_injective P rfl true .arms
    calc
      rootElement P rfl true .arms (e t) =
          coefficientAction P e (rootElement P rfl true .arms t) :=
        (coefficientAction_rootElement P rfl e true .arms t).symm
      _ = g * rootElement P rfl true .arms t * g⁻¹ :=
        DFunLike.congr_fun h _
      _ = rootElement P rfl true .arms
          ((ParameterRigidity.nodeCharacter P v .arms).val * t) := by
        rw [← hvg]
        exact ParameterRigidity.torus_root_conjugate P rfl v true .arms t
  have hc : (ParameterRigidity.nodeCharacter P v .arms).val = 1 := by
    simpa only [map_one, mul_one] using (he 1).symm
  ext t
  change e t = t
  simpa only [hc, one_mul] using he t

/-- The actual coefficient action meets the inner automorphism subgroup trivially. -/
theorem coefficientAction_mem_inner_iff (n : ℕ) (hn : 0 < n)
    (e : CoefficientAut (binaryParameters n hn)) :
    coefficientAction (binaryParameters n hn) e ∈
      MulAut.innerSubgroup (BinaryCarrier n hn) ↔ e = 1 := by
  constructor
  · rintro ⟨g, hg⟩
    exact coefficient_eq_one_of_inner n hn e g hg.symm
  · rintro rfl
    rw [map_one]
    exact (MulAut.innerSubgroup (BinaryCarrier n hn)).one_mem

end Triality.Standard.EvenField.NormalForm
