module

public import Stellmacher.SectionTwo.QuotientAction
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Ambient transport of quotient action modules

Let q be the Section 2 quotient by the centralizer of V. Under the exact
named quotient-conjugation action, the action commutator for a subgroup E
of the quotient maps into G as [q⁻¹(E), V]. Likewise, its fixed subgroup
maps onto V ∩ C_G(q⁻¹(E)). The full preimages here are exactly those in the
common factor/module decomposition of Stellmacher (2.2).

Surjectivity lifts the quotient actors, and the quotient action computation
lemma identifies their actions with conjugation. Comparing the action
commutator generators reduces the first theorem to the existing subgroup
conjugation commutator identity. The second compares fixed points directly
with centralizer membership. Neither requires finiteness or classification.

Source: Stellmacher (2.2), Journal of Algebra 190 (1997), p.20, in
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionTwo
universe u v
variable {G : Type u} [Group G] (S : Sylow 2 G)
  {barG : Type v} [Group barG] (q : G →* barG)
  (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)

public theorem quotientConjugationAction_commutator_map (E : Subgroup barG) :
    letI := quotientConjugationAction S q hq hker
    (commutatorAction E (vSubgroup S)).map (vSubgroup S).subtype =
      ambientCommutator (E.comap q) (vSubgroup S) := by
  let := quotientConjugationAction S q hq hker
  let : (vSubgroup S).Normal := Subgroup.normalClosure_normal
  have hnorm : E.comap q ≤ Subgroup.normalizer (vSubgroup S) :=
    Subgroup.le_normalizer_of_normal
  let : Subgroup.Normalizes (E.comap q) (vSubgroup S) := ⟨hnorm⟩
  have hcomm : commutatorAction E (vSubgroup S) =
      commutatorAction (E.comap q) (vSubgroup S) := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨e, x, rfl⟩
      obtain ⟨g, hg⟩ := hq (e : barG)
      refine ⟨⟨g, show q g ∈ E by rw [hg]; exact e.property⟩, x, ?_⟩
      congr 1
      apply Subtype.ext
      change ((e.val • x : vSubgroup S) : G) = g * (x : G) * g⁻¹
      rw [← hg, quotientConjugationAction_smul_coe S q hq hker]
    · rintro ⟨g, x, rfl⟩
      refine ⟨⟨q g, g.property⟩, x, ?_⟩
      congr 1
      apply Subtype.ext
      change (g : G) * (x : G) * (g : G)⁻¹ = ((q g • x : vSubgroup S) : G)
      rw [quotientConjugationAction_smul_coe S q hq hker]
  rw [hcomm, commutatorAction_subgroup_conj_map_eq_commutator
    (vSubgroup S) (E.comap q) hnorm, Subgroup.commutator_comm]
  rfl

public theorem quotientConjugationAction_fixedPoints_map (E : Subgroup barG) :
    letI := quotientConjugationAction S q hq hker
    (FixedPoints.subgroup E (vSubgroup S)).map (vSubgroup S).subtype =
      vSubgroup S ⊓ Subgroup.centralizer (E.comap q : Set G) := by
  let := quotientConjugationAction S q hq hker
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    change (y : G) ∈ Subgroup.centralizer (E.comap q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hfix := (FixedPoints.mem_subgroup (M := E) (a := y)).mp hy ⟨q a, ha⟩
    change q a • y = y at hfix
    have heq := congrArg Subtype.val hfix
    rw [quotientConjugationAction_smul_coe S q hq hker] at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  · rintro ⟨hxV, hxE⟩
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    change (⟨x, hxV⟩ : vSubgroup S) ∈ FixedPoints.subgroup E (vSubgroup S)
    rw [FixedPoints.mem_subgroup]
    intro e
    obtain ⟨g, hg⟩ := hq (e : barG)
    apply Subtype.ext
    change ((e.val • (⟨x, hxV⟩ : vSubgroup S) : vSubgroup S) : G) = x
    rw [← hg, quotientConjugationAction_smul_coe S q hq hker]
    change x ∈ Subgroup.centralizer (E.comap q : Set G) at hxE
    rw [Subgroup.mem_centralizer_iff] at hxE
    rw [hxE g (show q g ∈ E by rw [hg]; exact e.property), mul_inv_cancel_right]

end Stellmacher.SectionTwo
