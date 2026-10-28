module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.ResidualGeometry
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.ProjectiveSylow
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.SylowCenter.PrimeAction

/-!
# The whole Sylow center centralizes the linear involution residual

Let D be normal in a finite group J and isomorphic to PSL₃(q), with q > 3
prime and q congruent to one modulo four. For an involution z in D ∩ Z(S),
the ambient image R of C_D(z)'s solvable residual is SL₂(q).

Every element centralizing z normalizes R. Thus S normalizes R, its
intersection with R is Sylow in R, and every element of Z(S) fixes that
intersection pointwise. Prime-field SL₂ automorphism rigidity then makes
Z(S) centralize all of R. The argument retains the actual projective and
field comparisons supplied by `InvolutionModel`.

The final specialization uses the original `AmbientInput` and linear
`CaseThree` hypotheses. No positioning of the cyclic Cartan factors is
needed. This supplies the whole-center premise in the parent assembly.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51, and the proof of
1.3.4, printed pp.510–511 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J]

/-- Centralizing z normalizes the residual of its centralizer in a normal subgroup. -/
theorem centralizer_le_normalizer_involutionResidual (D : Subgroup J) [D.Normal] (z : J) :
    centralizer ({z} : Set J) ≤ normalizer (involutionResidual D z : Set J) := by
  let C := D ⊓ centralizer ({z} : Set J)
  have hC : centralizer ({z} : Set J) ≤ normalizer (C : Set J) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro g hg x hx
    exact ⟨(inferInstance : D.Normal).conj_mem x hx.1 g,
      (centralizer ({z} : Set J)).mul_mem
        ((centralizer ({z} : Set J)).mul_mem hg hx.2)
        ((centralizer ({z} : Set J)).inv_mem hg)⟩
  apply hC.trans
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let a := C.normalizerMonoidHom ⟨g, hg⟩
  have hay : a y ∈ solvableResidual C :=
    map_solvableResidual_le a.toMonoidHom (mem_map_of_mem a.toMonoidHom hy)
  exact ⟨a y, hay, rfl⟩

variable [Finite J]

private theorem sylow_intersection_of_normalizes (R : Subgroup J) (S : Sylow 2 J)
    (hSR : (S : Subgroup J) ≤ normalizer (R : Set J)) :
    ∃ P : Sylow 2 R, ∀ x ∈ (P : Subgroup R), (x : J) ∈ (S : Subgroup J) := by
  let N := normalizer (R : Set J)
  let R' := R.subgroupOf N
  let SN : Sylow 2 N := S.subtype hSR
  have : R'.Normal := Subgroup.normal_in_normalizer
  obtain ⟨P, hP⟩ := SN.exists_subgroupOf_eq_of_normal R'
  let e : R' ≃* R := subgroupOfEquivOfLe R.le_normalizer
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  rw [hP] at hy
  exact hy

/-- A normalizing Sylow center centralizes R if its intrinsic Sylow fixer is trivial. -/
private theorem centerImage_le_centralizer_of_sylow_rigidity (R : Subgroup J) (S : Sylow 2 J)
    (hSR : (S : Subgroup J) ≤ normalizer (R : Set J))
    (hrigid : ∀ (P : Sylow 2 R) (a : MulAut R),
      (∀ x ∈ (P : Subgroup R), a x = x) → a = 1) :
    centerImage (S : Subgroup J) ≤ centralizer (R : Set J) := by
  obtain ⟨P, hP⟩ := sylow_intersection_of_normalizes R S hSR
  rintro z ⟨zS, hzS, rfl⟩
  let a := R.normalizerMonoidHom ⟨zS, hSR zS.property⟩
  have ha : a = 1 := hrigid P a (by
    intro x hx
    apply Subtype.ext
    change (zS : J) * x * (zS : J)⁻¹ = x
    have hc := congrArg Subtype.val (mem_center_iff.mp hzS ⟨x, hP x hx⟩)
    change (x : J) * zS = zS * x at hc
    rw [← hc, mul_inv_cancel_right])
  apply mem_centralizer_iff.mpr
  intro x hx
  have he := congrArg Subtype.val (DFunLike.congr_fun ha (⟨x, hx⟩ : R))
  change (zS : J) * x * (zS : J)⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The whole ambient Sylow center centralizes the involution residual in the linear model. -/
theorem involutionResidual_le_centralizer_centerImage_of_linear
    (D : Subgroup J) [D.Normal] (S : Sylow 2 J) {q : ℕ} [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q) (hmod : q % 4 = 1)
    (hD : ClassicalGroup.IsPSL D 3 q) {z : J}
    (hzD : z ∈ D) (hzS : z ∈ centerImage (S : Subgroup J)) (hz : orderOf z = 2) :
    involutionResidual D z ≤ centralizer (centerImage (S : Subgroup J) : Set J) := by
  obtain ⟨e⟩ := involutionResidual_equiv hq hlarge hD hzD hz
  have hSC : (S : Subgroup J) ≤ centralizer ({z} : Set J) := by
    obtain ⟨zS, hzS, rfl⟩ := hzS
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp hzS (⟨x, hx⟩ : S))
  apply le_centralizer_iff.mpr
  apply centerImage_le_centralizer_of_sylow_rigidity _ S
    (hSC.trans (centralizer_le_normalizer_involutionResidual D z))
  intro P a ha
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hfix : ∀ x ∈ (Q : Subgroup SL(2, ZMod q)), MulAut.congr e a x = x := by
    rintro x ⟨y, hy, rfl⟩
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply, ha y hy]
  have he := sl2_prime_sylow_aut_eq_one hq hlarge hmod Q (MulAut.congr e a) hfix
  exact (MulAut.congr e).injective (he.trans (map_one (MulAut.congr e)).symm)

/-- The whole-center centralization clause from the original linear Cartan inputs. -/
theorem CaseThree.linear_involutionResidual_le_centralizer_centerImage
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ} [Fact q.Prime]
    (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .linear .linear)
    (_hB : ¬ IsCyclic B) (hlarge : 3 < q)
    {z : J} (hz : z ∈ D ⊓ centerImage (S : Subgroup J)) (hz2 : orderOf z = 2) :
    involutionResidual D z ≤ centralizer (centerImage (S : Subgroup J) : Set J) := by
  let : D.Normal := hA.normal
  exact involutionResidual_le_centralizer_centerImage_of_linear D S
    hC.odd_characteristic hlarge hC.sylow_sign hC.model hz.1 hz.2 hz2

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
