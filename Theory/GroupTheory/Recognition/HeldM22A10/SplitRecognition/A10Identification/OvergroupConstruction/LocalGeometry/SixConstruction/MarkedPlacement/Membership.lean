module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.SectionPlacement
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
import Mathlib.Tactic.FinCases

/-!
# Locating the marks in the supplied normal A₆

Map the known local centralizer to the dihedral quotient of the supplied
section. Its defining relations force pi and mu to have equal images, and
leave two possible images for each of tau*lambda and mu-prime*xi.
Consequently pi*mu belongs to the section without any fusion hypothesis.
The single involution class of A₆ then identifies every section involution
with mu in the ambient group. The source fusions pi~pi*lambda and pi~pi*xi
exclude the unwanted choices for the other two marks.

The last two fusions are explicit premises here. Their existence and the
symmetric-extension and centralization conclusions of `MarkedSection` are
separate obligations; these lemmas do not assert the existence of that record.
All dihedral and coordinate calculations use kernel reduction.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, printed pp.232–235.
The quotient argument uses the supplied actual section and preserves its
marking; it does not reconstruct the normal A₆.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem dihedral_markings : ∀ l r t x : DihedralGroup 4,
    l ^ 2 = 1 → r ^ 2 = 1 → t ^ 2 = 1 → x ^ 2 = 1 →
    (l * r) ^ 2 ≠ 1 → t * l = l * t → r * x = x * r →
    x * l * x = (l * r) ^ 2 * l → x * t * x = (l * r) ^ 2 * t →
    (t * r) ^ 2 = (l * r) ^ 2 ∧
      (t * l = 1 ∨ t * l = (l * r) ^ 2) ∧
      (r * x = 1 ∨ r * x = (l * r) ^ 2) := by
  decide +kernel

private abbrev K := centralizer ({modelElement 1} : Set CentralizerModels.a10Centralizer)
private def mark (i : Fin 6) : K :=
  ⟨modelElement (![0, 1, 2, 3, 6, 7] i), by
    apply mem_centralizer_singleton_iff.mpr
    fin_cases i <;> decide +kernel⟩

private theorem quotient_markings (f : K →* DihedralGroup 4) (hm : f (mark 1) ≠ 1) :
    f (mark 0) = f (mark 1) ∧
      (f (mark 3 * mark 4) = 1 ∨ f (mark 3 * mark 4) = f (mark 1)) ∧
      (f (mark 2 * mark 5) = 1 ∨ f (mark 2 * mark 5) = f (mark 1)) := by
  have hs : ∀ i : Fin 6, mark i ^ 2 = 1 := by decide +kernel
  have hsq : (mark 4 * mark 2) ^ 2 = mark 1 := by decide +kernel
  have hp : (mark 3 * mark 2) ^ 2 = mark 0 := by decide +kernel
  have htl : mark 3 * mark 4 = mark 4 * mark 3 := by decide +kernel
  have hrx : mark 2 * mark 5 = mark 5 * mark 2 := by decide +kernel
  have hxl : mark 5 * mark 4 * mark 5 = mark 1 * mark 4 := by decide +kernel
  have hxt : mark 5 * mark 3 * mark 5 = mark 1 * mark 3 := by decide +kernel
  have h := dihedral_markings (f (mark 4)) (f (mark 2)) (f (mark 3)) (f (mark 5))
    (by rw [← map_pow, hs, map_one]) (by rw [← map_pow, hs, map_one])
    (by rw [← map_pow, hs, map_one]) (by rw [← map_pow, hs, map_one])
    (by rwa [← map_mul, ← map_pow, hsq])
    (by rw [← map_mul, ← map_mul, htl])
    (by rw [← map_mul, ← map_mul, hrx])
    (by simpa only [← map_mul, ← map_pow, hsq] using congrArg f hxl)
    (by simpa only [← map_mul, ← map_pow, hsq] using congrArg f hxt)
  simpa only [← map_mul, ← map_pow, hp, hsq] using h

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : NoncentralAnalysis.AlternatingSixSection
    (centralizer ({D.a10NoncentralInvolution e} : Set G)))

private noncomputable def intoCentralizer : K →* centralizer ({D.a10NoncentralInvolution e} : Set G) where
  toFun a := ⟨D.a10ModelEmbedding e a, mem_centralizer_singleton_iff.mpr (by
    rw [← mu_eq D e]
    simpa only [map_mul, element] using
      congrArg (D.a10ModelEmbedding e) (mem_centralizer_singleton_iff.mp a.property))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

private theorem ambient_mem_iff (a : centralizer ({D.a10NoncentralInvolution e} : Set G)) :
    (a : G) ∈ s.ambientSubgroup ↔ a ∈ s.subgroup := by
  constructor
  · rintro ⟨b, hb, he⟩
    exact (Subtype.ext he : b = a) ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- The dihedral quotient forces pi*mu and constrains the two other marks. -/
public theorem section_marking_alternatives :
    pi D e * mu D e ∈ s.ambientSubgroup ∧
      (tau D e * lam D e ∈ s.ambientSubgroup ∨
        pi D e * (tau D e * lam D e) ∈ s.ambientSubgroup) ∧
      (mu' D e * xi D e ∈ s.ambientSubgroup ∨
        pi D e * (mu' D e * xi D e) ∈ s.ambientSubgroup) := by
  let := s.normal
  let q := s.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' s.subgroup)
  let f := q.comp (intoCentralizer D e)
  have hmem (a : K) : D.a10ModelEmbedding e a ∈ s.ambientSubgroup ↔ f a = 1 := by
    change ((intoCentralizer D e a) : G) ∈ s.ambientSubgroup ↔ f a = 1
    rw [ambient_mem_iff D e s (intoCentralizer D e a)]
    change (intoCentralizer D e a) ∈ s.subgroup ↔
      s.quotientEquiv (QuotientGroup.mk' s.subgroup (intoCentralizer D e a)) = 1
    rw [← s.quotientEquiv.map_one, s.quotientEquiv.injective.eq_iff]
    exact (QuotientGroup.eq_one_iff _).symm
  have hm : f (mark 1) ≠ 1 := fun h => mu_not_mem_section D e s ((hmem (mark 1)).mpr h)
  obtain ⟨hp, ht, hx⟩ := quotient_markings f hm
  have htwist (a : K) (ha : f a = f (mark 1)) :
      D.a10ModelEmbedding e (mark 0 * a) ∈ s.ambientSubgroup := by
    apply (hmem (mark 0 * a)).mpr
    rw [map_mul, hp, ha, ← map_mul]
    have hh : mark 1 * mark 1 = 1 := by decide +kernel
    rw [hh, map_one]
  have h₀ : D.a10ModelEmbedding e (mark 0) = pi D e := rfl
  have h₁ : D.a10ModelEmbedding e (mark 1) = mu D e := rfl
  have h₂ : D.a10ModelEmbedding e (mark 2) = mu' D e := rfl
  have h₃ : D.a10ModelEmbedding e (mark 3) = tau D e := rfl
  have h₄ : D.a10ModelEmbedding e (mark 4) = lam D e := rfl
  have h₅ : D.a10ModelEmbedding e (mark 5) = xi D e := rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [coe_mul, map_mul, h₀, h₁, h₂, h₃, h₄, h₅] using htwist (mark 1) rfl
  · rcases ht with ht | ht
    · exact Or.inl (by simpa only [coe_mul, map_mul, h₀, h₁, h₂, h₃, h₄, h₅] using (hmem (mark 3 * mark 4)).mpr ht)
    · exact Or.inr (by simpa only [coe_mul, map_mul, h₀, h₁, h₂, h₃, h₄, h₅] using htwist (mark 3 * mark 4) ht)
  · rcases hx with hx | hx
    · exact Or.inl (by simpa only [coe_mul, map_mul, h₀, h₁, h₂, h₃, h₄, h₅] using (hmem (mark 2 * mark 5)).mpr hx)
    · exact Or.inr (by simpa only [coe_mul, map_mul, h₀, h₁, h₂, h₃, h₄, h₅] using htwist (mark 2 * mark 5) hx)

/-- The product pi*mu belongs to every supplied normal A₆ section. -/
public theorem pi_mu_mem_section : pi D e * mu D e ∈ s.ambientSubgroup :=
  (section_marking_alternatives D e s).1

/-- Every involution of the section has the ambient conjugacy class of mu. -/
public theorem section_involution_isConj_mu (x : G) (hx : x ∈ s.ambientSubgroup)
    (hx2 : orderOf x = 2) : IsConj x (mu D e) := by
  let a : s.ambientSubgroup := ⟨x, hx⟩
  let b : s.ambientSubgroup := ⟨pi D e * mu D e, pi_mu_mem_section D e s⟩
  have hab : IsConj a b := by
    let j := s.ambientAlternatingEquiv
    have hb : orderOf (pi D e * mu D e) = 2 := by
      change orderOf (D.a10ModelEmbedding e (modelElement 0) *
        D.a10ModelEmbedding e (modelElement 1)) = 2
      rw [← map_mul, orderOf_injective _ (D.a10ModelEmbedding_injective e)]
      exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    have h := AlternatingSix.ShadowLocal.involutions_isConj (j a) (j b)
      (by simpa only [j.orderOf_eq, a, Subgroup.orderOf_mk] using hx2)
      (by simpa only [j.orderOf_eq, b, Subgroup.orderOf_mk] using hb)
    simpa only [MulEquiv.coe_toMonoidHom, j.symm_apply_apply] using
      j.symm.toMonoidHom.map_isConj h
  have hbmu : IsConj (pi D e * mu D e) (mu D e) := by
    have h : IsConj (modelElement 0 * modelElement 1) (modelElement 1) :=
      isConj_iff.mpr ⟨modelElement 4, by decide +kernel⟩
    simpa only [map_mul, element] using (D.a10ModelEmbedding e).map_isConj h
  exact (s.ambientSubgroup.subtype.map_isConj hab).trans hbmu

variable [Finite G]

/-- The original nonfusion excludes every pi-class involution from the section. -/
public theorem section_involution_not_isConj_pi
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (x : G) (hx : x ∈ s.ambientSubgroup) (hx2 : orderOf x = 2) :
    ¬ IsConj (pi D e) x := by
  intro hp
  have h := hp.trans (section_involution_isConj_mu D e s x hx hx2)
  exact hfusion (by simpa only [pi_eq, mu_eq] using h)

/-- Lambda's normalized source fusion determines the second marked membership. -/
public theorem tau_lam_mem_section_of_pi_lam_fusion
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : IsConj (pi D e) (pi D e * lam D e)) :
    tau D e * lam D e ∈ s.ambientSubgroup := by
  rcases (section_marking_alternatives D e s).2.1 with h | h
  · exact h
  · exfalso
    apply section_involution_not_isConj_pi D e s hfusion _ h
    · change orderOf (D.a10ModelEmbedding e (modelElement 0) *
        (D.a10ModelEmbedding e (modelElement 3) * D.a10ModelEmbedding e (modelElement 6))) = 2
      rw [← map_mul, ← map_mul, orderOf_injective _ (D.a10ModelEmbedding_injective e)]
      exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    · apply hlam.trans
      have hlocal : IsConj (modelElement 0 * modelElement 6)
          (modelElement 0 * (modelElement 3 * modelElement 6)) :=
        isConj_iff.mpr ⟨modelElement 4, by decide +kernel⟩
      simpa only [map_mul, element] using (D.a10ModelEmbedding e).map_isConj hlocal

/-- Xi's normalized source fusion determines the third marked membership. -/
public theorem mu'_xi_mem_section_of_pi_xi_fusion
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hxi : IsConj (pi D e) (pi D e * xi D e)) :
    mu' D e * xi D e ∈ s.ambientSubgroup := by
  rcases (section_marking_alternatives D e s).2.2 with h | h
  · exact h
  · exfalso
    apply section_involution_not_isConj_pi D e s hfusion _ h
    · change orderOf (D.a10ModelEmbedding e (modelElement 0) *
        (D.a10ModelEmbedding e (modelElement 2) * D.a10ModelEmbedding e (modelElement 7))) = 2
      rw [← map_mul, ← map_mul, orderOf_injective _ (D.a10ModelEmbedding_injective e)]
      exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    · apply hxi.trans
      have hlocal : IsConj (modelElement 0 * modelElement 7)
          (modelElement 0 * (modelElement 2 * modelElement 7)) :=
        isConj_iff.mpr ⟨modelElement 4, by decide +kernel⟩
      simpa only [map_mul, element] using (D.a10ModelEmbedding e).map_isConj hlocal

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
