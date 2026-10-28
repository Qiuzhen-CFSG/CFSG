module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting.Defs
public import Theory.Representation.BinaryConjugationSection.FreeInvolution

/-!
# Two involution lifts in one H/Q fiber

Freeness at the chosen involution first corrects a lift modulo U using Q,
then modulo Z using U. Since Z has order two and is centralized by H, the
remaining alternatives are i and iz. The conjugator is an actual element
of Q. No fusion of those alternatives or counting assertion is assumed.

Source: Aschbacher–Smith, J.2.6, printed p.435 (PDF p.446).
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- In one literal H/Q fiber, Q-conjugation reduces every involution to the
chosen lift or its product with the nonidentity element of Z. -/
theorem involution_fiber_two_lifts (d : TypeRuSetup G)
    (hZ : Nat.card d.Z = 2) {z : G} (hz : z ∈ d.Z) (hz1 : z ≠ 1)
    (i x : d.H) (hi : (i : G) ^ 2 = 1) (hx : (x : G) ^ 2 = 1)
    (hnatural : FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i))
    (hsix : FreeAt d.ru2.sixAction (d.ru2.quotientMap i))
    (himage : d.ru2.quotientMap x = d.ru2.quotientMap i) :
    ∃ q : d.Q, (q : G) * x * (q : G)⁻¹ = i ∨
      (q : G) * x * (q : G)⁻¹ = (i : G) * z := by
  have hdiff : (x : G) * (i : G)⁻¹ ∈ d.Q := by
    have hk : x * i⁻¹ ∈ d.ru2.quotientMap.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, himage, mul_inv_cancel]
    rw [d.ru2.quotient_kernel] at hk
    exact hk
  obtain ⟨a, ha⟩ := d.ru2.six.correct_involution_mod_kernel i x hi hx hsix hdiff
  let y : d.H := ⟨(a : G) * x * (a : G)⁻¹,
    d.H.mul_mem (d.H.mul_mem (d.ru2.six.section_le a.property) x.property)
      (d.H.inv_mem (d.ru2.six.section_le a.property))⟩
  have hy : (y : G) ^ 2 = 1 := by
    change (MulAut.conj (a : G) (x : G)) ^ 2 = 1
    rw [← map_pow, hx, map_one]
  obtain ⟨u, hu⟩ := d.ru2.natural.correct_involution_mod_kernel i y hi hy hnatural ha
  let q : d.Q := ⟨(u : G) * a,
    d.Q.mul_mem (d.ru2.six.kernel_le u.property) a.property⟩
  have he : (q : G) * x * (q : G)⁻¹ = (u : G) * y * (u : G)⁻¹ := by
    change ((u : G) * a) * x * ((u : G) * a)⁻¹ =
      (u : G) * ((a : G) * x * (a : G)⁻¹) * (u : G)⁻¹
    group
  have hqZ : ((q : G) * x * (q : G)⁻¹) * (i : G)⁻¹ ∈ d.Z := by
    rw [he]
    exact hu
  let c : d.Z := ⟨_, hqZ⟩
  have hc : (c : G) = 1 ∨ (c : G) = z := by
    by_cases hc1 : c = 1
    · exact Or.inl (congrArg Subtype.val hc1)
    · obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : d.Z)).mp hZ
      exact Or.inr (congrArg Subtype.val
        ((hw c hc1).trans (hw ⟨z, hz⟩ (fun h => hz1 (congrArg Subtype.val h))).symm))
  refine ⟨q, ?_⟩
  rcases hc with hc | hc
  · exact Or.inl (mul_inv_eq_one.mp hc)
  · exact Or.inr ((mul_inv_eq_iff_eq_mul.mp hc).trans (i.property z hz))

end CFSG.Quasithin.ChapterJ.Fusion.Outer
