module
public import Theory.SpecificGroups.G2.TernaryCubicForms

/-!
# Simultaneous cubic and commutator-form coordinates

A root-invariant form with coefficients a and b is normalized by an explicit
linear change commuting with the cubic. The conditions a ≠ 0 and a+b ≠ 0
mean that the cubic moves both its radical and the quotient by that radical.
The remaining scalar is a+b. Over F₃ it is a sign: a further explicit change
reverses the cubic and the form together when that sign is negative.
Thus the original scalar marking is preserved by choosing the cubic or its
inverse, rather than combining unrelated coordinate equivalences.

A second explicit change preserves the form and intertwines the literal
short and long root conventions. The original-group hypotheses are discharged
in G2Recognition.MaximalCubicForms, for Aschbacher–Smith I.4.5, printed p.417.
Root conventions and attribution: LICENSES/ATLAS-CITATION.cff and LICENSES/ATLAS.txt.
-/

public section
namespace Atlas.G2.TernaryCore
private def normalize (a b : ZMod 3) (ha : a≠0) (hab : a+b≠0) : V ≃* V where
  toFun v := Multiplicative.ofAdd ![(a*v.toAdd 0+b*v.toAdd 2)/(a+b),v.toAdd 1,v.toAdd 2,v.toAdd 3]
  invFun v := Multiplicative.ofAdd ![((a+b)*v.toAdd 0-b*v.toAdd 2)/a,v.toAdd 1,v.toAdd 2,v.toAdd 3]
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
    field_simp [ha,hab]
    ring
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
    field_simp [ha,hab]
    ring
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
    ring

private theorem normalize_root (a b : ZMod 3) (ha : a≠0) (hab : a+b≠0) (v : V) :
    normalize a b ha hab (shortRoot v)=shortRoot (normalize a b ha hab v) := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [normalize,shortRoot]
  field_simp [ha,hab]
  ring

private theorem normalize_form (a b : ZMod 3) (ha : a≠0) (hab : a+b≠0) (v w : V) :
    a*shortForm v w+b*(v.toAdd 2*w.toAdd 3-w.toAdd 2*v.toAdd 3)=
      (a+b)*shortForm (normalize a b ha hab v) (normalize a b ha hab w) := by
  simp [shortForm,normalize]
  field_simp [hab]
  ring

private def reverse : V ≃* V where
  toFun v := Multiplicative.ofAdd ![-v.toAdd 0,v.toAdd 1,-v.toAdd 2,v.toAdd 3]
  invFun v := Multiplicative.ofAdd ![-v.toAdd 0,v.toAdd 1,-v.toAdd 2,v.toAdd 3]
  left_inv v := by apply Multiplicative.toAdd.injective; ext i; fin_cases i <;> simp
  right_inv v := by apply Multiplicative.toAdd.injective; ext i; fin_cases i <;> simp
  map_mul' v w := by apply Multiplicative.toAdd.injective; ext i; fin_cases i <;> simp [add_comm]

private theorem reverse_root (v : V) :
    reverse (shortRoot (shortRoot v))=shortRoot (reverse v) := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [reverse,shortRoot] <;> ring_nf
  all_goals simp [show (2:ZMod 3)=-1 from rfl,sub_eq_add_neg]

private theorem reverse_form (v w : V) : shortForm (reverse v) (reverse w) = -shortForm v w := by
  simp [reverse,shortForm]
  ring

/-- Nondegenerate coefficients admit a simultaneous cubic/form normalization.
The cubic may be replaced by its inverse, as required by the fixed scalar marking. -/
theorem exists_shortRoot_form_normalization (a b : ZMod 3) (ha : a≠0) (hab : a+b≠0) :
    ∃ (e : V ≃* V) (flip : Bool),
      (∀ v,e (if flip then shortRoot (shortRoot v) else shortRoot v)=shortRoot (e v)) ∧
      (∀ v w,a*shortForm v w+b*(v.toAdd 2*w.toAdd 3-w.toAdd 2*v.toAdd 3)=
        shortForm (e v) (e w)) ∧
      (∀ v,(e v).toAdd 0=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0 ↔
        v.toAdd 0=0 ∧ v.toAdd 2=0 ∧ v.toAdd 3=0) := by
  let n := normalize a b ha hab
  have line (v) : (n v).toAdd 0=0 ∧ (n v).toAdd 2=0 ∧ (n v).toAdd 3=0 ↔
      v.toAdd 0=0 ∧ v.toAdd 2=0 ∧ v.toAdd 3=0 := by
    change (a*v.toAdd 0+b*v.toAdd 2)/(a+b)=0 ∧ v.toAdd 2=0 ∧ v.toAdd 3=0 ↔ _
    constructor
    · rintro ⟨h,h2,h3⟩
      rw [h2,mul_zero,add_zero,div_eq_zero_iff] at h
      exact ⟨(mul_eq_zero.mp (h.resolve_right hab)).resolve_left ha,h2,h3⟩
    · rintro ⟨h0,h2,h3⟩
      simp [h0,h2,h3]
  have cases : a+b=1 ∨ a+b=-1 := (by decide : ∀ k : ZMod 3,k≠0 → k=1 ∨ k=-1) _ hab
  rcases cases with h | h
  · refine ⟨n,false,fun v=>normalize_root a b ha hab v,?_,line⟩
    intro v w
    rw [normalize_form a b ha hab,h,one_mul]
  · refine ⟨n.trans reverse,true,?_,?_,?_⟩
    · intro v
      change reverse (n (shortRoot (shortRoot v)))=shortRoot (reverse (n v))
      rw [normalize_root,normalize_root,reverse_root]
    · intro v w
      change _=shortForm (reverse (n v)) (reverse (n w))
      rw [normalize_form a b ha hab,h,neg_one_mul,reverse_form]
    · intro v
      change -(n v).toAdd 0=0 ∧ -(n v).toAdd 2=0 ∧ (n v).toAdd 3=0 ↔ _
      simp only [neg_eq_zero]
      exact line v


/-- A simultaneous change between the two literal Atlas root conventions. -/
def shortLongCoordinates : V ≃* V where
  toFun v := Multiplicative.ofAdd ![v.toAdd 1,-v.toAdd 2,-v.toAdd 0,v.toAdd 3]
  invFun v := Multiplicative.ofAdd ![-v.toAdd 2,v.toAdd 0,-v.toAdd 1,v.toAdd 3]
  left_inv v := by apply Multiplicative.toAdd.injective; ext i; fin_cases i <;> simp
  right_inv v := by apply Multiplicative.toAdd.injective; ext i; fin_cases i <;> simp
  map_mul' v w := by apply Multiplicative.toAdd.injective; ext i; fin_cases i <;> simp [add_comm]

theorem shortLongCoordinates_root (v : V) :
    shortLongCoordinates (shortRoot v)=longRoot (shortLongCoordinates v) := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [shortLongCoordinates,shortRoot,longRoot,sub_eq_add_neg,add_comm]

/-- The Weyl conventions differ by the scalar involution under this same
form-preserving change. This is the equation used by the full actor comparison. -/
theorem shortLongCoordinates_weyl (v : V) :
    shortLongCoordinates (shortWeyl v)=(longWeyl (shortLongCoordinates v))⁻¹ := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [shortLongCoordinates,shortWeyl,longWeyl]

theorem shortLongCoordinates_form (v w : V) :
    longForm (shortLongCoordinates v) (shortLongCoordinates w)=shortForm v w := by
  simp [shortLongCoordinates,shortForm,longForm]
  ring

theorem shortLongCoordinates_line (v : V) :
    (shortLongCoordinates v).toAdd 1=0 ∧ (shortLongCoordinates v).toAdd 2=0 ∧
      (shortLongCoordinates v).toAdd 3=0 ↔ v.toAdd 0=0 ∧ v.toAdd 2=0 ∧ v.toAdd 3=0 := by
  simp [shortLongCoordinates,and_left_comm]
end Atlas.G2.TernaryCore
