module

public import Theory.SpecificGroups.MathieuAmalgamCompletion.CubicVariants
public import Mathlib.Data.Fin.VecNotation

/-!
# Retaining the same nineteen words while selecting the exterior cubic

Only the cubic word and the mixed commutator word in the proved nineteen-word
cut mention the exterior cubic. The elementary-nine variants retain both,
while every other proved word keeps exactly the same literal generators.
-/

public section
namespace Theory.SpecificGroups.MathieuAmalgamCompletion
open Subgroup Subgroup.CosetWordCertificate
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem support : ∀ i : Fin 27,
    (i.val<17 ∨ i=23) → i≠13 → ∀ a∈relator i, a.1≠3 := by decide +kernel

private theorem eval_agrees (g h : Fin 4→G) (w : Word (Fin 4))
    (ha : ∀ a∈w,g a.1=h a.1) : eval g w=eval h w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [eval_cons,eval_cons,ha a (by simp),ih (fun b hb => ha b (by simp [hb]))]

/-- Select any of the six original exterior cubics while retaining all
nineteen previously proved relations on the same endpoint pair and ell. -/
theorem partial_relators_cubic_variants (P : Subgroup G) (pair : Fin 2→G)
    (t n r ell : G) (ht : t∈P) (ht3 : orderOf t=3) (hn3 : orderOf n=3)
    (hnt : Commute n t) (hnT : n∉zpowers t)
    (hrt : r*t*r⁻¹=t⁻¹) (hrn : r*n*r⁻¹=n⁻¹)
    (helt : Commute ell t) (hcross : ⁅ell,n⁆^2=1)
    (hrel : ∀ i : Fin 27, (i.val<17 ∨ i=23 ∨ i=26) →
      eval ![pair 0,pair 1,ell,n] (relator i)=1)
    (b : Bool) (k : Nat) :
    let m := (if b then n⁻¹ else n)*t^k
    ∀ i : Fin 27, (i.val<17 ∨ i=23 ∨ i=26) →
      eval ![pair 0,pair 1,ell,m] (relator i)=1 := by
  let m := (if b then n⁻¹ else n)*t^k
  obtain ⟨_,hm3,_,_,hmixed,_⟩ :=
    cubic_variants_preserve_source P t n r ell ht ht3 hn3 hnt hnT hrt hrn helt hcross b k
  change ∀ i : Fin 27, (i.val<17 ∨ i=23 ∨ i=26) →
    eval ![pair 0,pair 1,ell,m] (relator i)=1
  intro i hi
  by_cases h13 : i=13
  · subst i
    have hh : m^3=1 := hm3 ▸ pow_orderOf_eq_one m
    simpa [relator,decode,eval,FreeGroup.lift_mk,pow_succ,mul_assoc] using hh
  by_cases h26 : i=26
  · subst i
    exact mixed_relator_of_commutator_square _ hmixed
  have hshort : i.val<17 ∨ i=23 := by tauto
  have he : eval ![pair 0,pair 1,ell,m] (relator i)=
      eval ![pair 0,pair 1,ell,n] (relator i) := by
    apply eval_agrees
    intro a ha
    have hj := support i hshort h13 a ha
    rcases a with ⟨j,c⟩
    fin_cases j <;> simp_all
  exact he.trans (hrel i hi)

end Theory.SpecificGroups.MathieuAmalgamCompletion
