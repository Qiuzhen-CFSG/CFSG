module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadRelator25
public import Theory.SpecificGroups.MathieuAmalgamCompletion.CubicVariantRelations

/-!
# Joining the fixed-free cubic word to the nineteen-word cut

The native lift of the cubic word supplies relation 25.  The already proved
nineteen-word source is transported through the same selected variant; the
Bool convention is bridged explicitly because the quotient lift and the
nineteen-word transport use opposite inverse flags.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetWordCertificate
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G]

theorem join_hexad_relator25_to_twenty
    (P : Subgroup G) (pair : Fin 2→G) (t n r ell : G)
    (ht : t∈P) (ht3 : orderOf t=3) (hn3 : orderOf n=3)
    (hnt : Commute n t) (hnT : n∉zpowers t)
    (hrt : r*t*r⁻¹=t⁻¹) (hrn : r*n*r⁻¹=n⁻¹)
    (helt : Commute ell t) (hcross : ⁅ell,n⁆^2=1)
    (hrel : ∀ i : Fin 27, (i.val<17 ∨ i=23 ∨ i=26) →
      eval ![pair 0,pair 1,ell,n]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1)
    (h25 : ∃ b : Bool, ∃ j : Fin 3,
      let m := (if b then n else n⁻¹)*t^j.val
      ∀ x : G, eval ![pair 0,pair 1,x,m]
        (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 25)=1) :
    ∃ b : Bool, ∃ j : Fin 3,
      let m := (if b then n else n⁻¹)*t^j.val
      ∀ i : Fin 27, (i.val<17 ∨ i=23 ∨ i=25 ∨ i=26) →
        eval ![pair 0,pair 1,ell,m]
          (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1 := by
  obtain ⟨b,j,h25⟩ := h25
  let b' := !b
  have hrel' := Theory.SpecificGroups.MathieuAmalgamCompletion.partial_relators_cubic_variants
    P pair t n r ell ht ht3 hn3 hnt hnT hrt hrn helt hcross hrel b' j.val
  refine ⟨b,j,?_⟩
  let m := (if b then n else n⁻¹)*t^j.val
  change ∀ i : Fin 27, (i.val<17 ∨ i=23 ∨ i=25 ∨ i=26) →
    eval ![pair 0,pair 1,ell,m]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator i)=1
  intro i hi
  by_cases h25i : i=25
  · subst i
    exact h25 ell
  have h19 : i.val<17 ∨ i=23 ∨ i=26 := by
    rcases hi with hi | hi
    · exact Or.inl hi
    rcases hi with hi | hi
    · exact Or.inr (Or.inl hi)
    rcases hi with hi | hi
    · exact (h25i hi).elim
    · exact Or.inr (Or.inr hi)
  have hsame : (if b' then n⁻¹ else n)*t^j.val=m := by
    dsimp [b',m]
    cases b <;> simp
  rw [←hsame]
  exact hrel' i h19

end CFSG.Quasithin.HigmanSims
