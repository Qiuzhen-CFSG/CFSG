module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.Splitting
public import Theory.SpecificGroups.SymmetricFive.CommonInvertedCubics

/-!
# The original cubic centralizer lifts the common-inverter relation

The marked direct-product splitting puts every actual commutator in the
S5 factor. Hence the common-transposition cubic relation in the literal
odd-core quotient lifts to square one in the original ambient group.
The quotient marking is arbitrary and is preserved in the hypotheses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Two original cubic-centralizer elements whose quotient cubics are
inverted by the same actual transposition have commutator of square one. -/
theorem TypeAt.cubic_centralizer_inverted_cubics_commutator_square
    (h : TypeAt z V) (t : G) (ht : t∈involutionCentralizer z) (ht3 : orderOf t=3)
    (φ : (centralizer ({t} : Set G) ⧸ pPrimeCore 2 (centralizer ({t} : Set G))) ≃*
      Equiv.Perm (Fin 5))
    (x y : centralizer ({t} : Set G)) (hx : x^3=1) (hy : y^3=1)
    (a : Equiv.Perm (Fin 5)) (ha : a.IsSwap)
    (hax : a*φ (QuotientGroup.mk x)*a⁻¹=(φ (QuotientGroup.mk x))⁻¹)
    (hay : a*φ (QuotientGroup.mk y)*a⁻¹=(φ (QuotientGroup.mk y))⁻¹) :
    ⁅(x:G),(y:G)⁆^2=1 := by
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  let q := QuotientGroup.mk' O
  have hxq : (φ (q x))^3=1 := by rw [←map_pow,←map_pow,hx,map_one,map_one]
  have hyq : (φ (q y))^3=1 := by rw [←map_pow,←map_pow,hy,map_one,map_one]
  have hh := Theory.SpecificGroups.SymmetricFive.common_transposition_inverted_cubics_commutator_square
    a (φ (q x)) (φ (q y)) ha hxq hyq hax hay
  have hq : q (⁅x,y⁆^2)=1 := by
    apply φ.injective
    rw [map_one,map_pow,map_commutatorElement,map_pow,map_commutatorElement]
    exact hh
  obtain ⟨ψ,_,_,_,e,_,heq,_⟩ := h.cubic_centralizer_split t ht ht3
  have hcoord (w : C) : (e.symm w).2=ψ (q w) := by
    simpa only [e.apply_symm_apply] using (heq (e.symm w).1 (e.symm w).2).symm
  have hz : ⁅x,y⁆^2=1 := by
    apply e.symm.injective
    apply Prod.ext
    · let : CommGroup (zpowers t) := IsCyclic.commGroup
      simp only [map_pow,map_commutatorElement,Prod.pow_fst,map_one,
        Prod.fst_one]
      simp [commutatorElement_def]
    · rw [hcoord,hq,map_one,map_one]
      rfl
  have hh := congrArg C.subtype hz
  simpa only [map_pow,map_commutatorElement,map_one,Subgroup.subtype_apply] using hh

end CFSG.Quasithin.HigmanSims
