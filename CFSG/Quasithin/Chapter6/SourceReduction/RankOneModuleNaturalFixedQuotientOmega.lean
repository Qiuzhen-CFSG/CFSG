module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientSource
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalModuleComparison
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarFullEnlargement
import all CFSG.Quasithin.Chapter6.Section01.SourceHStarLeftCartanOvergroup

/-!
# The literal omega-span quotient in the Thompson-moving source branch

A noncentral invariant subgroup of a marked natural fixed quotient still
maps onto the same natural module: SL₂ transitivity on nonzero vectors
proves surjectivity of the restricted coordinate map. The kernel remains
the original pointwise centralizer and the quotient actor is unchanged.

Enlarge the original Hypothesis 6.1.1 module to R₂(LT). Its actual natural
quotient forces L to move the Sylow omega-center. Restriction therefore
gives the natural fixed quotient on its literal L-span. The remaining
stationary Thompson branch of 6.1.4 is not asserted here.
-/
set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G]

/-- Restriction to a noncentral invariant subgroup preserves the exact actor
and fixed kernel of a natural quotient. -/
theorem IsNaturalFixedQuotient.of_noncentral_subgroup
    {L U V : Subgroup G} {n : ℕ} (hm : IsNaturalFixedQuotient L V n)
    (hUV : U ≤ V) (hLU : L ≤ normalizer (U : Set G))
    (hne : ¬ U ≤ centralizer (L : Set G)) : IsNaturalFixedQuotient L U n := by
  obtain ⟨F,_,_,_,hF,e,m,he⟩ := hm
  let := ZMod.algebra F 2
  let f := m.quotient.comp (inclusion hUV)
  have hf : Function.Surjective f := by
    obtain ⟨u,hu,huc⟩ := SetLike.not_le_iff_exists.mp hne
    let uV : V := ⟨u,hUV hu⟩
    have huz : (m.quotient uV).toAdd ≠ 0 := by
      intro hz
      have hk : uV ∈ m.quotient.ker := hz
      rw [m.kernel] at hk
      exact huc hk
    intro w
    by_cases hw : w = 1
    · exact ⟨1,by rw [map_one,hw]⟩
    have hwz : w.toAdd ≠ 0 := hw
    obtain ⟨s,hs⟩ := Theory.SpecificGroups.SymplecticFour.natural_transitive huz hwz
    obtain ⟨q,hq⟩ := e.surjective s
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    let uL : U := U.normalizerMonoidHom ⟨l,hLU l.property⟩ ⟨u,hu⟩
    refine ⟨uL,?_⟩
    have hh := m.equivariant l uV
    rw [he] at hh
    change m.quotient (V.normalizerMonoidHom ⟨l,m.normalizes l.property⟩ uV) =
      Multiplicative.ofAdd (specialLinearNatural 2
        (e (QuotientGroup.mk' (pCore 2 L) l)) (m.quotient uV).toAdd) at hh
    rw [hl,hq] at hh
    change m.quotient (V.normalizerMonoidHom ⟨l,m.normalizes l.property⟩ uV) =
      Multiplicative.ofAdd (Matrix.mulVec s.val (m.quotient uV).toAdd) at hh
    rw [hs] at hh
    exact hh
  let m' : ConjugationQuotientModel L U
      ((specialLinearNatural (k:=F) 2).restrictScalars (k:=ZMod 2)) := {
    normalizes := hLU
    actor := m.actor
    quotient := f
    surjective := hf
    kernel := by
      ext u
      change (inclusion hUV u) ∈ m.quotient.ker ↔ _
      rw [m.kernel]
      rfl
    equivariant := by
      intro l u
      exact m.equivariant l (inclusion hUV u) }
  exact ⟨F,inferInstance,inferInstance,inferInstance,hF,e,m',he⟩

namespace Hypothesis611
variable [Finite G] {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The moving source branch supplies the exact omega-span marking consumed
by the original Chapter 6.1.5 and Chapter 12 constructions. -/
theorem omega_natural_fixed_quotient_of_thompson_moves
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n := by
  let R := reducedSubgroup (L ⊔ (T : Subgroup G))
  let hR := h.reduced_enlargement
  have hjR : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (R : Set G) :=
    fun hc => hj (hc.trans (centralizer_le (reduced_le_reducedSubgroup h.V_mem)))
  have hm := hR.natural_fixed_quotient_of_thompson_moves hout hjR
  let hi := hR.rankOneInput hout
  obtain ⟨A,B,c⟩ := RankOneGeneric.exists_left_cartan_pair hi
  have hLC := hi.natural_quotient_not_centralizes_omega c hm
  have hUR : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L ≤ R :=
    conjugateSpanBy_le h.omega_le_reduced_enlargement
      (le_sup_left.trans (reduced_normalizes hR.V_mem))
  apply hm.of_noncentral_subgroup hUR (le_normalizer_conjugateSpanBy _ _)
  intro hc
  exact hLC (le_centralizer_iff.mp ((le_conjugateSpanBy _ _).trans hc))

end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
