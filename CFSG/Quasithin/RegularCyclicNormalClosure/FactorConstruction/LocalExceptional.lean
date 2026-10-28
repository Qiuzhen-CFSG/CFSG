module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.LocalCandidate
public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.LocalOddness
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Suborbits
public import CFSG.Quasithin.GoldschmidtONan.OddTerminal

/-!
# Conditional exceptional local source assembly

For the actual maximal-intersection quotient, the transitive geometry
branch implies oddness by an ambient rank argument. The proved GLS odd
terminal, with Step 1 supplied by its input, then yields a local exceptional
candidate with every local clause of FactorSeed.

The transitive-geometry premise is explicit. This theorem does not exclude
the complement alternative or prove global compatibility of conjugate
factors, and is not the unconditional exists_factorSeed source theorem.
The odd-terminal dependency is assembled above Theory; this neither imports
Feit–Thompson into Theory nor promotes its standalone dependency closure.

Sources: Aschbacher–Smith E.6.24, printed p.255; GLS Number 2, C.14.2,
printed pp.85–89, including its complete terminal proof on p.89.
-/

public section

open Module Subgroup Representation Representation.BinaryOffender
open Representation.RegularCyclicNormalClosure
open Representation.RegularCyclicNormalClosure.FactorConstruction
open scoped IsMulCommutative
namespace CFSG.Quasithin.RegularCyclicNormalClosure
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- Conditional local source assembly: the transitive geometry branch of
the actual maximal-intersection quotient gives the exceptional local candidate.
Global compatibility of distinct conjugates is not included. -/
theorem exceptionalCandidate_of_transitiveGeometry (h : Input ρ C)
    (a : A) (hnc : ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d)
    (F : Submodule (ZMod 2) W)
    (hF : F = fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a))
    (hmax : ∀ b : A, (fixedSpace ρ C).map (ρ b) ≠ fixedSpace ρ C →
      finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ b)) ≤ finrank (ZMod 2) F)
    (hgeom : Representation.GoldschmidtONan.TransitiveGeometry (quotientOnFixer ρ F)
      (C.subgroupOf (pointwiseFixer ρ F))) :
    ExceptionalCandidate ρ C (pointwiseFixer ρ F) := by
  have hne : (fixedSpace ρ C).map (ρ a) ≠ fixedSpace ρ C := by
    intro he
    apply hnc
    rw [h.normal_in_stabilizer a he]
    let := h.cyclic
    intro c hc d hd
    exact (Commute.all (⟨c, hc⟩ : C) ⟨d, hd⟩).map C.subtype
  have hdim := h.intersection_dimensions a hne
  rw [← hF] at hdim
  have hFU : F < fixedSpace ρ C := lt_of_le_of_ne (hF.le.trans inf_le_left)
    (fun he => by rw [he] at hdim; exact (Nat.lt_irrefl _) hdim.1)
  have hlocal := h.goldschmidtONan_onFixer F hFU hdim.2 hmax
  have hodd := h.odd_pointwiseFixer_of_transitiveGeometry F hFU.le hmax hgeom
  let : Finite (W ⧸ F) := Finite.of_surjective F.mkQ F.mkQ_surjective
  have hexc := CFSG.Quasithin.GoldschmidtONan.exceptionalCase_of_odd hlocal
    hlocal.suborbitGeometry hgeom hodd
  exact h.exceptionalCandidate_of_quotient a hnc F hF hexc

end CFSG.Quasithin.RegularCyclicNormalClosure
