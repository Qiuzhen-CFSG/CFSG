module

public import CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.ProperSections
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.E6Twisting

/-!
# Conditional assembly of the folded exceptional sections

These adapters use the actual folded subgroup and the actual central
projections. They retain the unproved F4 identification, triviality of the folded subgroup center,
and properness of the projected maps as explicit premises. Thus they do not
assert the exceptional inclusions from A.2.17 without their missing matrix
realization and central-intersection proofs.

The twisted square uses GF(p^(m+1)) inside GF(p^(2*(m+1))) through
`coefficientEmbedding`, and the target is the center quotient of O^{p'} of
the graph--field fixed group. This discharges the field and central-cover
bookkeeping for the source inclusion once the three geometric premises are
supplied.

Source: Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`;
GLS3 §§2.2--2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterA.Section02
open TwistedE6.FoldedSubsystem
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _

variable {S H G : Type*} [Group S] [Group H] [Group G]

/-- Transport the source of a proper embedding through an actual group equivalence. -/
def ChainEdge.precompEquiv (d : ChainEdge H G) (e : S ≃* H) : ChainEdge S G where
  map := d.map.comp e.toMonoidHom
  injective := d.injective.comp e.injective
  proper := by
    rw [MonoidHom.range_comp, e.toMonoidHom.range_eq_top_of_surjective e.surjective,
      ← MonoidHom.range_eq_map]
    exact d.proper

private theorem centralProjection_comp_injective
    (f : H →* G) (hf : Function.Injective f) (hc : Subgroup.center H = ⊥) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hfx : f x ∈ Subgroup.center G := (QuotientGroup.eq_one_iff (f x)).mp hx
  have hxcenter : x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply hf
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hfx (f y)
  simpa only [hc, Subgroup.mem_bot] using hxcenter

variable (F : Type*) [Field F] [Finite F]

/-- The folded realization and its projected faithfulness/properness imply the
literal split E6 contract. The premises are the remaining geometry, not source hypotheses. -/
def f4InE6OfFolding (e : ExceptionalSplit.F4 F ≃* splitSubgroup F)
    (hc : Subgroup.center (splitSubgroup F) = ⊥)
    (hp : (splitModelMap F).range ≠ ⊤) : F4InE6 F where
  edge := (⟨splitModelMap F,
    (by
      exact centralProjection_comp_injective (splitSubgroup F).subtype
        Subtype.val_injective hc), hp⟩ : ChainEdge _ _).precompEquiv e

/-- Higher exceptional realizations can use the folded subgroup directly,
without imposing a map on the entire adjoint E6 quotient. -/
def f4InE7OfFolding (e : ExceptionalSplit.F4 F ≃* splitSubgroup F)
    (d : ExceptionalSplit.ProperEmbedding (splitSubgroup F) (ExceptionalSplit.E7 F)) :
    F4InE7 F where
  edge := (⟨d.hom, d.injective, d.proper⟩ : ChainEdge _ _).precompEquiv e

def f4InE8OfFolding (e : ExceptionalSplit.F4 F ≃* splitSubgroup F)
    (d : ExceptionalSplit.ProperEmbedding (splitSubgroup F) (ExceptionalSplit.E8 F)) :
    F4InE8 F where
  edge := (⟨d.hom, d.injective, d.proper⟩ : ChainEdge _ _).precompEquiv e

variable (p m : ℕ) [Fact p.Prime]

/-- The literal commuting square for a supplied F4 folding identification.
The source cover is projected to F4, then transported and included in the
actual twisted defining-characteristic cover. -/
def foldedTwistedCentralEdge
    (e : ExceptionalSplit.F4 (GaloisField p (m + 1)) ≃*
      splitSubgroup (GaloisField p (m + 1)))
    (hc : Subgroup.center (splitSubgroup (GaloisField p (m + 1))) = ⊥)
    (hp : (modelMap p m).range ≠ ⊤) :
    CentralChainEdge
      (ExceptionalSplit.f4Cover (GaloisField p (m + 1)))
      (ExceptionalSplit.F4 (GaloisField p (m + 1)))
      (TwistedE6.centralCover p m) (TwistedE6.Model p m) where
  coverMap := (coverEmbedding p m).comp (e.toMonoidHom.comp
    (ExceptionalSplit.projection typeF4RootPairing typeF4RootPairing_base _))
  quotientMap := (modelMap p m).comp e.toMonoidHom
  sourceProjection := ExceptionalSplit.projection typeF4RootPairing typeF4RootPairing_base _
  targetProjection := TwistedE6.centralProjection p m
  commute := by ext x; rfl
  injective := by
    exact (centralProjection_comp_injective (coverEmbedding p m)
      (coverEmbedding_injective p m) hc).comp e.injective
  proper := by
    exact ((⟨modelMap p m,
      centralProjection_comp_injective (coverEmbedding p m) (coverEmbedding_injective p m) hc,
      hp⟩ : ChainEdge _ _).precompEquiv e).proper

def f4InTwistedE6OfFolding (hodd : Odd p)
    (e : ExceptionalSplit.F4 (GaloisField p (m + 1)) ≃*
      splitSubgroup (GaloisField p (m + 1)))
    (hc : Subgroup.center (splitSubgroup (GaloisField p (m + 1))) = ⊥)
    (hp : (modelMap p m).range ≠ ⊤) : F4InTwistedE6 p m where
  oddPrime := hodd
  exponent_positive := Nat.succ_pos m
  edge := (foldedTwistedCentralEdge p m e hc hp).toChainEdge

end CFSG.Quasithin.ChapterA.Section02
