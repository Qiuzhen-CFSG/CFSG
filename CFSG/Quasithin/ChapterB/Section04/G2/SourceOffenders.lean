module
public import Theory.Representation.G2NaturalOffenders
public import CFSG.Quasithin.ChapterB.Section04.G2.SourceGeometry

/-!
# Genuine inner offenders on the original B.4.6 module

The source hypothesis V = [V,E(L)] identifies fixed codimensions on V with
those on the literal natural quotient V/C_V(L). Its given equivariant
identification with the octonion module then transports the concrete
natural offender classification. Every inner offender is an A–B–C
conjugate under the specified group identification; both its rank and its
fixed codimension are 3n. This also excludes strong offenders and gives
quadratic ratio one under the source FF hypothesis.

No root-placement or elementary fusion conclusion is assumed. Source:
Aschbacher–Smith B.4.6(7), (13), printed pp.88–90. The ambient outer-actor
containment is a separate part of the original lemma.
-/

@[expose] public section
open Representation Atlas.G2.Natural
namespace CFSG.Quasithin.ChapterB.Section04.G2
open Representation.OneCohomology Representation.BinaryOffender
variable {F L V : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
  [Group L] [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable (σ : Representation (ZMod 2) L V)
    (hgen : Coinvariants.ker (σ.comp (Theory.GroupTheory.componentLayer L).subtype) = ⊤)
    (eL : L ≃* Atlas.G2.Model F)
    (eN : (V ⧸ fixed σ) ≃ₗ[ZMod 2] Space F)
    (he : ∀ g v, eN (naturalQuotientAction σ g v) = action F (eL g) (eN v))
    {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n)

include hgen eL eN he hc hn

/-- The actual B.4.6 action sends every offender to the concrete A–B–C conjugacy class. -/
theorem offender_conjugate_elementary (A : Subgroup L) (hA : IsOffender σ A) :
    ∃ g : Atlas.G2.Model F,
      A.map eL.toMonoidHom = (Atlas.G2.EvenTwoRank.elementary F).map (MulAut.conj g).toMonoidHom := by
  have hq := (offender_naturalQuotient_iff σ hgen eL eN he A).mp hA
  have hm := hq.map_equivariant (naturalQuotientAction σ)
    (Atlas.G2.NaturalOffenders.binaryNatural (F:=F)) eL.toMonoidHom eL.injective eN he
  exact Atlas.G2.NaturalOffenders.natural_offender_conjugate_elementary hc hn _ hm

/-- B.4.6(13) retains the exact rank and fixed codimension on V, not just on its quotient. -/
theorem offender_rank_and_fixedCodim (A : Subgroup L) (hA : IsOffender σ A) :
    rank A = 3*n ∧ fixedCodim σ A = 3*n := by
  have hq := (offender_naturalQuotient_iff σ hgen eL eN he A).mp hA
  have hm := hq.map_equivariant (naturalQuotientAction σ)
    (Atlas.G2.NaturalOffenders.binaryNatural (F:=F)) eL.toMonoidHom eL.injective eN he
  constructor
  · rw [← rank_map_injective eL.toMonoidHom eL.injective]
    exact Atlas.G2.NaturalOffenders.natural_offender_rank hc hn _ hm
  · rw [fixedCodim_naturalQuotient_eq σ hgen eL eN he,
      fixedCodim_map_equivariant (naturalQuotientAction σ)
        (Atlas.G2.NaturalOffenders.binaryNatural (F:=F)) eL.toMonoidHom eN he]
    exact Atlas.G2.NaturalOffenders.natural_offender_fixedCodim hc hn _ hm

/-- In particular the original source action has no strong offender. -/
theorem no_strong_offender : ¬ IsStrongFFModule σ := by
  rintro ⟨A,hA⟩
  obtain ⟨hr,hd⟩ := offender_rank_and_fixedCodim σ hgen eL eN he hc hn A ⟨hA.1,hA.2.le⟩
  have hl := hA.2
  omega

/-- The FF hypothesis of B.4.6 gives its exact action ratio on the original module. -/
theorem quadraticRatio_eq_one (hff : IsFFModule σ) : quadraticRatio σ = 1 := by
  let : Finite L := Finite.of_equiv (Atlas.G2.Model F) eL.symm.toEquiv
  exact quadraticRatio_eq_one_of_no_strong σ hff
    (fun A hA => no_strong_offender σ hgen eL eN he hc hn ⟨A,hA⟩)

end CFSG.Quasithin.ChapterB.Section04.G2
