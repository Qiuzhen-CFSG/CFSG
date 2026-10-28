module

public import Theory.Representation.BinaryOffender.IrreducibleDiagonal
public import Theory.GroupTheory.CentralPChiefFactors
public import Theory.GroupTheory.PResidual.Defs
public import CFSG.Quasithin.ChapterB.Section01.Restriction
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleMovedSpace
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleStabilizer
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleOrbitContradiction

/-!
# B.7.2(1): irreducible-section invariance

The source assumes a faithful finite-dimensional binary representation, a best
offender A, a nontrivial subgroup X = O²(X) = [X,A], and central 2-chief factors
of X. The latter hypothesis is `Subgroup.HasCentralPChiefFactors 2 X`: it uses
normal intervals inside X and their literal relative quotients. The
conclusion is setwise stabilization of each `IsIrrPlus ρ X I` by each a in A
with [V,a,A] = 0, not pointwise fixation of the vectors of I.

If a moves I, restrict to the faithful action image on W = I + Iᵃ. The
moved-space reduction transports every source hypothesis, including the best
offender property and central chief factors. The commutator identity makes the
restricted a normalize the image of X, so its image of I is again in Irr⁺.
The residual and chief-factor hypotheses give O₂(X) ≤ Z(X) and then a trivial
stabilizer of I in the restricted offender. Counting its regular orbit together
with the a-diagonal in W/C_W(X) yields the quotient diagonal contradiction.
Thus no moved member exists. All reduction premises are discharged here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.7.2(1), printed p. 119 (PDF p. 130).
-/

public section

namespace CFSG.Quasithin.ChapterB
open Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- B.7.2(1): an element a of a best offender with [V,a,A] = 0 fixes every
member of Irr⁺(X,V) setwise, under the source residual and chief-factor hypotheses. -/
theorem source_lemma_B_7_2_1 [Finite G] [FiniteDimensional (ZMod 2) V]
    (hfaithful : Function.Injective ρ) {A X : Subgroup G}
    (hA : IsBestOffender ρ A) (hXne : X ≠ ⊥) (hres : pResidual 2 X = ⊤)
    (hXA : ⁅X, A⁆ = X) (hchief : Subgroup.HasCentralPChiefFactors 2 X)
    {a : G} (ha : a ∈ A)
    (hq : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) :
    a ∈ subspaceStabilizer ρ I := by
  apply (subspace_map_eq_iff ρ I a).mp
  by_contra hne
  let W := I ⊔ I.map (ρ a)
  let ρw := subspaceImageRepresentation ρ W
  let Aw := restrictedSubgroup ρ W A
  let Xw := restrictedSubgroup ρ W X
  obtain ⟨hfw, hAw, hXwne, hresw, hXAw, hchiefw, _, hIw, _,
    aw, haw, _, hqw, hnew, hsupw⟩ :=
    movedSpace_action_data ρ hfaithful hA hXne hres hXA hchief ha hq hI (Ne.symm hne)
  have hAN : Aw ≤ Subgroup.normalizer (Xw : Set (subspaceActionImage ρ W)) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hXAw.le
  have hIaw := hIw.map_normalizer ρw (hAN haw)
  have hstab := irreducible_stabilizer_eq_bot ρw hfw hAw.1 hXwne hresw
    hXAw hchiefw haw hqw hIw hIaw hnew hsupw
  exact irreducible_orbit_contradiction ρw hfw hAw hXAw haw hqw hIw hIaw hnew hsupw hstab

end CFSG.Quasithin.ChapterB
