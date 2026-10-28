module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Groups
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle

/-!
# The symplectic rank calculation for the original chosen geometry

The weak-closure theorem selects the literal conjugate of V inside R₂ and
proves its two normalizations. Its forward automizer bound then forces the
commutator and reverse automizer to have binary rank four. The swapped-module
marking is an explicit construction input of `qt-d-1141-swapped-natural-action`.
The opposing G₂ bound and the final contradiction are not asserted here.

Source: Aschbacher--Smith, 11.4.1(2), printed p.776.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
variable {G F : Type*} [Group G] [Field F] [Algebra (ZMod 2) F]
variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)

/-- The selected weak-closure conjugate has the source's commutator and reverse rank. -/
theorem ofFlag_exists_mutual_rank_four [Finite F]
    (X : Subgroup G) (z : G) (H₀ : Subgroup G)
    (hF : Nat.card F = 4) (I U : Subgroup G)
    (hout : ¬ I ≤ normalizer (L : Set G))
    (hN : normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G))
    (hC : (I ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) =
      (I ⊔ (T : Subgroup G)).pCoreIn 2)
    (hU : IsPGroup 2 U) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hW : indexedWeakClosure V (T : Subgroup G) 0 ≤ (ofFlag S f X z H₀).R₂)
    (hs : (4 : ℕ∞) ≤ @globalS G _ V D.elementary)
    (hr : (4 : ℕ∞) < globalR V)
    (α : (ofFlag S f X z H₀).R₂ →* Sp F) (e : U ≃* Multiplicative (Vector F))
    (hact : ∀ (a : (ofFlag S f X z H₀).R₂) (u : U),
      (e ⟨a.val * u.val * a.val⁻¹,
        (mem_normalizer_iff.mp (hTU (LocalGeometry.localRadical_le_sylow _ a.property))
          u.val).mp u.property⟩).toAdd = α a • (e u).toAdd)
    (himage : α.range ≤ Plane.radical.map planeLocal.subtype) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (ofFlag S f X z H₀).R₂ ∧
      V.map (MulAut.conj g).toMonoidHom ≤ T ∧
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (U : Set G) ∧
      U ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
      inducedAutomizer U (V.map (MulAut.conj g).toMonoidHom) ≠ ⊥ ∧
      4 ≤ Representation.BinaryOffender.rank
        (inducedAutomizer U (V.map (MulAut.conj g).toMonoidHom)) ∧
      ⁅U, V.map (MulAut.conj g).toMonoidHom⁆ =
        U ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
      rank (⁅U, V.map (MulAut.conj g).toMonoidHom⁆ : Subgroup G) = 4 ∧
      rank (inducedAutomizer (V.map (MulAut.conj g).toMonoidHom) U) = 4 := by
  obtain ⟨g, hgR, hgT, hgU, hUg, hne, hrank⟩ :=
    ofFlag_exists_mutually_normalizing_conjugate D S f X z H₀ hF I U hout hN hC
      hU hTU hW hs hr α e hact himage
  refine ⟨g, hgR, hgT, hgU, hUg, hne, hrank, ?_⟩
  exact RankComparison.mutual_plane_ranks hF (ofFlag S f X z H₀).R₂
    (V.map (MulAut.conj g).toMonoidHom) U hgR
    ((LocalGeometry.localRadical_le_sylow _).trans hTU) hUg α e hact himage hrank

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
