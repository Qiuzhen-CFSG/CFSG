module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.SymmetricOuter.Factors

/-!
# Assembly of the symmetric outer degree-twenty bounds

The actual inner intersection of an elementary actor of rank at least four
has rank at least three. The marked constituent identification carries it
injectively into S8. Its cost on the induced eight-space, together with
the nontrivial action on the deleted six-space, adds to the involution's
own displacement by the image--homology inequality.

The universal constituent identification and the rank-three estimate on the
concrete induced model are explicit pending inputs. Thus these are conditional
assembly theorems, not an unconditional proof of the HS source paragraph.
Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
preprint pp.16--17; Aschbacher--Smith K.4, printed p.457.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
open Subgroup Theory.GroupTheory Representation.BinaryOffender

namespace Twenty.Symmetric
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Image and homology costs give the strict bound on a rank-four or larger
actor, conditional on actual layer identifications and the model calculation. -/
theorem eleven_le_of_factors (h : SourceHypotheses ρ)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS)
    (hmodel : InducedRankThreeBound) {A : Subgroup G} (hA : IsElementaryTwo A)
    (hr : 4 ≤ rank A) {t : G} (htA : t ∈ A) (F : Factors ρ e t) :
    11 ≤ fixedCodim ρ A := by
  let := hA.2
  have hAC : A ≤ centralizer {t} := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun x : A => (x : G))
      ((IsMulCommutative.is_comm (M := A)).comm ⟨a, ha⟩ ⟨t, htA⟩)
  let D := A ⊓ generalizedFitting G
  have hDr : 3 ≤ rank D := by
    have hh := rank_le_inner_rank_add_one h hA
    change rank A ≤ rank D + 1 at hh
    omega
  have hDne : D ≠ ⊥ := by
    intro hz
    rw [hz, Representation.BinaryOffender.rank_bot] at hDr
    omega
  have hD := hA.of_le (show D ≤ A from inf_le_left) hDne
  let := hD.2
  have hDK : D ≤ innerCentralizer t :=
    le_inf (inf_le_left.trans hAC) inf_le_right
  let B := D.subgroupOf (innerCentralizer t)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hDK
  have hBr : rank B = rank D := rank_subgroupOf hDK
  have hEr : 3 ≤ rank (B.map F.marking) := by
    rw [F.rank_map_marking h B, hBr]
    exact hDr
  have hEne : B.map F.marking ≠ ⊥ := by
    intro hz
    rw [hz, Representation.BinaryOffender.rank_bot] at hEr
    omega
  have hE : IsElementaryTwo (B.map F.marking) :=
    ⟨hEne, IsElementaryAbelian.map F.marking⟩
  have hEight := hmodel _ hE hEr
  have hSix := Representation.SymmetricEightConstituents.deleted_fixedCodim_pos _ hEne
  change 1 ≤ fixedCodim Models.deleted (B.map F.marking) at hSix
  have hBA : B.map (innerCentralizer t).subtype ≤ A := by
    rw [show B = D.subgroupOf (innerCentralizer t) from rfl,
      map_subgroupOf_eq_of_le hDK]
    exact inf_le_left
  have hh := F.codim_bound
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) t htA) A htA B hBA
  omega

/-- Conditional construction of the exact three-field interface consumed
by the degree-twenty assembly. The two pending inputs are not source hypotheses. -/
theorem estimates_of_factors (h : SourceHypotheses ρ)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS)
    (hmodel : InducedRankThreeBound)
    (hfactors : ∀ t : G, t ^ 2 = 1 → IsSymmetricOuter e t → Nonempty (Factors ρ e t)) :
    SymmetricOuterEstimates ρ e := by
  constructor
  · intro t ht hs
    obtain ⟨F⟩ := hfactors t ht hs
    exact F.displacement.ge
  · intro A hA hr t htA hs
    let := hA.2
    obtain ⟨F⟩ := hfactors t (elemPow_eq_one_of_isElementaryAbelian (p := 2) t htA) hs
    exact (by decide : 10 ≤ 11).trans (eleven_le_of_factors h e hmodel hA (by omega) htA F)
  · intro A hA hr t htA hs
    let := hA.2
    obtain ⟨F⟩ := hfactors t (elemPow_eq_one_of_isElementaryAbelian (p := 2) t htA) hs
    exact eleven_le_of_factors h e hmodel hA (by omega) htA F

/-- Application to the original degree-twenty consumer. The independent
inner and elementary-outer branches, and both pending symmetric inputs,
remain explicit until their producers finish. -/
theorem gap_of_factors (h : SourceHypotheses ρ)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS)
    (hI : InnerEstimates ρ) (hE : ElementaryOuterEstimates ρ e)
    (hmodel : InducedRankThreeBound)
    (hfactors : ∀ t : G, t ^ 2 = 1 → IsSymmetricOuter e t → Nonempty (Factors ρ e t))
    (A : Subgroup G) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim ρ A :=
  gap_of_estimates h e hI hE (estimates_of_factors h e hmodel hfactors) A hA

end Twenty.Symmetric
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
