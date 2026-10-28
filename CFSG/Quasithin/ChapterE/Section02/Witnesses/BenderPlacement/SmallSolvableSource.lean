module

public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallExtension
public import CFSG.Quasithin.ChapterE.Section02.SolvableStructure.CubicActors

/-!
# Solvable source reduction for the small marked module

The original E.2.9 witness and the four-dimensional small-automizer calculation
force a dihedral quotient of order six. The E.2.1 source alternatives therefore
have residual prime three. The cyclic alternative gives the full conjugate span
and its normalized quaternion core; the other alternatives retain the actual
order-nine or extraspecial order-twenty-seven residual and its literal model.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, E.2.17,
solvable case. The two noncyclic residual alternatives require the subsequent
source exclusions; this theorem does not assume those exclusions.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {V U : Subgroup H} [IsElementaryAbelian 2 V]

theorem source_solvable_small_core_or_exceptional_residual
    {κ : GroupClass} (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hVT : V ≤ T) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU q hq hk)) :
    (let Y := conjugateSpanBy V ⊤
     Nonempty (QuaternionCentralProductData (Y.pCoreIn 2)) ∧
       U = Y.pCoreIn 2 ⊔ (U ⊓ centralizer (V : Set H)) ∧
       Y.pCoreIn 2 ⊓ centralizer (V : Set H) = Y.pCoreIn 2 ⊓ V ∧
       U ≤ normalizer (Y.pCoreIn 2 : Set H) ∧
       ⁅U ⊓ centralizer (V : Set H), Y.pCoreIn 2⁆ ≤ Y.pCoreIn 2 ⊓ V) ∨
    (Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 9 ∧
      Nonempty (pResidual 2 (H ⧸ pCore 2 H) ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))) ∨
    (Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 27 ∧
      IsExtraspecial 3 (pResidual 2 (H ⧸ pCore 2 H)) ∧
      Nonempty (pResidual 2 (H ⧸ pCore 2 H) ≃* HeisenbergPrime 3)) := by
  obtain ⟨w₀⟩ := Solvable.solvable_witness T hP hs V hVT hvn hVM hout
  let w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V 1 :=
    OriginalWitness.of_dihedral w₀
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hNV := ChapterE.minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  have hc := w.small_quaternion_core hVT hTV hVM hNV hfit hV hTU hU q hq hk hD hratio
  obtain ⟨e⟩ := hc.2.2.2.1
  have hI : Nat.card (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup) = 6 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have h3 : 3 ∣ Nat.card H := by
    have hh := (pCore 2 w.pair.subgroup).index_dvd_card
    change Nat.card (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup) ∣ Nat.card w.pair.subgroup at hh
    rw [hI] at hh
    exact ((by decide : 3 ∣ 6).trans hh).trans w.pair.subgroup.card_subgroup_dvd_card
  have he : ¬ (ChapterB.minimalParabolicMax T hP).pCoreIn 2 ≤ pCore 2 H := by
    intro hle
    exact hout (hVM.trans (hle.trans (ChapterB.minimalParabolicTwoCore_le_core T hP)))
  rcases SolvableMinimalParabolic.source_cubic_models hH T hP hs (Or.inl he) h3 with
    h3 | h9 | h27
  · have hn := w.small_normal_span_of_cubic_residual
      hVT hTV hVM hNV hfit hV hTU hU q hq hk hD hratio h3.1
    left
    dsimp only
    rw [hn.2.1]
    exact hn.2.2
  · exact Or.inr (Or.inl h9)
  · exact Or.inr (Or.inr h27)
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
