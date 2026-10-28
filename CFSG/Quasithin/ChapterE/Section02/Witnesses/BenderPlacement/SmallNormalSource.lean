module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallNormal

/-!
# Original solvable E.2.17 normal-core consumer

The solvable E.2.9 witness is constructed from the original minimal-parabolic
configuration. Applying the global small-section argument gives an ambient
normal quaternion core, its Sylow containment, centralizer product and marked
commutator bound. No witness or ambient normalization is added as a premise.

Source: Aschbacher--Smith, E.2.17, solvable branch, printed pp.229--230.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {V U : Subgroup H} [IsElementaryAbelian 2 V]
theorem source_solvable_small_normal_core
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
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU q hq hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    ∃ P : Subgroup H, P.Normal ∧ P ≤ (T : Subgroup H) ∧
      Nonempty (QuaternionCentralProductData P) ∧
      U = P ⊔ (U ⊓ centralizer (V : Set H)) ∧
      P ⊓ centralizer (V : Set H) = P ⊓ V ∧
      ⁅U ⊓ centralizer (V : Set H),P⁆ ≤ P ⊓ V := by
  obtain ⟨w₀⟩ := Solvable.solvable_witness T hP hs V hVT hvn hVM hout
  let w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V 1 :=
    OriginalWitness.of_dihedral w₀
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  exact ⟨w.pair.subgroup.pCoreIn 2,w.small_normal_core_of_solvable hH hP hs
    hVT hTV hVM hout hfit hV hTU hU q hq hk hD hratio hres⟩
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
