module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSFiveCentralizer

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]

/-- A large subgroup of the original Suzuki root span cannot centralize an
actual order-five subgroup of the remote-center join.  The full graph core
is retained by the imported DGS five-centralizer source. -/
theorem source_quintic_dgs_five_centralizer_escape
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (A : Subgroup (Reduction.G₀ ![H, sourceResidual M Mc ⊔ (T : Subgroup G)] (T : Subgroup G)))
    (hA : A ≤ Reduction.reducedFamily ![H, sourceResidual M Mc ⊔ (T : Subgroup G)]
      (T : Subgroup G) false) (hAc : Nat.card A = 5)
    (I : Subgroup (Reduction.G₀ ![H, sourceResidual M Mc ⊔ (T : Subgroup G)]
      (T : Subgroup G)))
    (hI : I ≤ V (Reduction.reducedFamily ![H, sourceResidual M Mc ⊔ (T : Subgroup G)]
      (T : Subgroup G)) (base (Reduction.reducedFamily ![H, sourceResidual M Mc ⊔ (T : Subgroup G)]
      (T : Subgroup G)) false) 1)
    (hIC : I ≤ centralizer (A : Set (Reduction.G₀ ![H, sourceResidual M Mc ⊔
      (T : Subgroup G)] (T : Subgroup G))))
    (hIcard : 4 < Nat.card I)
    (hZcard : Nat.card (Z (Reduction.reducedFamily ![H, sourceResidual M Mc ⊔
      (T : Subgroup G)] (T : Subgroup G))
      (base (Reduction.reducedFamily ![H, sourceResidual M Mc ⊔ (T : Subgroup G)]
      (T : Subgroup G)) false)) = 2) : False := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let y := base F false
  obtain ⟨hV,_⟩ := source_quintic_dgs_five_centralizer_base
    hG T hempty hM hu hmany hcard e H hH hi A hA hAc
  have hIZ : I ≤ Z F y := by
    rw [←hV]
    exact le_inf hI hIC
  have hIle : Nat.card I ≤ Nat.card (Z F y) := card_le_of_le hIZ
  rw [hZcard] at hIle
  omega

end CFSG.Quasithin.Chapter14.Section06
