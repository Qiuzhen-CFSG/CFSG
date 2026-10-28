module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Roots
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.OddSubgroups

/-!
# Odd Sylow commutators in the actual centralizer circles

The centralizer of w normalizes its distinguished circle. When t is a
distinguished involution commuting with w, it lies in that circle, hence
[C_P(w),t] lies there. An odd p-subgroup in an actual linear circle is cyclic.
The terminal containment likewise places any full t-commutator centralizing
w in D∩C_G(w)°, preserving the original ambient subgroups.

Source: GLS IV, Chapter 2, Proposition 16.5.
-/

namespace BenderSuzuki.ZD.Source16OddResidual
open Subgroup Theory.GroupTheory OddInvolutionFrattini
open scoped IsMulCommutative
variable {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}

/-- The fixed-centralizer commutator lies in its literal distinguished circle. -/
public theorem rw_le_circle (h : IsProductDisconnected Z M)
    (P : Subgroup G) {t w : G} (ht : t∈Z) (htw : Commute t w) :
    Rw P t w ≤ localCircleIn Z (centralizer ({w} : Set G)) := by
  have htL : t ∈ localCircleIn Z (centralizer ({w} : Set G)) := by
    rw [localCircleIn_eq_closure]
    exact subset_closure ⟨ht,mem_centralizer_singleton_iff.mpr htw.eq⟩
  have hn : P ⊓ centralizer ({w} : Set G) ≤
      normalizer (localCircleIn Z (centralizer ({w} : Set G))) :=
    inf_le_right.trans (source16_localCircleIn_normalizer h _)
  exact (commutator_mono le_rfl (zpowers_le.mpr htL)).trans
    (le_normalizer_iff_commutator_le_right.mp hn)

/-- The actual linear model makes every literal odd-primary R_w cyclic. -/
public theorem rw_cyclic_of_linear_circle [Finite G]
    (h : IsProductDisconnected Z M) (P A : Subgroup G) [IsMulCommutative A]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (hp : p≠2)
    (hAP : A≤normalizer P) {t w : G} (htA : t∈A) (hwA : w∈A)
    (ht : t∈Z) {n : ℕ}
    (e : localCircle Z (centralizer ({w} : Set G)) ≃* MatrixGroups.PSL2BinaryMatrixGroup n) :
    IsCyclic (Rw P t w) := by
  have htw : Commute t w := Subtype.ext_iff.mp (mul_comm (⟨t,htA⟩:A) ⟨w,hwA⟩)
  let F := centralizer ({w} : Set G)
  let f : localCircle Z F ≃* localCircleIn Z F :=
    (localCircle Z F).equivMapOfInjective F.subtype F.subtype_injective
  have hRwP : Rw P t w≤P := (rw_le P t w).trans (r_le P (hAP htA))
  have hRwp : IsPGroup p (Rw P t w) := hP.of_injective (inclusion hRwP) (inclusion_injective hRwP)
  exact RankOneModelGeometry.pSubgroup_isCyclic_of_linear_model _ (f.symm.trans e) _
    (rw_le_circle h P ht htw) hp hRwp

/-- The full commutator condition forces a centralized subgroup into the
actual circle; no old distinguished mark is asserted to centralize w. -/
public theorem full_commutator_le_circle (h : IsProductDisconnected Z M)
    (R : Subgroup G) {t w : G} (ht : t∈Z) (htw : Commute t w)
    (hRw : R≤centralizer ({w} : Set G)) (hR : ⁅R,zpowers t⁆=R) :
    R≤localCircleIn Z (centralizer ({w} : Set G)) := by
  rw [←hR]
  exact (commutator_mono (le_inf le_rfl hRw) le_rfl).trans (rw_le_circle h R ht htw)

/-- The final source contradiction uses cyclicity of the actual D∩circle.
Its earlier-source producer may use a changed distinguished base point. -/
public theorem false_of_full_commutator_centralized
    (h : IsProductDisconnected Z M) (R : Subgroup G) {t w : G}
    (ht : t∈Z) (htw : Commute t w)
    (hRD : R≤residualPairStabilizer M t) (hRw : R≤centralizer ({w} : Set G))
    (hR : ⁅R,zpowers t⁆=R) (hn : ¬IsCyclic R)
    (hc : IsCyclic (residualPairStabilizer M t ⊓
      localCircleIn Z (centralizer ({w} : Set G)) : Subgroup G)) : False := by
  let := hc
  exact hn (isCyclic_of_injective
    (inclusion (le_inf hRD (full_commutator_le_circle h R ht htw hRw hR)))
    (inclusion_injective _))

end BenderSuzuki.ZD.Source16OddResidual
