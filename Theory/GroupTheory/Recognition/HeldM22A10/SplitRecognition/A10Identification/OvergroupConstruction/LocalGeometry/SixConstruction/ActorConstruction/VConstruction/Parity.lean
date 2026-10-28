module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.SectionActions
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Parity of Held's marked extension

The perfect normal A6 is exactly the derived subgroup of its cyclic extension
by mu-prime. Consequently every supplied S6 equivalence takes this A6 to the
even permutations. Mu-prime lies outside A6 because it does not centralize
lambda. The extension centralizes mu and contains xi.

The derived-subgroup argument follows the existing `SixParity` proof, here
using only `MarkedSection`, without assuming either actor. Source: D. Held,
Illinois J. Math. 13 (1969), 224--240, DOI 10.1215/ijm/1256053756, Lemma 4.2.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
namespace VConstruction
variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : NoncentralAnalysis.AlternatingSixSection
    (centralizer ({D.a10NoncentralInvolution e} : Set G))) (m : MarkedSection D e s)

private theorem marked_commutator :
    ⁅s.ambientSubgroup ⊔ zpowers (mu' D e), s.ambientSubgroup ⊔ zpowers (mu' D e)⁆ =
      s.ambientSubgroup := by
  let := s.ambientSubgroup_isPerfect
  let X := s.ambientSubgroup ⊔ zpowers (mu' D e)
  have hA : s.ambientSubgroup ≤ X := le_sup_left
  have hn : zpowers (mu' D e) ≤ normalizer (s.ambientSubgroup : Set G) :=
    zpowers_le.mpr (mu'_normalizes_section D e s)
  let : (s.ambientSubgroup.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hA).mpr (sup_le s.ambientSubgroup.le_normalizer hn)
  have htop : s.ambientSubgroup.subgroupOf X ⊔ (zpowers (mu' D e)).subgroupOf X = ⊤ :=
    (codisjoint_subgroupOf_sup s.ambientSubgroup (zpowers (mu' D e))).eq_top
  have hcomm : IsMulCommutative ((zpowers (mu' D e)).subgroupOf X) := inferInstance
  have hder : commutator X ≤ s.ambientSubgroup.subgroupOf X :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top htop hcomm
  apply le_antisymm
  · simpa only [map_subtype_commutator, map_subgroupOf_eq_of_le hA] using
      map_mono (f := X.subtype) hder
  · exact s.ambientSubgroup.commutator_eq_self.symm.le.trans (commutator_mono hA hA)

public theorem marked_even_subgroup :
    (alternatingGroup (Fin 6)).comap m.symmetricEquiv.toMonoidHom =
      s.ambientSubgroup.subgroupOf (s.ambientSubgroup ⊔ zpowers (mu' D e)) := by
  have hmap : (commutator (s.ambientSubgroup ⊔ zpowers (mu' D e) : Subgroup G)).map
      m.symmetricEquiv.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr m.symmetricEquiv.surjective,
      ← _root_.commutator_def, alternatingGroup.commutator_perm_eq (by simp)]
  rw [← hmap, comap_map_eq_self_of_injective m.symmetricEquiv.injective]
  apply map_subtype_inj.mp
  rw [map_subtype_commutator, map_subgroupOf_eq_of_le le_sup_left]
  exact marked_commutator D e s

public theorem marked_even_iff
    (x : (s.ambientSubgroup ⊔ zpowers (mu' D e) : Subgroup G)) :
    Perm.sign (m.symmetricEquiv x) = 1 ↔ (x : G) ∈ s.ambientSubgroup := by
  change x ∈ (alternatingGroup (Fin 6)).comap m.symmetricEquiv.toMonoidHom ↔ _
  rw [marked_even_subgroup D e s m]
  rfl

include m in
public theorem marked_mu'_not_mem : mu' D e ∉ s.ambientSubgroup := by
  intro h
  have hc := mem_centralizer_iff.mp (m.centralizes h) (lam D e) (by simp)
  have hn : modelElement 6 * modelElement 2 ≠ modelElement 2 * modelElement 6 := by decide +kernel
  apply hn
  apply D.a10ModelEmbedding_injective e
  simpa only [element, map_mul] using hc

public theorem extension_le_centralizer :
    s.ambientSubgroup ⊔ zpowers (mu' D e) ≤ centralizer ({mu D e} : Set G) :=
  sup_le s.ambientSubgroup_le
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (mu_commute_mu' D e).symm.eq))

include m in
public theorem marked_xi_mem_extension :
    xi D e ∈ s.ambientSubgroup ⊔ zpowers (mu' D e) := by
  have hd : mu' D e ∈ s.ambientSubgroup ⊔ zpowers (mu' D e) :=
    (show zpowers (mu' D e) ≤ _ from le_sup_right) (mem_zpowers _)
  have hc : mu' D e * xi D e ∈ s.ambientSubgroup ⊔ zpowers (mu' D e) :=
    (show s.ambientSubgroup ≤ _ from le_sup_left) m.mu'_xi_mem
  simpa only [inv_mul_cancel_left] using mul_mem (inv_mem hd) hc
end VConstruction
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
