module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Thompson.Setup
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Thompson.Offenders
public import Stellmacher.MaxElementarySectionControl
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# The orthogonal Thompson comparison after 13.6.23

Put X = O^{3′}(C_K(z)), R = O₂(XT_v), and Q = O₂(KT_v), as
embedded subgroups of the original group. A chosen marking identifies the
actual plus actor with S₈, XT_v with the four-block stabilizer, and the
literal section U_K/C_{U_K}(K), U_K = [W_K,K], with its natural module.

The proved two-group kernel transports R to V₄ × V₄. There are no
nontrivial offenders in that subgroup, so the maximum-elementary counting
argument and the section codimension inequality give J(R) ≤ ker(+) ≤ Q.
The genuine common Sylow subgroup gives Q ≤ R, and the intermediate
Thompson theorem proves J(R) = J(Q). No central extension is split and
no Thompson containment or normality is an assumption.

This is a conditional source comparison: the independent marked-local-action
and source-selection constructions must supply `Marking` and `EarlierData`.
The final consumers apply the comparison to the literal residual and the
13.6.16(1) vanishing, including residual invariance from 13.6.23(1).

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, concluding
paragraph after 13.6.23, printed p.933; B.3.2, printed pp.83–85.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Stellmacher Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Thompson
open ComponentSelection
open Theory.SpecificGroups.SymmetricEight
variable {G : Type*} [Group G] [Finite G]
    {K L T : Subgroup G} {z v : G}

/-- The independently constructed orthogonal marking: its two invariant
subspaces are literally U_K and C_{U_K}(K), and its actor map is the plus
map. The parabolic image is the actual X T_v, not an unrelated subgroup. -/
structure Marking (d : EarlierData K L T z v) where
  model : Gplus K L T z v d.normalizeL d.fixSeed ≃* Equiv.Perm (Fin 8)
  upper : Subrepresentation (d.modelRepresentation model)
  lower : Subrepresentation (d.modelRepresentation model)
  upper_mem : ∀ w : Additive d.internalW, w ∈ upper.toSubmodule ↔
    ((w.toMul : plusActor K L T v) : G) ∈ ⁅WK K L T z v, K⁆
  lower_mem : ∀ w : Additive d.internalW, w ∈ lower.toSubmodule ↔
    ((w.toMul : plusActor K L T v) : G) ∈
      ⁅WK K L T z v, K⁆ ⊓ centralizer (K : Set G)
  sectionEquiv : (upper.toSubmodule ⧸
      (sectionLower (d.modelRepresentation model) lower upper).toSubmodule)
      ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8)
  equivariant : ∀ g w, sectionEquiv
      (sectionRepresentation (d.modelRepresentation model) lower upper g w) =
    BinaryPermutation.naturalRepresentation (Fin 8) g (sectionEquiv w)
  local_image : ((Source.orthogonalResidual K z ⊔ Tv T v).subgroupOf
      (plusActor K L T v)).map (d.modelMap model) = A6ShadowTwoLocals.fourStabilizer

variable (d : EarlierData K L T z v)
include d

omit d [Finite G] in
theorem local_le_actor : Source.orthogonalResidual K z ⊔ Tv T v ≤ plusActor K L T v := by
  apply sup_le _ le_sup_right
  exact (map_subtype_le (primeToResidual 3 (K ⊓ Gv z : Subgroup G))).trans
    (inf_le_left.trans (K_le_plusActor K L T v))

omit [Finite G] in
/-- The reverse core containment uses the genuine common Sylow subgroup. -/
theorem EarlierData.componentCore_le_localCore :
    (K ⊔ Tv T v).pCoreIn 2 ≤ (Source.orthogonalResidual K z ⊔ Tv T v).pCoreIn 2 := by
  have hs := d.tvSylow.restrict (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)
    (sup_le d.component.1.1 inf_le_right)
  obtain ⟨P, hP⟩ := hs
  have hQT : (K ⊔ Tv T v).pCoreIn 2 ≤ Tv T v := by
    exact (pCoreIn_le_sylow _ P).trans hP.le
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) (hQT.trans le_sup_right)
  have hloc : Source.orthogonalResidual K z ⊔ Tv T v ≤ K ⊔ Tv T v := by
    rw [← d.actor_eq]
    exact local_le_actor
  exact hloc.trans ((K ⊔ Tv T v).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

theorem EarlierData.internalW_le_localCore :
    d.internalW ≤ ((Source.orthogonalResidual K z ⊔ Tv T v).subgroupOf
      (plusActor K L T v)).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 d.internalW)
  · intro w hw
    exact mem_sup_right (d.WK_le_Tv hw)
  · exact le_normalizer_of_normal

/-- The marking's lower space is the actual fixed subgroup inside its upper
space. This also rules out silently replacing the section by a complement. -/
theorem Marking.lower_le_upper (m : Marking d) : m.lower ≤ m.upper := by
  intro w hw
  exact (m.upper_mem w).mpr ((m.lower_mem w).mp hw).1

/-- The actual R_v image, obtained by transporting the two-core through
the proved two-group kernel. -/
theorem EarlierData.localCore_image (m : Marking d) :
    (((Source.orthogonalResidual K z ⊔ Tv T v).subgroupOf
      (plusActor K L T v)).pCoreIn 2).map (d.modelMap m.model) =
        FourBlockCoreAction.kleinGroup := by
  rw [map_pCoreIn_of_ker_isPGroup (d.modelMap m.model)
    (d.modelMap_kernel_isPGroup m.model), m.local_image,
    FourBlockCoreAction.fourStabilizer_pCoreIn]

/-- B.3.2 applied to the marked central section forces every maximum
elementary subgroup of R_v into the true plus kernel. -/
theorem EarlierData.localCore_maxJ_le_kernel (m : Marking d) :
    elementaryAbelianMaxJ (((Source.orthogonalResidual K z ⊔ Tv T v).subgroupOf
      (plusActor K L T v)).pCoreIn 2) ≤ (d.modelMap m.model).ker := by
  apply maxJ_le_ker_of_nonoffending_section d.internalW (d.modelMap m.model)
    (d.modelMap_surjective m.model) (d.modelMap_ker m.model) _
    d.internalW_le_localCore m.lower m.upper
    (BinaryPermutation.naturalRepresentation (Fin 8)) m.sectionEquiv m.equivariant
  intro A hA
  rw [d.localCore_image m] at hA
  exact OrthogonalOffenders.not_isOffender_natural hA

/-- The literal comparison used in the paragraph after 13.6.23. No
maximum-elementary placement or Thompson normality is an input. -/
theorem EarlierData.thompson_eq (m : Marking d) :
    elementaryAbelianMaxJ ((Source.orthogonalResidual K z ⊔ Tv T v).pCoreIn 2) =
      elementaryAbelianMaxJ ((K ⊔ Tv T v).pCoreIn 2) := by
  let H := plusActor K L T v
  let P := (Source.orthogonalResidual K z ⊔ Tv T v).subgroupOf H
  have hmap : (P.pCoreIn 2).map H.subtype =
      (Source.orthogonalResidual K z ⊔ Tv T v).pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup H.subtype
      (IsPGroup.ker_isPGroup_of_injective H.subtype_injective),
      map_subgroupOf_eq_of_le local_le_actor]
  have hJ : elementaryAbelianMaxJ ((Source.orthogonalResidual K z ⊔ Tv T v).pCoreIn 2) ≤
      (K ⊔ Tv T v).pCoreIn 2 := by
    rw [← hmap, elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      ← d.actor_eq]
    exact map_mono ((d.localCore_maxJ_le_kernel m).trans
      (le_sSup ⟨inferInstance, d.modelMap_kernel_isPGroup m.model⟩))
  exact (elementaryAbelianMaxJ_eq_of_intermediate _ _ hJ d.componentCore_le_localCore).symm

omit d

/-- The proved comparison supplies the final Thompson contradiction with
the actual residual and the explicit 13.6.16(1) vanishing. -/
theorem false_of_marking (S : Sylow 2 G)
    (d : EarlierData K L (S : Subgroup G) z v) (m : Marking d)
    (hvS : v ∈ S) (hv : v ≠ 1)
    (hTX : (S : Subgroup G) ≤ normalizer (Source.orthogonalResidual K z : Set G))
    (hidx : (Tv (S : Subgroup G) v).relIndex (S : Subgroup G) = 2)
    (h16 : (K ⊔ (S : Subgroup G)).pCoreIn 2 = ⊥) : False := by
  apply Source.false_of_orthogonal_thompson_comparison S v K
    (Source.orthogonalResidual K z) hvS hv _ hTX hidx (d.thompson_eq m) h16
  exact (map_subtype_le _).trans (inf_le_left.trans d.component.1.1)

/-- Source 13.6.23(1) and the actual T-invariant plane discharge residual
invariance in the final consumer. The module/centralizer marking remains
the separately constructed input. -/
theorem false_of_residual_and_plane_marking (S : Sylow 2 G)
    (d : EarlierData K L (S : Subgroup G) z v) (m : Marking d)
    (hres : K = (primeToResidual 3 (Gv v)).map (Gv v).subtype)
    (V₂ : Subgroup G) (hV₂ : V₂ = zpowers z ⊔ zpowers v)
    (hSV₂ : (S : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hvS : v ∈ S) (hv : v ≠ 1)
    (hidx : (Tv (S : Subgroup G) v).relIndex (S : Subgroup G) = 2)
    (h16 : (K ⊔ (S : Subgroup G)).pCoreIn 2 = ⊥) : False :=
  false_of_marking S d m hvS hv
    (Source.normalizes_orthogonalResidual K V₂ (S : Subgroup G) z v hres hV₂ hSV₂)
    hidx h16

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Thompson
