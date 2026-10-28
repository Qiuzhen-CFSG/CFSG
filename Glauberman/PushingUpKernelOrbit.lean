module
public import Glauberman.PushingUpOmegaSplitting
public import Glauberman.PushingUpAbelianKernelIntersection
public import Theory.GroupTheory.RankOneInvariantKernelQuotient

/-!
# The original selected-actor application of Niles Lemma7.6

The literal maximal invariant normal kernel lies below O2(H). For the
maximum abelian actor chosen by Lemma7.5, its fixed index on the enlarged
central omega layer is at most four. A generating conjugate pair and the
natural-module index sixteen force the enlarged layer to split over the
original layer by fixed points. Thus their moved subgroups agree, and the
orbit-centralizer theorem identifies the kernel with the cyclic intersection
of the original two-core. The original H,S,K and all inclusion maps are
preserved. Natural-module index and moved-centralizer facts are supplied
separately by the source2.9 recognition.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma7.6, pp.61–62.
-/

public section
open Subgroup NilesRankOneKernel
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

/-- Niles7.6 for the literal selected A and its chosen conjugate supplement. -/
theorem pushingUp_kernel_orbit_of_selected_actor
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (α : MulAut S) (A : Subgroup H)
    (hA : A ∈ thompsonAbelianSubgroups (S : Subgroup H))
    (hVN : omegaCenterIn (pCore 2 H) ≤
      (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype)
    (hinter : A ⊓ pCore 2 H = A ⊓
      (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype)
    (g : H)
    (hgen : (A ⊔ A.map (MulAut.conj g).toMonoidHom) ⊔ pCore 2 H = ⊤)
    (hV : 16 ≤ (centralizer
      ((A ⊔ A.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H)).relIndex
        (omegaCenterIn (pCore 2 H)))
    (hC : (S : Subgroup H) ⊓ centralizer
      ((⁅omegaCenterIn (pCore 2 H),A ⊔ A.map (MulAut.conj g).toMonoidHom⁆ : Subgroup H) : Set H) =
        pCore 2 H) :
    invariantNormalKernel (S : Subgroup H) α =
      ⨅ n : ℤ, ((pCore 2 H).subgroupOf (S : Subgroup H)).map ((α ^ n).toMonoidHom) := by
  let N := invariantNormalKernel (S : Subgroup H) α
  let Z := N.map (S : Subgroup H).subtype
  let L := A ⊔ A.map (MulAut.conj g).toMonoidHom
  have hNS : Z ≤ (S : Subgroup H) := map_subtype_le _
  have hNQ : Z ≤ pCore 2 H := by
    exact le_sSup ⟨inferInstance,S.isPGroup'.of_injective
      (inclusion hNS) (inclusion_injective hNS)⟩
  have hQS : pCore 2 H ≤ (S : Subgroup H) := pCore_isPGroup.le_sylow_of_normal S
  have hidx : (pCore 2 H).relIndex A ≤ 4 := by
    have hs : (pCore 2 H).relIndex (S : Subgroup H) = 4 := by
      rw [relIndex,index_eq_card]
      exact (Theory.SpecificGroups.SL2.sylow_twoCore_quotient_elementary_four hF S hu K e).2
    exact (relIndex_le_of_le_right hA.1 index_ne_zero_of_finite).trans_eq hs
  have hsplit : omegaCenterIn Z = omegaCenterIn (pCore 2 H) ⊔
      (omegaCenterIn Z ⊓ centralizer (L : Set H)) :=
    omega_eq_coreOmega_sup_fixed (S : Subgroup H) (pCore 2 H) Z A
      hA hNS hNQ hVN hinter hidx g hV
  have hWnormal : (omegaCenterIn Z).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    calc
      ⊤ = normalizer (Z : Set H) := (Subgroup.normalizer_eq_top Z).symm
      _ ≤ normalizer (omegaCenterIn Z : Set H) := normalizer_le_normalizer_omegaCenterIn Z
  have hcomm : ⁅omegaCenterIn Z,L⁆ = ⁅omegaCenterIn (pCore 2 H),L⁆ :=
    commutator_eq_of_abelian_fixed_splitting _ _ _ inferInstance le_normalizer_of_normal hsplit
  have hSL : (S : Subgroup H) ⊔ L = ⊤ := by
    apply top_le_iff.mp
    rw [← hgen]
    exact sup_le le_sup_right (hQS.trans le_sup_left)
  have hmapnormal : (((pCore 2 H).subgroupOf (S : Subgroup H)).map
      (S : Subgroup H).subtype).Normal := by
    rw [map_subgroupOf_eq_of_le hQS]
    infer_instance
  apply invariantKernel_eq_orbit_inf_of_omega_commutator (S : Subgroup H) α
    ((pCore 2 H).subgroupOf (S : Subgroup H)) L hSL
  apply map_injective (S : Subgroup H).subtype_injective
  rw [centralizer_map_subtype,map_subgroupOf_eq_of_le hQS]
  have hm : ⁅(omegaCenterIn N).map (S : Subgroup H).subtype,L⁆ ≤ (S : Subgroup H) := by
    rw [omegaCenterIn_map_injective _ (S : Subgroup H).subtype_injective]
    exact (commutator_le_left _ _).trans
      (fun x hx => hNS ((mem_omegaCenterIn_iff Z x).mp hx).1)
  rw [map_subgroupOf_eq_of_le hm,omegaCenterIn_map_injective _
    (S : Subgroup H).subtype_injective,hcomm]
  exact hC

end Glauberman
