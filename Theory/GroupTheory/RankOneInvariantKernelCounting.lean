module
public import Theory.GroupTheory.RankOneInvariantKernelOmega
public import Theory.GroupTheory.TwoLayerFixedIndex
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.SmallMoverFamily

/-!
# The invariant-kernel orbit formula from sharp fixed indices

The smaller core omega and larger invariant-kernel omega have matching
fixed indices under a supplement L. Their full fixed subgroups give
W=V C_W(L), hence [W,L]=[V,L]. Reducedness preserves the centralizer of
this moved subgroup, and the actual cyclic-orbit centralizer argument
identifies N-alpha with the intersection of all alpha-translates of O2.
The lower and upper bounds are explicit numerical inputs, discharged for
the original SL2 group by its module degree and maximum abelian arguments.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 7.6,
printed pp.61-62, assertion (2) and its final paragraph.
-/

public section
open Subgroup Theory.GroupTheory
namespace NilesRankOneKernel
variable {H : Type*} [Group H] [Finite H]

private theorem split_of_fixed_indices
    (V W L : Subgroup H) [IsMulCommutative W]
    (hVW : V ≤ W) (k : ℕ)
    (hlow : k ≤ (centralizer (L : Set H)).relIndex V)
    (hupp : (centralizer (L : Set H)).relIndex W ≤ k) :
    V ⊔ (W ⊓ centralizer (L : Set H)) = W := by
  let D := (centralizer (L : Set H)).subgroupOf W
  let : D.Normal := normal_of_isMulCommutative D
  have hV : V.subgroupOf W ≤ (⊤ : Subgroup W) := le_top
  have hlo : k ≤ D.relIndex (V.subgroupOf W) := by
    rwa [relIndex_subgroupOf hVW]
  have hup : D.relIndex (⊤ : Subgroup W) ≤ k := by
    rw [relIndex_top_right]
    exact hupp
  have he := sup_eq_of_fixed_indices (⊤ : Subgroup W) (V.subgroupOf W) D hV le_top k hlo hup
  have hm := congrArg (Subgroup.map W.subtype) he
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVW,←MonoidHom.range_eq_map,range_subtype] at hm
  have hD : D.map W.subtype = W ⊓ centralizer (L : Set H) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨y.property,hy⟩
    · intro hx; exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  rwa [hD] at hm

/-- The sharp count on the literal larger omega discharges the commutator
centralizer premise of the invariant-kernel orbit theorem. -/
theorem invariantKernel_eq_orbit_inf_of_fixed_indices
    (S : Sylow 2 H) (α : MulAut S)
    (hV : omegaCenterIn (pCore 2 H) ≤
      (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype)
    (hC : centralizer (omegaCenterIn (pCore 2 H) : Set H) = pCore 2 H)
    (hred : IsPReduced 2 (omegaCenterIn (pCore 2 H)))
    (L : Subgroup H) (hgen : L ⊔ pCore 2 H = ⊤)
    (k : ℕ) (hlow : k ≤ (centralizer (L : Set H)).relIndex (omegaCenterIn (pCore 2 H)))
    (hupp : (centralizer (L : Set H)).relIndex
      (omegaCenterIn ((invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype)) ≤ k) :
    invariantNormalKernel (S : Subgroup H) α =
      ⨅ m : ℤ, ((pCore 2 H).subgroupOf (S : Subgroup H)).map ((α ^ m).toMonoidHom) := by
  let V := omegaCenterIn (pCore 2 H)
  let N := invariantNormalKernel (S : Subgroup H) α
  let W := omegaCenterIn (N.map (S : Subgroup H).subtype)
  obtain ⟨hNQ,hVW,hWn,_⟩ := invariantKernel_omega_properties S α hV hC.le
  let _ := hred.normal
  let _ := hWn
  have hWsplit : V ⊔ (W ⊓ centralizer (L : Set H)) = W :=
    split_of_fixed_indices V W L hVW k hlow hupp
  have hVL : L ≤ normalizer (V : Set H) := le_normalizer_of_normal
  have hcomm : ⁅W,L⁆ = ⁅V,L⁆ := by
    apply le_antisymm ?_ (commutator_mono hVW le_rfl)
    change ⁅W,L⁆ ≤ ⁅V,L⁆
    rw [←hWsplit]
    apply commutator_sup_le_of_relative_normal W V (W ⊓ centralizer (L : Set H)) L ⁅V,L⁆
    · exact (W.le_centralizer.trans (centralizer_le
        ((le_normalizer_iff_commutator_le_left.mp hVL).trans hVW))).trans
          (centralizer_le_normalizer _)
    · exact hVW
    · exact inf_le_left
    · exact le_rfl
    · exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le
  have hQV : pCore 2 H ≤ centralizer (V : Set H) := hC.ge
  have hcommTop : ⁅V,L⁆ = ⁅V,(⊤ : Subgroup H)⁆ :=
    commutator_eq_of_centralizing_sup (sup_comm L _ ▸ hgen) hQV hVL
  have hcent : centralizer ((⁅W,L⁆ : Subgroup H) : Set H) = pCore 2 H := by
    rw [hcomm,hcommTop]
    exact (hred.centralizer_commutator_eq V (QuotientGroup.mk' (centralizer (V : Set H)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) ⊤
      (by rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)).trans hC
  have hQS : pCore 2 H ≤ (S : Subgroup H) := pCore_isPGroup.le_sylow_of_normal S
  have hSL : (S : Subgroup H) ⊔ L = ⊤ := top_unique (by
    rw [←hgen]; exact sup_le le_sup_right (hQS.trans le_sup_left))
  have hWS : W ≤ (S : Subgroup H) := by
    intro w hw
    exact map_subtype_le _ (((mem_omegaCenterIn_iff _ _).mp hw).1)
  have hMS : ⁅W,L⁆ ≤ (S : Subgroup H) := (commutator_le_left _ _).trans hWS
  let : (((pCore 2 H).subgroupOf (S : Subgroup H)).map (S : Subgroup H).subtype).Normal := by
    rw [map_subgroupOf_eq_of_le hQS]
    infer_instance
  apply invariantKernel_eq_orbit_inf_of_omega_commutator (S : Subgroup H) α
    ((pCore 2 H).subgroupOf (S : Subgroup H)) L hSL
  rw [omegaCenterIn_map_injective _ (S : Subgroup H).subtype_injective]
  apply Subgroup.map_injective (f := (S : Subgroup H).subtype) (S : Subgroup H).subtype_injective
  rw [centralizer_map_subtype,map_subgroupOf_eq_of_le hMS,hcent,
    map_subgroupOf_eq_of_le hQS,inf_eq_right.mpr hQS]

end NilesRankOneKernel
