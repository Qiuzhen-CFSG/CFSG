module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.ModelFacts
public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.HigmanSims.Orders
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.HigmanSims.SylowCenter
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.HigmanSims.PermutationFusion

/-!
# HS Sylow-center embeddings for the A₆ and A₈ pairs

In the full degree-100 HS carrier, the required alternating involutions fuse
to the generator of the whole center of the certified Sylow two-subgroup.
Conjugating that Sylow subgroup and transporting through the supplied HS
isomorphism realizes the given order-two subgroup exactly in the ambient G.
The automorphism Sylow orders are strictly smaller than the HS Sylow order.

Only L ≤ K is needed from the exclusion setup for this model calculation.
No earlier centralizer table or extra fusion premise is assumed.

Source: Aschbacher–Smith, 16.1.7(h) and the proof of 16.3.4,
printed pp.1172 and 1178 / PDF pp.1189 and 1195.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup ClassificationModels
open Sporadic.LeechRelated.HS.EvenLocalCandidates
variable {G : Type*} [Group G] [Finite G] {L K : Subgroup G}

private theorem lifting_of_fusion (hLK : L ≤ K) (eK : K ≃* SporadicName.hs.Carrier)
    (hf : ∀ (P : Sylow 2 L) (x : P), x ∈ center P → orderOf (x : L) = 2 →
      IsConj e0 (eK (inclusion hLK x))) : InvolutionCenterLifting L K := by
  intro P V hV hcV
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 (hcV ▸ dvd_rfl)
  have hxG : orderOf (x : G) = 2 :=
    (orderOf_injective V.subtype V.subtype_injective x).trans hx
  have hgen : zpowers (x : G) = V :=
    eq_of_le_of_card_ge (zpowers_le.mpr x.property) (by rw [Nat.card_zpowers, hxG, hcV])
  obtain ⟨l, hl, hel⟩ := hV x.property
  obtain ⟨p, hp, hep⟩ := hl
  have he : ((p : L) : G) = (x : G) :=
    (congrArg (fun a : L => (a : G)) hep).trans hel
  have hpord : orderOf (p : L) = 2 :=
    (orderOf_injective L.subtype L.subtype_injective (p : L)).symm.trans
      ((congrArg orderOf he).trans hxG)
  have h := hs_center_embedding_of_isConj K eK (inclusion hLK p) (hf P p hp hpord)
  change SylowCenterEmbedding K (zpowers ((p : L) : G)) at h
  rwa [he, hgen] at h

/-- The order-two subgroups in embedded A₆ Sylow centers are full HS Sylow centers. -/
theorem hs_involutionCenterLifting_a6 (hLK : L ≤ K)
    (eK : K ≃* SporadicName.hs.Carrier) (eL : L ≃* alternatingGroup (Fin 6)) :
    InvolutionCenterLifting L K := by
  apply lifting_of_fusion hLK eK
  intro P x _ hx
  let f := eK.toMonoidHom.comp ((inclusion hLK).comp eL.symm.toMonoidHom)
  have hf : Function.Injective f :=
    eK.injective.comp ((inclusion_injective hLK).comp eL.symm.injective)
  have ho : orderOf (eL x) = 2 := (eL.orderOf_eq x).trans hx
  have h := HSPermutationFusion.a6_involution_isConj f hf (eL x) ho
  change IsConj e0 (eK (inclusion hLK (eL.symm (eL x)))) at h
  rwa [eL.symm_apply_apply] at h

/-- The order-two subgroups in embedded A₈ Sylow centers are full HS Sylow centers. -/
theorem hs_involutionCenterLifting_a8 (hLK : L ≤ K)
    (eK : K ≃* SporadicName.hs.Carrier) (eL : L ≃* alternatingGroup (Fin 8)) :
    InvolutionCenterLifting L K := by
  apply lifting_of_fusion hLK eK
  intro P x hx ho
  let Q : Sylow 2 (alternatingGroup (Fin 8)) :=
    P.mapSurjective (f := eL.toMonoidHom) eL.surjective
  let y : Q := ⟨eL x, mem_map_of_mem eL.toMonoidHom x.property⟩
  have hy : y ∈ center Q := by
    apply mem_center_iff.mpr
    intro q
    obtain ⟨a, ha, he⟩ := q.property
    apply Subtype.ext
    change (q : alternatingGroup (Fin 8)) * eL x = eL x * (q : alternatingGroup (Fin 8))
    change eL a = (q : alternatingGroup (Fin 8)) at he
    rw [← he, ← map_mul, ← map_mul]
    exact congrArg eL (congrArg Subtype.val (mem_center_iff.mp hx ⟨a, ha⟩))
  let f := eK.toMonoidHom.comp ((inclusion hLK).comp eL.symm.toMonoidHom)
  have hf : Function.Injective f :=
    eK.injective.comp ((inclusion_injective hLK).comp eL.symm.injective)
  have hyord : orderOf (y : alternatingGroup (Fin 8)) = 2 := (eL.orderOf_eq x).trans ho
  have h := HSPermutationFusion.a8_sylow_involution_isConj f hf Q y hy hyord
  change IsConj e0 (eK (inclusion hLK (eL.symm (eL x)))) at h
  rwa [eL.symm_apply_apply] at h

/-- Both intrinsic HS model facts, retaining the actual full group isomorphisms. -/
theorem hs_model_facts_of_le (hLK : L ≤ K) (eK : K ≃* SporadicName.hs.Carrier)
    (hL : Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (L ≃* alternatingGroup (Fin 8))) :
    InvolutionCenterLifting L K ∧ SylowOrderGap L K := by
  rcases hL with hL | hL
  · obtain ⟨eL⟩ := hL
    exact ⟨hs_involutionCenterLifting_a6 hLK eK eL, hs_sylowOrderGap_a6 eK eL⟩
  · obtain ⟨eL⟩ := hL
    exact ⟨hs_involutionCenterLifting_a8 hLK eK eL, hs_sylowOrderGap_a8 eK eL⟩

/-- The complete HS branch of the model calculation used by 16.3.4. -/
theorem hs_model_facts {T : Sylow 2 G} {z t i : G}
    (h : ExclusionSetup T z L K t i) (eK : K ≃* SporadicName.hs.Carrier)
    (hL : Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (L ≃* alternatingGroup (Fin 8))) :
    InvolutionCenterLifting L K ∧ SylowOrderGap L K :=
  hs_model_facts_of_le (h.componentL.1.trans inf_le_left) eK hL

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
