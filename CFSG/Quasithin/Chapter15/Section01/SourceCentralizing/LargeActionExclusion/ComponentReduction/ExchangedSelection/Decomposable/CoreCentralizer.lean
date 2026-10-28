module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.Thompson
public import Theory.Representation.BinaryOffender.PrimeIndexFixedKernel
public import Theory.GroupTheory.PResidual.CentralizingTwoGroup
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Transport

/-!
# The marked centralizer inside the decomposable factor product

The actual Sylow intersection in the first dihedral factor has prime index.
Its Thompson four-space is not fixed by that factor, so this intersection
is exactly its pointwise kernel. The opposite factor fixes that space;
thus the kernel in Jhat is the product of the first Sylow intersection
and the opposite dihedral factor. Its two-residual is precisely the latter's
original odd kernel, with the same prime three or five.

This identifies both original sixteen-element residual supports and lifts
the calculation through the literal preimage of Jhat in M. The faithful
quotient kernel is C_M(V). Extending this calculation from the factor-product
centralizer to the full C_M(Z₁) remains a separate source obligation.

Source: Aschbacher--Smith 15.1.16(a)--18, printed pp.1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_card_two {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) {p : ℕ} (hp : Odd p) (hc : Nat.card D = 2*p) : Nat.card S = 2 := by
  have hd : 2 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) (by simp [hc])
  obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card S) p := by
    rw [hk]
    exact hp.coprime_two_left.pow_left k
  have hb : Nat.card S ∣ 2 := hcop.dvd_of_dvd_mul_right (hc ▸ card_subgroup_dvd_card _)
  exact Nat.dvd_antisymm hb hd

/-- The pointwise kernel inside the original two-factor actor has residual
exactly the opposite marked odd kernel. -/
theorem ThompsonPair.core_centralizer {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    let ρ := imageRepresentation M V hn
    let S := ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let C := subspaceKernel ρ W (Jhat ρ)
    C = (S ⊓ (c.ambientFactor d s.first).actor) ⊔ (c.ambientFactor d s.second).actor ∧
    (pResidual 2 C).map C.subtype =
      ((s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap) := by
  classical
  let ρ := imageRepresentation M V hn
  let F := c.ambientFactor d s.first
  let H := c.ambientFactor d s.second
  let Q : Sylow 2 (internalActionImage M V hn) :=
    (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  let S := (Q : Subgroup (internalActionImage M V hn))
  let B := S ⊓ F.actor
  let W := F.space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)
  change subspaceKernel ρ W (Jhat ρ) = B ⊔ H.actor ∧ _
  have hgen : F.actor ⊔ H.actor = Jhat ρ := by
    rw [←c.ambient_actors_generate d]
    apply le_antisymm
    · exact sup_le (le_iSup (fun k => (c.ambientFactor d k).actor) s.first)
        (le_iSup (fun k => (c.ambientFactor d k).actor) s.second)
    · exact iSup_le fun k => by
        rcases s.covers k with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
  have hcom : ∀ f ∈ F.actor, ∀ g ∈ H.actor, Commute f g := by
    intro f hf g hg
    simp only [F,H,FactorData.ambientFactor,Factor.map_actor,FactorData.embedding] at hf hg
    obtain ⟨f,hf,rfl⟩ := hf
    obtain ⟨g,hg,rfl⟩ := hg
    exact congrArg (Jhat ρ).subtype (d.actors_commute c.faithful s.distinct hf hg).eq
  have hHF : H.actor ≤ normalizer (F.actor : Set _) := by
    apply le_normalizer_iff.mpr
    intro g hg f hf
    rw [(hcom f hf g hg).symm.eq,mul_inv_cancel_right]
    exact hf
  have hFn : (F.actor.subgroupOf (Jhat ρ)).Normal :=
    normal_subgroupOf_of_le_normalizer (hgen ▸ sup_le F.actor.le_normalizer hHF)
  have hsub : F.actor.IsSubnormal := Subgroup.IsSubnormal.trans
    (hgen ▸ le_sup_left) hFn.isSubnormal (Jhat_normal ρ).isSubnormal
  obtain ⟨QF,hQF⟩ := Q.exists_subgroupOf_eq_of_subnormal F.actor hsub
  have hp : s.prime.Prime := by rcases s.prime_cases with h | h <;> rw [h] <;> decide
  have hodd : Odd s.prime := by rcases s.prime_cases with h | h <;> rw [h] <;> decide
  have hFc : Nat.card F.actor = 2*s.prime :=
    (Nat.card_range_of_injective F.embedding.group_injective).trans
      ((Nat.card_congr (s.dihedral s.first).dihedral.some.toEquiv).trans DihedralGroup.nat_card)
  have hBc : Nat.card B = 2 := by
    have hh := sylow_card_two QF hodd hFc
    rw [hQF] at hh
    rw [←map_subgroupOf_eq_of_le (show B ≤ F.actor from inf_le_right)]
    simpa only [B,S,inf_subgroupOf_right,card_map_of_injective F.actor.subtype_injective] using hh
  have hi : B.relIndex F.actor = s.prime := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (internalActionImage M V hn)) B F.actor
      bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,hBc,hFc] at hh
    omega
  have hWplane : plane V W = thompsonPlane T V F.space := by
    have he : plane V W = plane V F.space ⊓ plane V (fixedSpace ρ
        (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V hn).rangeRestrict)) :=
      Subgroup.map_inf (binarySubgroup F.space)
        (binarySubgroup (fixedSpace ρ (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V hn).rangeRestrict))) V.subtype V.subtype_injective
    exact he.trans (congrArg (fun X : Subgroup G => plane V F.space ⊓ X)
      (plane_thompson_image hTM hn))
  have hWne : W ≠ ⊥ := by
    intro he
    have hh := plane_card (V := V) W
    rw [hWplane,s.thompson_card,he] at hh
    simp at hh
  have hWB : W ≤ fixedSpace ρ B := by
    have hJ' : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict = S ⊓ Jhat ρ := hJ
    have hBJ : B ≤ S ⊓ Jhat ρ := inf_le_inf_left _ (hgen ▸ le_sup_left)
    exact inf_le_right.trans (fixedSpace_antitone ρ (hBJ.trans hJ'.ge))
  have hWnot : ¬ W ≤ fixedSpace ρ F.actor := by
    intro hh
    apply hWne
    apply bot_unique
    have hkernel : (s.marking s.first).kernel.map F.embedding.groupMap ≤ F.actor := map_le_range _ _
    have hWF : W ≤ F.space := inf_le_left
    have hWH : W ≤ H.space := by
      rw [←s.kernel_fixed s.first s.second s.distinct]
      exact hh.trans (fixedSpace_antitone ρ hkernel)
    exact (le_inf hWF hWH).trans
      ((c.ambient_spaces_independent d).pairwiseDisjoint s.distinct).le_bot
  have hK : subspaceKernel ρ W F.actor = B :=
    subspaceKernel_eq_of_prime_index ρ F.actor B W inf_le_right (hi ▸ hp) hWB hWnot
  have hWH : W ≤ fixedSpace ρ H.actor :=
    inf_le_left.trans (c.ambient_cross d s.distinct)
  have he : subspaceKernel ρ W (Jhat ρ) = B ⊔ H.actor := by
    rw [←hgen,subspaceKernel_sup_of_fixed ρ F.actor H.actor W hHF hWH,hK]
  refine ⟨he,?_⟩
  change (pResidual 2 (subspaceKernel ρ W (Jhat ρ))).map _ = _
  rw [he,embedded_twoResidual_sup_of_centralizing_twoGroup B H.actor
    Q.isPGroup'.to_inf_left (by
      intro b hb g hg
      exact (hcom b hb.2 g hg).symm.eq)]
  let e : H.Carrier ≃* H.actor := MonoidHom.ofInjective H.embedding.group_injective
  have hr := map_pResidual_of_surjective 2 e.toMonoidHom e.surjective
  have hh := congrArg (Subgroup.map H.actor.subtype) hr
  rw [map_map] at hh
  change (pResidual 2 H.Carrier).map H.embedding.groupMap =
    (pResidual 2 H.actor).map H.actor.subtype at hh
  exact hh.symm.trans (congrArg (Subgroup.map H.embedding.groupMap)
    (s.marking s.second).kernel_eq_twoResidual.symm)
end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker

namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The same-prime residual inside the original factor product has exactly
the two original sixteen-element fixed and moved supports. -/
theorem ThompsonPair.core_residual_geometry {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    let ρ := imageRepresentation M V hn
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let C := subspaceKernel ρ W (Jhat ρ)
    let R := (pResidual 2 C).map C.subtype
    Nat.card (pResidual 2 C) = s.prime ∧
    fixedSpace ρ R = (c.ambientFactor d s.first).space ∧
    subspaceCommutator ρ ⊤ R = (c.ambientFactor d s.second).space ∧
    Nat.card (plane V (fixedSpace ρ R)) = 16 ∧
    Nat.card (plane V (subspaceCommutator ρ ⊤ R)) = 16 := by
  intro ρ W C R
  have he : R = (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap :=
    (s.core_centralizer hTM hn c d hJ).2
  have hf : fixedSpace ρ R = (c.ambientFactor d s.first).space := by
    rw [he]
    exact s.kernel_fixed s.second s.first s.distinct.symm
  have hm : subspaceCommutator ρ ⊤ R = (c.ambientFactor d s.second).space := by
    rw [he]
    exact s.kernel_moved s.second
  refine ⟨?_,hf,hm,?_,?_⟩
  · rw [←card_map_of_injective C.subtype_injective]
    exact (congrArg (fun A : Subgroup (internalActionImage M V hn) => Nat.card A) he).trans (s.kernel_card s.second)
  · rw [hf]
    exact s.support_card s.first
  · rw [hm]
    exact s.support_card s.second

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker

namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The centralizer of the marked subgroup inside the actual preimage of Jhat,
viewed as a subgroup of M. -/
@[expose] noncomputable def factorCentralizer (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (W : Submodule (ZMod 2) (Additive V)) : Subgroup M :=
  (Jhat (imageRepresentation M V hn)).comap (actionHom M V hn).rangeRestrict ⊓
    (centralizer (plane V W : Set G)).subgroupOf M

omit [Finite G] in
/-- The original action map sends this literal centralizer onto the pointwise
kernel in the two-factor actor. -/
theorem factorCentralizer_image (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (W : Submodule (ZMod 2) (Additive V)) :
    (factorCentralizer M V hn W).map (actionHom M V hn).rangeRestrict =
      subspaceKernel (imageRepresentation M V hn) W (Jhat (imageRepresentation M V hn)) := by
  ext g
  constructor
  · rintro ⟨m,hm,rfl⟩
    exact ⟨hm.1,((ExtraspecialMarker.image_mem_kernel_iff M V hn W m).mpr hm.2).2⟩
  · intro hg
    obtain ⟨m,rfl⟩ := (actionHom M V hn).rangeRestrict_surjective g
    exact ⟨m,⟨hg.1,(ExtraspecialMarker.image_mem_kernel_iff M V hn W m).mp ⟨trivial,hg.2⟩⟩,rfl⟩

omit [Finite G] in
/-- The literal quotient kernel is precisely the original module centralizer. -/
theorem factorCentralizer_kernel (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (W : Submodule (ZMod 2) (Additive V)) :
    ((actionHom M V hn).rangeRestrict.comp (factorCentralizer M V hn W).subtype).ker =
      ((centralizer (V : Set G)).subgroupOf M).subgroupOf (factorCentralizer M V hn W) := by
  ext x
  change (actionHom M V hn).rangeRestrict x.val = 1 ↔ _
  have he : (actionHom M V hn).rangeRestrict x.val = 1 ↔ actionHom M V hn x.val = 1 :=
    Subtype.ext_iff
  exact he.trans (show x.val ∈ (actionHom M V hn).ker ↔ _ from by rw [actionHom_ker]; rfl)

/-- Compute the residual through the same quotient and action maps. The
quotient is by C_M(V), rather than by a two-core. -/
theorem ThompsonPair.factorCentralizer_residual {T : Sylow 2 G} {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn)) :
    let ρ := imageRepresentation M V hn
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let C := factorCentralizer M V hn W
    let a := (actionHom M V hn).rangeRestrict.comp C.subtype
    (pResidual 2 C).map a =
      (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap ∧
    Nat.card (pResidual 2 (C ⧸ a.ker)) = s.prime := by
  intro ρ W C a
  let K := subspaceKernel ρ W (Jhat ρ)
  have hCK : C.map (actionHom M V hn).rangeRestrict = K := factorCentralizer_image M V hn W
  have hr := map_embedded_pResidual 2 C (actionHom M V hn).rangeRestrict
  have he := (s.core_centralizer hTM hn c d hJ).2
  have himage : (pResidual 2 C).map a = (pResidual 2 K).map K.subtype := by
    exact (map_map _ _ _).symm.trans (hr.trans (congrArg
      (fun H : Subgroup (internalActionImage M V hn) => (pResidual 2 H).map H.subtype) hCK))
  refine ⟨himage.trans he,?_⟩
  have harange : a.range = K := by
    exact (MonoidHom.range_comp _ _).trans (by rw [range_subtype]; exact hCK)
  let e : (C ⧸ a.ker) ≃* K := (QuotientGroup.quotientKerEquivRange a).trans
    (MulEquiv.subgroupCongr harange)
  have hc : Nat.card (pResidual 2 (C ⧸ a.ker)) = Nat.card (pResidual 2 K) := by
    rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,
      map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
  exact hc.trans (s.core_residual_geometry hTM hn c d hJ).1

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
