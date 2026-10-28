module
public import Theory.Mathieu.M23.QuasithinGeometry.SourceRecognition.PairOrbit
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalQuotients
public import Theory.GroupTheory.Recognition.QuasithinM23.ActorNormalizer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.ElementaryAbelian.EightQuotientRank
/-!
# The automorphism image of the native pair/heptad intersection

The intersection has order 1920 and acts on the full sixteen-core with kernel
that core. Its image has order 120 in GL(4,2). Under GL(4,2) = A8 the
normalizer of this image lies in the marked A7; the pair stabilizer there is
self-normalizing. Thus the actual action image is self-normalizing.

Source: Aschbacher--Smith 5.2.20(5), printed pp.656--657. This is the native
core-restriction calculation used to align the two original local markings.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry
private abbrev H := pairStabilizer.subgroupOf heptadStabilizer
private abbrev V := Fin 4 → ZMod 2

private theorem H_card : Nat.card H = 1920 := by
  have hi : H.index = 21 := by
    change (MulAction.stabilizer heptadStabilizer x.val).index = 21
    rw [MulAction.index_stabilizer,heptad_pair_orbit]
    have hs : {p : Finset (Fin 23) | p.card = 2 ∧ p ⊆ omega} =
        (omega.powersetCard 2 : Set (Finset (Fin 23))) := by
      ext p
      simp only [Set.mem_ofPred_eq,Finset.mem_coe,Finset.mem_powersetCard,and_comm]
    rw [hs,Set.ncard_coe_finset,Finset.card_powersetCard]
    decide +kernel
  have hh := H.card_mul_index
  rw [hi,heptadStabilizer_card] at hh
  omega

private theorem H_preimage : H =
    (MulAction.stabilizer (alternatingGroup (Fin 7)) ({5,6} : Set (Fin 7))).comap
      heptadAlternatingAction := by
  ext g
  have hx : ({5,6} : Finset (Fin 7)).image label = x.val := by decide +kernel
  have hh := heptadAction_stabilizes_labels g ({5,6} : Finset (Fin 7))
  rw [hx] at hh
  change (g : M23) • x.val = x.val ↔ _
  rw [←hh]
  rw [←Finset.coe_inj]
  simp only [Finset.coe_smul_finset,Finset.coe_insert,Finset.coe_singleton]
  rfl

private theorem H_self_normalizing : normalizer (H : Set heptadStabilizer) = H := by
  let P := MulAction.stabilizer (alternatingGroup (Fin 7)) ({5,6} : Set (Fin 7))
  have hP : IsCoatom P := alternatingGroup.isCoatom_stabilizer_of_ncard_lt_ncard_compl
    (by exact ⟨5,by simp,6,by simp,by decide⟩) (by
      have hh := Set.ncard_add_ncard_compl ({5,6} : Set (Fin 7))
      rw [Set.ncard_pair (by decide),Nat.card_fin] at hh
      rw [Set.ncard_pair (by decide)]
      omega)
  have hPne : P ≠ ⊥ := by
    intro hh
    let t : alternatingGroup (Fin 7) := ⟨Equiv.swap 0 1 * Equiv.swap 5 6,by
      change Equiv.Perm.sign _ = 1; decide⟩
    have ht : t ∈ P := by
      change t • ({5,6} : Set (Fin 7)) = {5,6}
      simp only [Set.smul_set_insert,Set.smul_set_singleton]
      change ({6,5} : Set (Fin 7)) = {5,6}
      exact Set.pair_comm _ _
    have ht1 := mem_bot.mp (hh ▸ ht)
    have hx := congrArg (fun g : alternatingGroup (Fin 7) => g.val 0) ht1
    have : (1 : Fin 7) = 0 := hx
    contradiction
  have hNP : normalizer (P : Set (alternatingGroup (Fin 7))) = P := by
    by_contra hn
    have htop := hP.2 _ (lt_of_le_of_ne P.le_normalizer (Ne.symm hn))
    let : P.Normal := normalizer_eq_top_iff.mp htop
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 7))
      (N := P) with hh | hh
    · exact hPne hh
    · exact hP.1 hh
  rw [H_preimage,←comap_normalizer_eq_of_surjective P
    (fun a => ⟨AlternatingSection.s a,heptadAlternatingAction_section a⟩),hNP]

private def coreLinear : MulAut heptadKernel ≃* (V ≃ₗ[ZMod 2] V) :=
  (MulAut.congr heptadBinaryEquiv.symm).trans {
    toFun a := {
      toFun v := (a (Multiplicative.ofAdd v)).toAdd
      invFun v := (a.symm (Multiplicative.ofAdd v)).toAdd
      left_inv v := a.symm_apply_apply v
      right_inv v := a.apply_symm_apply v
      map_add' v w := a.map_mul v w
      map_smul' c v := by
        have hc : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
        rcases hc with rfl | rfl
        · simp only [zero_smul,RingHom.id_apply]; exact a.map_one
        · simp only [one_smul,RingHom.id_apply] }
    invFun a := a.toAddEquiv.toMultiplicative
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }

private theorem coreLinear_conjugation (a : alternatingGroup (Fin 7)) :
    coreLinear (heptadConjugation a) = heptadLinearAction a := by ext v; rfl

private theorem conjugation_factor (a : heptadStabilizer) :
    (MulAut.conjNormal : heptadStabilizer →* MulAut heptadKernel) a =
      heptadConjugation (heptadAlternatingAction a) := by
  obtain ⟨w,rfl⟩ := heptadSplitEquiv.surjective a
  have hq : heptadAlternatingAction (heptadSplitEquiv w) = w.right :=
    Subtype.ext (heptadAction_split w)
  rw [hq]
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  change (w.left.val * AlternatingSection.s w.right) * u.val *
      (w.left.val * AlternatingSection.s w.right)⁻¹ = _
  have hu := congrArg Subtype.val (heptadKernel_mul_comm w.left (heptadConjugation w.right u))
  simp only [Subgroup.coe_mul,heptadConjugation_coe] at hu
  rw [heptadConjugation_coe]
  calc
    _ = w.left.val * (AlternatingSection.s w.right * u.val *
      (AlternatingSection.s w.right)⁻¹) * w.left.val⁻¹ := by group
    _ = _ := by rw [hu,mul_inv_cancel_right]

private abbrev actor : heptadStabilizer →* MulAut heptadKernel := MulAut.conjNormal

private theorem actor_ker : actor.ker = heptadKernel := by
  rw [MulAut.conjNormal_ker_eq_centralizer]
  apply le_antisymm heptadKernel_selfCentralizing
  intro u hu
  apply mem_centralizer_iff.mpr
  intro v hv
  exact congrArg Subtype.val (heptadKernel_mul_comm ⟨v,hv⟩ ⟨u,hu⟩)

private theorem core_le_H : heptadKernel ≤ H := by
  rw [H_preimage,←heptadAlternatingAction_ker]
  exact ker_le_comap _ _

private theorem actor_image_card : Nat.card (H.map actor) = 120 := by
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map H actor
  rw [actor_ker,inf_eq_right.mpr core_le_H,heptadKernel_card,H_card] at hh
  omega

/-- The automorphism image of the heptad/pair intersection on the actual
sixteen-core is self-normalizing in the full automorphism group of that core. -/
theorem heptad_pair_core_action_self_normalizing :
    normalizer ((pairStabilizer.subgroupOf heptadStabilizer).map
      (MulAut.conjNormal : heptadStabilizer →* MulAut heptadKernel) :
        Set (MulAut heptadKernel)) =
      (pairStabilizer.subgroupOf heptadStabilizer).map MulAut.conjNormal := by
  change normalizer (H.map actor : Set _) = H.map actor
  apply le_antisymm _ (H.map actor).le_normalizer
  intro c hc
  have hcle : (H.map actor).map coreLinear.toMonoidHom ≤ heptadLinearAction.range := by
    rintro _ ⟨_,⟨g,hg,rfl⟩,rfl⟩
    exact ⟨heptadAlternatingAction g,by rw [←coreLinear_conjugation,←conjugation_factor]; rfl⟩
  have hcard : Nat.card ((H.map actor).map coreLinear.toMonoidHom) = 120 :=
    (card_map_of_injective coreLinear.injective).trans actor_image_card
  have hcn : coreLinear c ∈ normalizer
      ((H.map actor).map coreLinear.toMonoidHom : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [←map_equiv_normalizer_eq]
    exact mem_map_of_mem _ hc
  obtain ⟨b,hb⟩ := Theory.GroupTheory.QuasithinM23.order120_linear_normalizer_le_exceptional
    heptadLinearAction heptadLinearAction_injective (by simp) _ hcle hcard hcn
  have he : actor (AlternatingSection.s b) = c := by
    apply coreLinear.injective
    exact hb
  have hgN : AlternatingSection.s b ∈ normalizer (H : Set heptadStabilizer) := by
    apply mem_normalizer_iff.mpr
    intro g
    have hmem (g : heptadStabilizer) : actor g ∈ H.map actor ↔ g ∈ H := by
      change g ∈ (H.map actor).comap actor ↔ _
      rw [comap_map_eq_self (actor_ker.le.trans core_le_H)]
    rw [←hmem g,←hmem (AlternatingSection.s b*g*(AlternatingSection.s b)⁻¹)]
    rw [map_mul,map_mul,map_inv,he]
    exact mem_normalizer_iff.mp hc (actor g)
  exact ⟨AlternatingSection.s b,H_self_normalizing ▸ hgN,he⟩

end Sporadic.Mathieu.M23Geometry
