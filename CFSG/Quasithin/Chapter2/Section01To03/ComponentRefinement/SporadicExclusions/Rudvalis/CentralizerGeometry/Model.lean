module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalCover.Generation
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.LocalSubgroups
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.Quasithin.EvenCharacteristic

/-!
# The Rudvalis max4 local and its involution-centralizer supplement

The aligned max4/max6 pair generates the actual degree-4060 model under the
simplicity hypothesis supplied by the source component. The center of the
marked Sylow subgroup has order two. Hence any inner involution fixing that
Sylow pointwise has the marked max6 conjugate as its fixed subgroup.
Sylow conjugacy transports the max4 seed and this generation equality to any
prescribed Sylow, retaining invariance under every Sylow-preserving automorphism.

The marked eight-group lies in O₂(max4), and its relative centralizer equals
O₂(max4); this proves the self-centralizing-core clause directly. The model
isomorphism is induced by the actual conjugation, not by a group-order label.
Source: Aschbacher–Smith 2.3.9(7), printed p.526; GLS3 Table 5.3r and its
max4 justification, printed pp.291–292. The imported ATLAS word certificates
retain their original attribution and permutation conventions.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase.CentralizerGeometry
open Subgroup Rudvalis
open Rudvalis.SylowOvergroups Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover

structure ModelSeed (S : Sylow 2 Model) (α : MulAut Model) where
  localSubgroup : Subgroup Model
  modelIso : localSubgroup ≃* max4
  sylow_le : (S : Subgroup Model) ≤ localSubgroup
  invariant : ∀ β : MulAut Model, (S : Subgroup Model).map β.toMonoidHom = S →
    localSubgroup.map β.toMonoidHom = localSubgroup
  selfCentralizing : centralizer (pCore 2 localSubgroup : Set localSubgroup) ≤
    pCore 2 localSubgroup
  generated : α.fixedSubgroup ⊔ localSubgroup = ⊤

private theorem max4_selfCentralizing :
    centralizer (pCore 2 max4 : Set max4) ≤ pCore 2 max4 := by
  intro x hx
  rw [← CoreQuotients.max4_centralizer_eq_pCore]
  change (x : Model) ∈ centralizer (elementary 2 : Set Model)
  intro y hy
  obtain ⟨w, hw, he⟩ := CoveringIncidence.marked_eight_le_core hy
  rw [← he]
  exact congrArg Subtype.val (hx w hw)

/-- The marked second local is the centralizer of the unique central involution
of the literal four-word Sylow subgroup. -/
private theorem marked_fixed (hc : center Model = ⊥) (α : MulAut Model)
    (ho : orderOf α = 2) (hi : ∃ x : Model, α = MulAut.conj x)
    (hf : ∀ x ∈ (SylowInvariantPair.sylow : Subgroup Model), α x = x) :
    α.fixedSubgroup = SylowInvariantPair.locals 1 := by
  obtain ⟨t, ht, hto, he⟩ := MulAut.inner_involution_fixing_sylow_center hc
    SylowInvariantPair.sylow α ho hi hf
  have hz : elementaryGenerator 0 ∈ elementary 0 := subset_closure (by simp)
  rw [SylowInvariantPair.elementary_zero_eq_center] at hz
  obtain ⟨u, hu, hzu⟩ := hz
  let tz : center localP := ⟨t, ht⟩
  let uz : center localP := ⟨u, hu⟩
  let : IsCyclic (center localP) :=
    isCyclic_of_prime_card SylowInvariantPair.localP_center_card
  have htorder : orderOf tz = 2 := by
    exact ((Subgroup.orderOf_coe tz).symm.trans (Subgroup.orderOf_coe t).symm).trans hto
  have huorder : orderOf uz = 2 := by
    have hu' : orderOf (u : Model) = 2 := by
      change orderOf (localP.subtype u) = 2
      rw [hzu]
      exact Max6Certificate.elementary_zero_order
    exact ((Subgroup.orderOf_coe uz).symm.trans (Subgroup.orderOf_coe u).symm).trans hu'
  have htu : (t : Model) = elementaryGenerator 0 :=
    (congrArg (fun v : center localP => (v.val : Model))
      (IsCyclic.eq_of_orderOf_eq_two htorder huorder)).trans hzu
  rw [he, htu, MulAut.fixedSubgroup_conj, SylowInvariantPair.second_eq_normalizer]
  change _ = normalizer (closure {elementaryGenerator 0} : Set Model)
  rw [← zpowers_eq_closure,
    normalizer_zpowers_eq_centralizer_of_order_two _ Max6Certificate.elementary_zero_order]

/-- Construct the actual invariant max4 conjugate over any prescribed Sylow.
Its supplement is the fixed subgroup of the supplied inner involution. -/
theorem nonempty_modelSeed [IsSimpleGroup Model] (hc : center Model = ⊥)
    (S : Sylow 2 Model) (α : MulAut Model) (ho : orderOf α = 2)
    (hi : α ∈ (MulAut.conj (G := Model)).range)
    (hf : ∀ x ∈ (S : Subgroup Model), α x = x) : Nonempty (ModelSeed S α) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model SylowInvariantPair.sylow S
  let e := MulAut.conj g
  have hS : (SylowInvariantPair.sylow : Subgroup Model).map e.toMonoidHom = S :=
    congrArg Sylow.toSubgroup hg
  let β := MulAut.congr e.symm α
  have hβo : orderOf β = 2 := (MulAut.congr e.symm).orderOf_eq α |>.trans ho
  have hβi : ∃ x : Model, β = MulAut.conj x := by
    apply (MulAut.congr_inner_iff e.symm α).mpr
    obtain ⟨x, hx⟩ := hi
    exact ⟨x, hx.symm⟩
  have hβf : ∀ x ∈ (SylowInvariantPair.sylow : Subgroup Model), β x = x := by
    intro x hx
    change e.symm (α (e x)) = x
    rw [hf _ (hS ▸ mem_map_of_mem e.toMonoidHom hx), e.symm_apply_apply]
  have hfixed := marked_fixed hc β hβo hβi hβf
  let P := max4.map e.toMonoidHom
  have hPC : centralizer (pCore 2 P : Set P) ≤ pCore 2 P :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap max4)).mp max4_selfCentralizing
  refine ⟨{
    localSubgroup := P
    modelIso := (e.subgroupMap max4).symm
    sylow_le := ?_
    invariant := ?_
    selfCentralizing := hPC
    generated := ?_ }⟩
  · rw [← hS]
    exact map_mono localP_le_max4
  · intro γ hγ
    let δ := MulAut.congr e.symm γ
    have hδ : (SylowInvariantPair.sylow : Subgroup Model).map δ.toMonoidHom =
        SylowInvariantPair.sylow := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_map]
      have he : e.toMonoidHom.comp δ.toMonoidHom = γ.toMonoidHom.comp e.toMonoidHom := by
        ext x
        exact e.apply_symm_apply (γ (e x))
      rw [he, ← map_map, hS, hγ]
    have hinv := SylowInvariantPair.locals_invariant 0 δ hδ
    change max4.map δ.toMonoidHom = max4 at hinv
    change (max4.map e.toMonoidHom).map γ.toMonoidHom = max4.map e.toMonoidHom
    rw [map_map]
    have he : γ.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp δ.toMonoidHom := by
      ext x
      exact (e.apply_symm_apply (γ (e x))).symm
    rw [he, ← map_map, hinv]
  · have hcmap : β.fixedSubgroup.map e.toMonoidHom = α.fixedSubgroup := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' := (MulAut.mem_fixedSubgroup β y).mp hy
        apply (MulAut.mem_fixedSubgroup α (e y)).mpr
        have hh := congrArg e hy'
        change e (e.symm (α (e y))) = e y at hh
        simpa only [e.apply_symm_apply] using hh
      · intro hx
        refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
        have hx' := (MulAut.mem_fixedSubgroup α x).mp hx
        apply (MulAut.mem_fixedSubgroup β (e.symm x)).mpr
        change e.symm (α (e (e.symm x))) = e.symm x
        rw [e.apply_symm_apply, hx']
    rw [← hcmap, hfixed]
    change (SylowInvariantPair.locals 1).map e.toMonoidHom ⊔
      (SylowInvariantPair.locals 0).map e.toMonoidHom = ⊤
    rw [← Subgroup.map_sup, sup_comm,
      CFSG.Quasithin.ChapterE.Rudvalis.LocalCover.locals_sup_eq_top,
      map_top_of_surjective _ e.surjective]

end CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase.CentralizerGeometry

end
