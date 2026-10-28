module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.Representation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.Summand
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting.Coordinates

/-!
# Splitting the literal K⁺-module in the ordinary A₇ branch

The genuine earlier identity [W_K,K] = [Z(O₂(K)),K] embeds U(K) in W_K.
`Coordinates` identifies U(K), using the SAME `ordinaryModuleModel`, with
the natural binary A₇ module. Every displacement of W_K belongs to that
embedded module. Vanishing first cohomology supplies a fixed complement.
Finally W_K = ⟨z^K⟩ makes the complement cyclic, hence of dimension at most one.
All transports use the literal plus projection and component image.

The earlier commutator identity remains explicit, with source producers
`qt-13-06-selection-modules` and
`qt-13-06-control-characteristic-normalizers`. Commutator generation of U(K)
is proved from IsShort.twoPerfect in the intrinsic cover; no extra Irr⁺ or
cover premise is required. The result concerns K⁺; extending it to the full
plus actor and the final Baumann argument belong to the parent assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.3(1),
printed p.84/PDF95, and Lemma 13.6.22, printed p.932/PDF949.
-/

@[expose] public section

open scoped IsMulCommutative commutatorElement
open Subgroup Representation
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting
variable {G : Type*} [Group G] (K L T : Subgroup G) (z v : G)

private noncomputable def blockEmbedding
    (hU : (blockU K).map K.subtype ≤ WK K L T z v) :
    blockU K →* Carrier K L T z v where
  toFun u := ⟨⟨u.val.val, K_le_plusActor K L T v u.val.property⟩,
    hU (mem_map_of_mem K.subtype u.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem blockEmbedding_injective
    (hU : (blockU K).map K.subtype ≤ WK K L T z v) :
    Function.Injective (blockEmbedding K L T z v hU) := by
  intro u w h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : Carrier K L T z v => (x.val : G)) h

variable [IsElementaryAbelian 2 (WK K L T z v)]

private noncomputable def blockLinear (h : IsAlternatingBlock K 7)
    (hU : (blockU K).map K.subtype ≤ WK K L T z v) :
    letI := h.2.1.elementary
    Additive (blockU K) →ₗ[ZMod 2] Additive (Carrier K L T z v) := by
  let := h.2.1.elementary
  exact (blockEmbedding K L T z v hU).toAdditive.toZModLinearMap 2

private theorem blockLinear_conjugate (h : IsAlternatingBlock K 7)
    (hU : (blockU K).map K.subtype ≤ WK K L T z v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hWT : WK K L T z v ≤ Tv T v)
    (k : K) (u : blockU K) :
    letI := h.2.1.elementary
    representation K L T z v hL hz hWT (componentMap K L T z v hL hz k).val
      (blockLinear K L T z v h hU (Additive.ofMul u)) =
      blockLinear K L T z v h hU (Additive.ofMul (blockConjugate K k u)) := by
  let := h.2.1.elementary
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  exact representation_apply K L T z v hL hz hWT
    ⟨k, K_le_plusActor K L T v k.property⟩ _

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting
variable {G : Type*} [Group G] (K L T : Subgroup G) (z v : G)
variable [IsElementaryAbelian 2 (WK K L T z v)]

private def carrierMap : Carrier K L T z v →* G :=
  (plusActor K L T v).subtype.comp (Carrier K L T z v).subtype

omit [IsElementaryAbelian 2 (WK K L T z v)] in
private theorem carrierMap_injective : Function.Injective (carrierMap K L T z v) :=
  (plusActor K L T v).subtype_injective.comp (Carrier K L T z v).subtype_injective

private theorem seed_linear_span
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hWT : WK K L T z v ≤ Tv T v)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (w : Additive (Carrier K L T z v)) (hw : carrierMap K L T z v w.toMul = z) :
    Submodule.span (ZMod 2) (Set.range (fun k : plusImage K L T z v hL hz K =>
      representation K L T z v hL hz hWT k.val w)) = ⊤ := by
  let S := Submodule.span (ZMod 2) (Set.range (fun k : plusImage K L T z v hL hz K =>
      representation K L T z v hL hz hWT k.val w))
  let A := S.toAddSubgroup.toSubgroup'
  have hWA : WK K L T z v ≤ A.map (carrierMap K L T z v) := by
    rw [seed_span K L T z v hn hLv]
    apply (closure_le _).mpr
    rintro _ ⟨k, hk, u, hu, rfl⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hu
    let a := representation K L T z v hL hz hWT
      (componentMap K L T z v hL hz ⟨k, hk⟩).val w
    have ha : a.toMul ∈ A := by
      change a ∈ S
      exact Submodule.subset_span ⟨componentMap K L T z v hL hz ⟨k, hk⟩, rfl⟩
    refine ⟨a.toMul ^ n, A.zpow_mem ha n, ?_⟩
    rw [map_zpow]
    have he : carrierMap K L T z v a.toMul = k * z * k⁻¹ := by
      change (((representation K L T z v hL hz hWT
        (plusMk K L T z v hL hz ⟨k, K_le_plusActor K L T v hk⟩) w).toMul :
        plusActor K L T v) : G) = _
      rw [ModuleComparison.representation_apply]
      exact congrArg (fun x => k * x * k⁻¹) hw
    rw [he, conj_zpow]
  apply top_unique
  intro u _
  obtain ⟨a, ha, he⟩ := hWA u.toMul.property
  have he' := carrierMap_injective K L T z v he
  change u.toMul ∈ A
  rw [← he']
  exact ha
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting
open BinaryPermutation
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting
variable {G : Type*} [Group G] [Finite G] (K L T : Subgroup G) (z v : G)
variable [IsElementaryAbelian 2 (WK K L T z v)]

private noncomputable def componentEquiv
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v) (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (h : IsAlternatingBlock K 7) :
    plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 7) :=
  (componentQuotientEquiv K L T z v hL hz hn hLv hY hR (ordinaryQuotientEquiv K h)).symm.trans
    (ordinaryQuotientEquiv K h)

omit [IsElementaryAbelian 2 (WK K L T z v)] in
private theorem componentEquiv_apply
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v) (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (h : IsAlternatingBlock K 7) (k : K) :
    componentEquiv K L T z v hL hz hn hLv hY hR h (componentMap K L T z v hL hz k) =
      blockProjection K (ordinaryQuotientEquiv K h) k := by
  unfold componentEquiv
  rw [MulEquiv.trans_apply,
    ← componentQuotientEquiv_mk K L T z v hL hz hn hLv hY hR (ordinaryQuotientEquiv K h) k,
    MulEquiv.symm_apply_apply]
  rfl

/-- Split the literal component action for any permutation homomorphism compatible
with the chosen block coordinates. The sole earlier module identity is the
source equality [W_K,K] = [Z(O₂(K)),K]; no splitting or codimension is assumed. -/
theorem natural_component_summand
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hWT : WK K L T z v ≤ Tv T v)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v) (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (h : IsAlternatingBlock K 7)
    (hUK : ⁅WK K L T z v, K⁆ =
      ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆)
    (φ : Gplus K L T z v hL hz →* Equiv.Perm (Fin 7))
    (hφ : ∀ k : K, φ (plusMk K L T z v hL hz
      ⟨k, K_le_plusActor K L T v k.property⟩) =
        (blockProjection K (ordinaryQuotientEquiv K h) k).val) :
    ∃ d : NaturalSummand
      ((representation K L T z v hL hz hWT).comp (plusImage K L T z v hL hz K).subtype)
      (φ.comp (plusImage K L T z v hL hz K).subtype),
      Module.finrank (ZMod 2) d.projection.ker ≤ 1 := by
  let := h.2.1.elementary
  let B := plusImage K L T z v hL hz K
  let ρ := (representation K L T z v hL hz hWT).comp B.subtype
  let e := componentEquiv K L T z v hL hz hn hLv hY hR h
  have hUK' : ⁅WK K L T z v, K⁆ = (blockU K).map K.subtype :=
    hUK.trans (central_commutator K h.2.1)
  have hU : (blockU K).map K.subtype ≤ WK K L T z v := by
    rw [← hUK']
    exact le_normalizer_iff_commutator_le_left.mp
      ((K_le_plusActor K L T v).trans (plusActor_normalizes_WK K L T z v hL hz))
  let E := coordinates K h
  let j := blockLinear K L T z v h hU
  let i := j.comp E.symm.toLinearMap
  have hi : Function.Injective i :=
    (blockEmbedding_injective K L T z v hU).comp E.symm.injective
  have he (g : B) (w : natural (Fin 7)) : ρ g (i w) = i (naturalAction e g w) := by
    obtain ⟨k, rfl⟩ := componentMap_surjective K L T z v hL hz g
    change representation K L T z v hL hz hWT (componentMap K L T z v hL hz k).val
      (j (E.symm w)) = j (E.symm (naturalAction e (componentMap K L T z v hL hz k) w))
    refine (blockLinear_conjugate K L T z v h hU hL hz hWT k (E.symm w).toMul).trans ?_
    apply congrArg j
    apply E.injective
    rw [E.apply_symm_apply]
    change E (Additive.ofMul (blockConjugate K k (E.symm w).toMul)) = _
    rw [coordinates_conjugate K h]
    change naturalRepresentation (Fin 7) (blockProjection K (ordinaryQuotientEquiv K h) k).val
      (E (E.symm w)) = _
    rw [E.apply_symm_apply]
    change naturalRepresentation (Fin 7) (blockProjection K (ordinaryQuotientEquiv K h) k).val w =
      naturalRepresentation (Fin 7) (e (componentMap K L T z v hL hz k)).val w
    rw [componentEquiv_apply]
  have hm (g : B) (w : Additive (Carrier K L T z v)) : ρ g w - w ∈ i.range := by
    obtain ⟨k, rfl⟩ := componentMap_surjective K L T z v hL hz g
    have hx : carrierMap K L T z v (ρ (componentMap K L T z v hL hz k) w - w).toMul ∈
        (blockU K).map K.subtype := by
      rw [← hUK', commutator_comm]
      change (((representation K L T z v hL hz hWT
        (plusMk K L T z v hL hz ⟨k, K_le_plusActor K L T v k.property⟩) w).toMul :
          plusActor K L T v) : G) / ((w.toMul : plusActor K L T v) : G) ∈ _
      rw [ModuleComparison.representation_apply, div_eq_mul_inv]
      exact commutator_mem_commutator k.property w.toMul.property
    obtain ⟨u, hu, heq⟩ := hx
    refine ⟨E (Additive.ofMul ⟨u, hu⟩), ?_⟩
    change j (E.symm (E (Additive.ofMul ⟨u, hu⟩))) = _
    rw [E.symm_apply_apply]
    apply Additive.toMul.injective
    apply carrierMap_injective K L T z v
    exact heq
  have hφe : φ.comp B.subtype = (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    obtain ⟨k, rfl⟩ := componentMap_surjective K L T z v hL hz g
    change φ (plusMk K L T z v hL hz ⟨k, K_le_plusActor K L T v k.property⟩) =
      (e (componentMap K L T z v hL hz k)).val
    rw [hφ, componentEquiv_apply]
  obtain ⟨d⟩ := split_of_injective e i hi he hm
  rw [← hφe] at d
  have hzW : z ∈ WK K L T z v := by
    rw [seed_span K L T z v hn hLv]
    exact le_conjugateSpanBy (zpowers z) K (mem_zpowers z)
  let w : Additive (Carrier K L T z v) :=
    Additive.ofMul ⟨⟨z, (show Tv T v ≤ plusActor K L T v from le_sup_right) (hWT hzW)⟩, hzW⟩
  exact ⟨d, seed_bound d w (seed_linear_span K L T z v hL hz hWT hn hLv w rfl)⟩


/-- Apply the component splitting to the injective action supplied by
`ordinary_action_exists`, retaining its equality on every original k. -/
theorem ordinary_component_splitting
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hWT : WK K L T z v ≤ Tv T v)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v) (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (h : IsAlternatingBlock K 7)
    (hUK : ⁅WK K L T z v, K⁆ =
      ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆) :
    ∃ φ : Gplus K L T z v hL hz →* Equiv.Perm (Fin 7),
      Function.Injective φ ∧
      (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7) ∧
      (∀ k : K, φ (plusMk K L T z v hL hz
        ⟨k, K_le_plusActor K L T v k.property⟩) =
          (blockProjection K (ordinaryQuotientEquiv K h) k).val) ∧
      ∃ d : NaturalSummand
        ((representation K L T z v hL hz hWT).comp (plusImage K L T z v hL hz K).subtype)
        (φ.comp (plusImage K L T z v hL hz K).subtype),
        Module.finrank (ZMod 2) d.projection.ker ≤ 1 := by
  obtain ⟨φ, hi, hm, hc⟩ := ordinary_action_exists K L T z v hL hz hn hLv hY hR h
  exact ⟨φ, hi, hm, hc, natural_component_summand K L T z v hL hz hWT hn hLv hY hR h hUK φ hc⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting

end
