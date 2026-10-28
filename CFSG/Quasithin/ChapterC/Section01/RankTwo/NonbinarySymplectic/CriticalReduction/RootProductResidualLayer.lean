module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductClosureLayer
public import Glauberman.BaumannFixedIndex

/-!
# The residual omega layer of the original Baumann closure

For the rank-one envelope and its actual Baumann normal closure N, retain
the full original U-alpha inside N. Let P be the constructed Sylow
intersection, Z₀ its ordinary Thompson central omega, and D = [U-alpha,O²(N)].
Two-perfect commutator idempotence gives [Z₀ U-alpha,O²(N)] = D. Residual
movement makes D nonzero. The smaller Z₀D is elementary and N-normal,
contains the full normal closure of Z₀, and still lies in Q-alpha under
the two literal subgroup inclusions. D itself is residually generated.
The whole omega closure is Z₀ times its own residual commutator.

A residual conjugator gives opposite Baumann generators. If the whole core
centralizes this same D, its Baumann fixed index is at most q, and its
global fixed index is at least q², the checked fixed-index argument proves
that P maps to the original Baumann subgroup. The original field degree,
central attachments and characteristic replacement remain unchanged.

Source: MS93 (5.1), printed p.913. This supplies a precise local endgame for
the F₀ Sylow clause; its core-centralization and index premises remain to
be established. Selected-path generation, arbitrary-degree Niles pushing-up,
terminal exclusions and the distance-two witness are also still open.
-/

public noncomputable section
open scoped Pointwise
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual Baumann closure has a nonzero residual layer inside the full
original U. This layer gives a smaller normal enlargement of the original
Thompson central omega, at the unchanged field degree. -/
theorem Input.replacement_root_product_baumann_residual_layer
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hprod : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical))) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧
      ∃ S : Sylow 2 I,
        (S : Subgroup I).map I.subtype =
          Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) ∧
      let N := normalClosure (Glauberman.baumannSubgroup (S : Subgroup I) : Set I)
      N ⊔ pCore 2 I = ⊤ ∧
      Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
      generalizedFitting N = pCore 2 N ∧
      (pResidual 2 N).map N.subtype = pResidual 2 I ∧
      ∃ P : Sylow 2 N,
        ((Glauberman.baumannSubgroup (P : Subgroup N)).map N.subtype).map I.subtype =
          Glauberman.baumannSubgroup (Q d.radical t) ∧
        ((omegaCenterIn (thompsonSubgroup (P : Subgroup N))).map N.subtype).map I.subtype =
          omegaCenterIn (thompsonSubgroup (Q d.radical t)) ∧
        normalClosure (Glauberman.baumannSubgroup (P : Subgroup N) : Set N) = ⊤ ∧
        Order.HasUniqueMaximalOver (P : Subgroup N) ⊤ ∧
      let U₀ := ((U d.radical a).subgroupOf I).subgroupOf N
      let Z₀ := omegaCenterIn (thompsonSubgroup (P : Subgroup N))
      let D := ⁅U₀,pResidual 2 N⁆
      U₀.Normal ∧
      (Z₀ ⊔ U₀).Normal ∧ IsElementaryAbelian 2 (Z₀ ⊔ U₀ : Subgroup N) ∧
      ⁅Z₀ ⊔ U₀,pResidual 2 N⁆ = D ∧
      D ≠ ⊥ ∧ D ≤ U₀ ∧ ⁅D,pResidual 2 N⁆ = D ∧
      (Z₀ ⊔ D).Normal ∧ IsElementaryAbelian 2 (Z₀ ⊔ D : Subgroup N) ∧
      normalClosure (Z₀ : Set N) ≤ Z₀ ⊔ D ∧
      normalClosure (Z₀ : Set N) =
        Z₀ ⊔ ⁅normalClosure (Z₀ : Set N),pResidual 2 N⁆ ∧
      ((Z₀ ⊔ D).map N.subtype).map I.subtype ≤ Q d.radical a ∧
      ∃ x : N, x ∈ pResidual 2 N ∧
        (Glauberman.baumannSubgroup (P : Subgroup N) ⊔
          (Glauberman.baumannSubgroup (P : Subgroup N)).map (MulAut.conj x).toMonoidHom) ⊔
          pCore 2 N = ⊤ ∧
        (D ≤ centralizer (pCore 2 N : Set N) →
          (centralizer (Glauberman.baumannSubgroup (P : Subgroup N) : Set N)).relIndex D ≤
            Nat.card E.Carrier →
          Nat.card E.Carrier ^ 2 ≤ (center N).relIndex D →
          ((P : Subgroup N).map N.subtype).map I.subtype =
            Glauberman.baumannSubgroup (Q d.radical t)) := by
  obtain ⟨E,hE,I,hI,hQI,S,hS,hBa,hWB,hgen,heN,hcores,hfit,hres,hU,
    P,hP,hunique,hOm,hBP,hBgen,hZe,hmove,hseed,hVe,hVQ,hVm,hVs,hVomega,hVC,hOmegaC⟩ :=
    h.replacement_root_product_native_baumann_closure d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let := finite_stabilizer d.radical a
  let : Finite I := Finite.of_injective (inclusion hI) (inclusion_injective hI)
  let N := normalClosure (Glauberman.baumannSubgroup (S : Subgroup I) : Set I)
  let f := I.subtype.comp N.subtype
  have hf : Function.Injective f := I.subtype_injective.comp N.subtype_injective
  let Z₀ := omegaCenterIn (thompsonSubgroup (P : Subgroup N))
  let U₁ := (U d.radical a).subgroupOf I
  let U₀ := U₁.subgroupOf N
  let W := omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a
  obtain ⟨_,hWe,hWn,hWQ,hWL,_⟩ := h.replacement_root_product_thompson_layer d geometry hb ha hat
    E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  have hWI : W ≤ I := hWQ.trans hQI
  have hUI : U d.radical a ≤ I := le_sup_right.trans hWI
  have hUN : U₁ ≤ N := by
    intro u hu
    obtain ⟨v,hv,he⟩ := hU hu
    exact I.subtype_injective he ▸ hv
  have hUm : U₀.map f = U d.radical a := by
    rw [←Subgroup.map_map,map_subgroupOf_eq_of_le hUN,map_subgroupOf_eq_of_le hUI]
  have hZm : Z₀.map f = omegaCenterIn (thompsonSubgroup (Q d.radical t)) := by
    rw [←Subgroup.map_map]
    exact hOm
  have hWm : (Z₀ ⊔ U₀).map f = W := by rw [Subgroup.map_sup,hZm,hUm]
  let : U₁.Normal := (normal_subgroupOf_iff_le_normalizer hUI).mpr
    (hI.trans (U_normalized a))
  let : U₀.Normal := inferInstance
  let W₁ := W.subgroupOf I
  let : W₁.Normal := (normal_subgroupOf_iff_le_normalizer hWI).mpr (hI.trans hWn)
  have hWN : W₁ ≤ N := by
    have hh := congrArg (Subgroup.comap I.subtype) hWm
    rw [←Subgroup.map_map,comap_map_eq_self_of_injective I.subtype_injective] at hh
    change W.comap I.subtype ≤ N
    rw [←hh]
    exact map_subtype_le _
  have hWnative : Z₀ ⊔ U₀ = W₁.subgroupOf N := by
    apply map_injective hf
    rw [hWm,←Subgroup.map_map,map_subgroupOf_eq_of_le hWN,map_subgroupOf_eq_of_le hWI]
  let : (Z₀ ⊔ U₀ : Subgroup N).Normal := hWnative ▸ inferInstance
  let : IsElementaryAbelian 2 W := hWe
  let : IsElementaryAbelian 2 W₁ := IsElementaryAbelian.subgroupOf hWI
  let : IsElementaryAbelian 2 (W₁.subgroupOf N) := IsElementaryAbelian.subgroupOf hWN
  let : IsElementaryAbelian 2 (Z₀ ⊔ U₀ : Subgroup N) := hWnative ▸ inferInstance
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.of_le (show U₀ ≤ Z₀ ⊔ U₀ from le_sup_right)
  have hLm : (pResidual 2 N).map f = (pResidual 2 I).map I.subtype := by
    rw [←Subgroup.map_map,hres]
  have hLL : (pResidual 2 N).map f ≤ Ltilde d.radical a := by
    rw [hLm]
    exact embedded_pResidual_mono 2 hI
  have hmoveU : ⁅Z₀ ⊔ U₀,pResidual 2 N⁆ ≤ U₀ := by
    apply (map_le_map_iff_of_injective hf).mp
    rw [map_commutator,hWm,hUm]
    exact (commutator_mono le_rfl hLL).trans hWL
  obtain ⟨hD,hDN,hDe,hZbound⟩ := Glauberman.baumann_residual_enlargement P U₀ hBgen hmoveU
  let D := ⁅U₀,pResidual 2 N⁆
  have hDU : D ≤ U₀ := commutator_le_left _ _
  have hDne : D ≠ ⊥ := by
    intro hz
    apply hmove
    apply bot_unique
    exact ((commutator_mono (show Z₀ ≤ Z₀ ⊔ U₀ from le_sup_left) le_rfl).trans_eq hD).trans_eq hz
  let eN := Classical.choice heN
  let q := eN.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
  have hq : Function.Surjective q := eN.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 N := by
    change eN.toMonoidHom.ker.comap (QuotientGroup.mk' (pCore 2 N)) = _
    rw [eN.toMonoidHom.ker_eq_bot eN.injective,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  obtain ⟨hsupp,_,x,hx,hopp,_⟩ :=
    Glauberman.baumann_rank_one_opposites_of_generation P q hq hk hBgen
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le hDU
  let : (Z₀ ⊔ D : Subgroup N).Normal := hDN
  let : IsElementaryAbelian 2 (Z₀ ⊔ D : Subgroup N) := hDe
  refine ⟨E,hE,I,hI,S,hS,hgen,heN,hfit,hres,P,hBP,hOm,hBgen,hunique,
    inferInstance,inferInstance,inferInstance,hD,hDne,hDU,?_,hDN,hDe,hZbound,
    Glauberman.baumann_omega_closure_eq_sup_residual P hBgen,?_,x,hx,hopp,?_⟩
  · exact commutator_isPPerfect_idempotent (pResidual 2 N) U₀
      (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 U₀) le_normalizer_of_normal
  · rw [Subgroup.map_map]
    exact ((map_mono (f := f) (sup_le_sup_left hDU Z₀)).trans_eq hWm).trans hWQ
  · intro hcore hi hiG
    have he := (Glauberman.baumann_eq_sylow_of_fixed_index_bounds P D
      hBgen hsupp hcore x hopp (Nat.card E.Carrier) hi hiG).2
    rw [←he]
    exact hBP

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
