module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Core
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeLargeField
public import Theory.ElementaryAbelian.Injective
public import Mathlib.Tactic.Group

/-!
# Central splitting in the linear closure branch

For p whose L-commutators lie in V and which centralizes O₂(L), those
commutators define a cocycle on the actual marked SL₃ quotient. Vanishing
of natural H¹ supplies v∈V with v⁻¹p centralizing L. Applying this to the
collapsed three-conjugate core gives S=V C_S(L).

Faithfulness of the actual I-action on V identifies its centralizer with
S. Consequently C_S(L)=C_U(L), this factor is elementary abelian, and
I=L S gives U=(U∩L)C_U(L). The factor C_U(L) is central in U. No equality
between U and T∩L is asserted.

Source: Aschbacher--Smith, 11.5.7, printed p.782, using I.1.6 and C.1.13(b).
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped Pointwise
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

include d

set_option backward.isDefEq.respectTransparency false in
private theorem centralizing_correction (p : G)
    (hdis : ∀ l : L, ⁅(l : G),p⁆ ∈ V)
    (hfix : ∀ l : L, l ∈ pCore 2 L → Commute (l : G) p) :
    ∃ v : V, (v : G)⁻¹ * p ∈ centralizer (L : Set G) := by
  classical
  let F := E.input.field.Carrier
  let A := Matrix.SpecialLinearGroup (Fin 3) F
  let ρ := specialLinearNatural (k := F) 3
  let f : L →* A := d.model.toMonoidHom.comp (starProjection (setup E))
  have hf : Function.Surjective f := d.model.surjective.comp (starProjection_surjective (setup E))
  let δ (l : L) : V := ⟨⁅(l : G),p⁆, hdis l⟩
  let c (l : L) : Fin 3 → F := (d.coordinates (δ l)).toAdd
  have hc_eq (l : L) : (d.coordinates.symm (Multiplicative.ofAdd (c l)) : G) =
      (l : G) * p * (l : G)⁻¹ * p⁻¹ := by
    exact congrArg Subtype.val (d.coordinates.symm_apply_apply (δ l))
  have hc_same {l t : L} (h : f l = f t) : c l = c t := by
    have hn : t⁻¹ * l ∈ pCore 2 L := by
      rw [← starProjection_ker E, MonoidHom.mem_ker]
      apply d.model.injective
      change f (t⁻¹ * l) = d.model 1
      rw [map_mul, map_inv, h, inv_mul_cancel, map_one]
    have hcomm := (hfix (t⁻¹ * l) hn).eq
    change ((t : G)⁻¹ * (l : G)) * p = p * ((t : G)⁻¹ * (l : G)) at hcomm
    have he : (l : G) * p * (l : G)⁻¹ * p⁻¹ = (t : G) * p * (t : G)⁻¹ * p⁻¹ := by
      calc
        _ = (t : G) * (((t : G)⁻¹ * (l : G)) * p) * (l : G)⁻¹ * p⁻¹ := by group
        _ = (t : G) * (p * ((t : G)⁻¹ * (l : G))) * (l : G)⁻¹ * p⁻¹ := by rw [hcomm]
        _ = _ := by group
    exact congrArg (fun v : V => (d.coordinates v).toAdd) (Subtype.ext he)
  have hcoc (l t : L) : c (l * t) = ρ (f l) (c t) + c l := by
    have he := d.equivariant l (δ t)
    change (d.coordinates _).toAdd = ρ (f l) (c t) at he
    rw [← he]
    change (d.coordinates (δ (l * t))).toAdd =
      (d.coordinates _).toAdd + (d.coordinates (δ l)).toAdd
    change d.coordinates (δ (l * t)) = d.coordinates _ * d.coordinates (δ l)
    rw [← map_mul]
    apply congrArg d.coordinates
    apply Subtype.ext
    change ((l : G) * (t : G)) * p * ((l : G) * (t : G))⁻¹ * p⁻¹ =
      ((l : G) * ((t : G) * p * (t : G)⁻¹ * p⁻¹) * (l : G)⁻¹) *
        ((l : G) * p * (l : G)⁻¹ * p⁻¹)
    group
  let b (a : A) : L := (hf a).choose
  have hb (a : A) : f (b a) = a := (hf a).choose_spec
  let z : cocycles ρ := ⟨fun a => c (b a), by
    intro a t
    have he := hc_same (show f (b (a*t)) = f (b a * b t) by rw [map_mul,hb,hb,hb])
    exact he.trans (by rw [hcoc,hb])⟩
  have hF : 2 < Nat.card F := by
    rw [show Nat.card F = 2 ^ E.input.field.degree from d.field_card]
    exact (by norm_num : 2 < 2 ^ 2).trans_le
      (Nat.pow_le_pow_right (by decide) E.input.nonbinary)
  obtain ⟨w, hw⟩ := SLHigherNatural.exists_principal_sl3_large_field hF z
  have hcw (l : L) : c l = ρ (f l) w - w := by
    have he := congrArg (fun z : cocycles ρ => z.val (f l)) hw
    exact (hc_same (hb (f l)).symm).trans he
  let v : V := d.coordinates.symm (Multiplicative.ofAdd w)
  refine ⟨v, ?_⟩
  intro l hl
  let l' : L := ⟨l,hl⟩
  have he := d.equivariant l' v
  change (d.coordinates _).toAdd = ρ (f l') (d.coordinates v).toAdd at he
  have hv : (d.coordinates v).toAdd = w := d.coordinates.apply_symm_apply _
  rw [hv] at he
  have hδ : l * p * l⁻¹ * p⁻¹ = l * (v : G) * l⁻¹ * (v : G)⁻¹ := by
    have hh := hc_eq l'
    rw [hcw, sub_eq_add_neg] at hh
    change (d.coordinates.symm
      (Multiplicative.ofAdd (ρ (f l') w) * (Multiplicative.ofAdd w)⁻¹) : G) = _ at hh
    rw [map_mul, map_inv] at hh
    have he' : (d.coordinates.symm (Multiplicative.ofAdd (ρ (f l') w)) : G) =
        l * (v : G) * l⁻¹ := by
      exact congrArg Subtype.val (d.coordinates.symm_apply_eq.mpr he.symm)
    change (d.coordinates.symm (Multiplicative.ofAdd (ρ (f l') w)) : G) * (v : G)⁻¹ = _ at hh
    rw [he'] at hh
    exact hh.symm
  change l * ((v : G)⁻¹ * p) = ((v : G)⁻¹ * p) * l
  calc
    _ = (l * (v : G) * l⁻¹)⁻¹ * (l * p * l⁻¹ * p⁻¹) * p * l := by group
    _ = (l * (v : G) * l⁻¹)⁻¹ * (l * (v : G) * l⁻¹ * (v : G)⁻¹) * p * l := by rw [hδ]
    _ = _ := by group


/-- Vanishing natural H¹ splits a subgroup whose displacements lie in V
and whose elements commute with the actual two-core of L. -/
theorem split_of_commutator (P : Subgroup G) (hVP : V ≤ P)
    (hPL : ⁅P,L⁆ ≤ V) (hPC : P ≤ centralizer (L.pCoreIn 2 : Set G)) :
    P = V ⊔ (P ⊓ centralizer (L : Set G)) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨v, hv⟩ := centralizing_correction E d p
      (fun l => hPL (by rw [commutator_comm]; exact commutator_mem_commutator l.property hp))
      (fun l hl => hPC hp l (mem_map_of_mem L.subtype hl))
    have hvP : (v : G)⁻¹ * p ∈ P := P.mul_mem (P.inv_mem (hVP v.property)) hp
    simpa only [mul_inv_cancel_left] using
      (mul_mem_sup v.property (show (v : G)⁻¹ * p ∈ P ⊓ centralizer (L : Set G) from ⟨hvP,hv⟩))
  · exact sup_le hVP inf_le_left

open scoped IsMulCommutative in
/-- The central splitting of S in 11.5.7, on the original three-conjugate core. -/
theorem threeCore_split
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    threeCore E x y = V ⊔ (threeCore E x y ⊓ centralizer (L : Set G)) := by
  let := threeCore_elementary E d hUT hf hc
  exact split_of_commutator E d _
    ((d.central_first_of_source hUT hf).trans inf_le_left)
    (threeCore_commutator E d hUT hf hc).le
    ((threeCore E x y).le_centralizer.trans
      (centralizer_le (componentCore_le_threeCore E d hUT hf)))

/-- Faithfulness identifies the centralizer of V inside the original I. -/
theorem threeGroup_chosen_centralizer
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    threeGroup E x y ⊓ centralizer (V : Set G) = threeCore E x y := by
  apply le_antisymm
  · intro a ha
    let i : I (setup E) x y := ⟨a,ha.1⟩
    have he : d.sourceCoreQuotientEquiv hUT hf
        (QuotientGroup.mk' (pCore 2 (I (setup E) x y)) i) = 1 := by
      apply Matrix.SpecialLinearGroup.toLin'_injective
      rw [map_one]
      ext w : 1
      obtain ⟨v,rfl⟩ := d.coordinates.surjective (Multiplicative.ofAdd w)
      change _ *ᵥ (d.coordinates v).toAdd = (d.coordinates v).toAdd
      rw [← d.sourceCoreQuotientEquiv_equivariant hUT hf i v]
      congr 2
      apply Subtype.ext
      change a * (v : G) * a⁻¹ = (v : G)
      rw [← ha.2 v v.property, mul_inv_cancel_right]
    have hk : i ∈ pCore 2 (I (setup E) x y) := by
      apply (QuotientGroup.eq_one_iff i).mp
      exact (d.sourceCoreQuotientEquiv hUT hf).injective
        (he.trans (map_one _).symm)
    exact mem_map_of_mem _ hk
  · exact le_inf (pCoreIn_le _ _)
      (le_centralizer_iff.mp ((d.central_first_of_source hUT hf).trans inf_le_right))

/-- The central factor in S is exactly C_U(L). -/
theorem threeCore_centralizer
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    threeCore E x y ⊓ centralizer (L : Set G) = E.W ⊓ centralizer (L : Set G) := by
  apply le_antisymm (inf_le_inf_right _ (hc.le.trans (triple_le_closure E x y)))
  intro u hu
  refine ⟨?_,hu.2⟩
  apply (threeGroup_chosen_centralizer E d hUT hf).le
  exact ⟨(threeGroup_eq_join d hUT hf).ge (mem_sup_right hu.1),
    centralizer_le D.le_component hu.2⟩

/-- The literal U-factor in the central splitting is abelian. -/
theorem closure_centralizer_elementary
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    IsElementaryAbelian 2 ↥(E.W ⊓ centralizer (L : Set G)) := by
  rw [← threeCore_centralizer E d hUT hf hc]
  let := threeCore_elementary E d hUT hf hc
  exact IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)

/-- All of I is obtained from L and its own two-core. -/
theorem threeGroup_eq_component_sup_core
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    threeGroup E x y = L ⊔ threeCore E x y := by
  apply le_antisymm
  · intro a ha
    let i : I (setup E) x y := ⟨a,ha⟩
    let q := QuotientGroup.mk' (pCore 2 (I (setup E) x y))
    obtain ⟨z,hz⟩ := d.model.surjective (d.sourceCoreQuotientEquiv hUT hf (q i))
    obtain ⟨l,hl⟩ := starProjection_surjective (setup E) z
    have he : q (inclusion (d.L_le_I hUT hf) l) = q i := by
      apply (d.sourceCoreQuotientEquiv hUT hf).injective
      rw [d.sourceCoreQuotientEquiv_on_L hUT hf,hl,hz]
    have hk : (inclusion (d.L_le_I hUT hf) l)⁻¹ * i ∈ pCore 2 (I (setup E) x y) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ((inclusion (d.L_le_I hUT hf) l)⁻¹ * i) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hm : (l : G)⁻¹ * a ∈ threeCore E x y := mem_map_of_mem _ hk
    simpa only [mul_inv_cancel_left] using mul_mem_sup (show (l : G) ∈ L from l.property) hm
  · exact sup_le (d.L_le_I hUT hf) (pCoreIn_le _ _)

/-- S=S₂ and H¹=0 give the original closure U=(U∩L)C_U(L). -/
theorem closure_split
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    E.W = (E.W ⊓ L) ⊔ (E.W ⊓ centralizer (L : Set G)) := by
  let C := E.W ⊓ centralizer (L : Set G)
  have hS : threeCore E x y = V ⊔ C := by
    rw [threeCore_split E d hUT hf hc,threeCore_centralizer E d hUT hf hc]
  have hI : threeGroup E x y = L ⊔ C := by
    rw [threeGroup_eq_component_sup_core E d hUT hf,hS,←sup_assoc,
      sup_eq_left.mpr D.le_component]
  apply le_antisymm
  · intro u hu
    have hm : u ∈ (C : Set G) * (L : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right C L
        (inf_le_right.trans (centralizer_le_normalizer _)),sup_comm,←hI]
      exact (threeGroup_eq_join d hUT hf).ge (mem_sup_right hu)
    obtain ⟨c,hc,l,hl,he⟩ := hm
    have hlU : l ∈ E.W := by
      have hh := E.W.mul_mem (E.W.inv_mem hc.1) hu
      simpa only [← he,inv_mul_cancel_left] using hh
    rw [←he]
    exact (E.W ⊓ L ⊔ C).mul_mem (mem_sup_right hc) (mem_sup_left ⟨hlU,hl⟩)
  · exact sup_le inf_le_left inf_le_left

open scoped IsMulCommutative in
/-- The two-core of the original L has the same central splitting. -/
theorem componentCore_split
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    L.pCoreIn 2 = V ⊔ (L.pCoreIn 2 ⊓ centralizer (L : Set G)) := by
  let := threeCore_elementary E d hUT hf hc
  have hCS := componentCore_le_threeCore E d hUT hf
  exact split_of_commutator E d _ D.le_componentCore
    (componentCore_commutator E d hUT hf hc).le
    (hCS.trans ((threeCore E x y).le_centralizer.trans (centralizer_le hCS)))

open scoped IsMulCommutative in
/-- The central supplement is central in U, not just fixed by L. -/
theorem closure_centralizer_central
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    E.W ⊓ centralizer (L : Set G) ≤ centralizer (E.W : Set G) := by
  let C := E.W ⊓ centralizer (L : Set G)
  let := closure_centralizer_elementary E d hUT hf hc
  apply le_centralizer_iff.mpr
  apply (closure_split E d hUT hf hc).le.trans
  exact sup_le (inf_le_right.trans (le_centralizer_iff.mp
    (show C ≤ centralizer (L : Set G) from inf_le_right))) C.le_centralizer

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
