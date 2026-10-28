module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaStructure.ThompsonCenter
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.Representation.BinaryGroupAction
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Full Sylow images and Campbell commutator identities in every field

In the binary case, the faithful actual quotient action on the four-group
identifies the entire local quotient with its six automorphisms, hence with
SL₂ over the marked field. Together with the large-field action this supplies
an equivariant natural projection for every original C.1.17 group over a
Baumann-fixed base. The sharp maximum-elementary image theorem then gives
A O₂(H)=S for every maximum elementary A outside the core. Since the core
centralizes V, the literal commutators [A,F], [A,V], [J(S),F] and [S,V]
coincide. No separate full-quotient action premise remains.

Source: Campbell, *Pushing up in Finite Groups* (1979), II.3.2(iii) and
II.4.5(i), printed pp.24–26; Aschbacher–Smith C.1.17–18, printed p.126.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}
 {F : Type} [Field F] [CharP F 2] [Finite F]

theorem InLocalClass.exists_binary_campbell_projection (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (hF : Nat.card F = 2) :
    ∃ (q : H →* SL(2,F)) (f : moved e →* Multiplicative (Fin 2 → F)),
      Function.Surjective q ∧ q.ker = localKernel e ∧ Function.Surjective f ∧
      ∀ (g : H) (w : moved e), (f (movedConjugate e g w)).toAdd = Matrix.mulVec (q g).val (f w).toAdd := by
  classical
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let _ : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let _ : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  let P := Multiplicative (Fin 2 → F)
  let : IsElementaryAbelian 2 P := Representation.BinaryGroupAction.elementary
  have hcP : Nat.card P = 4 := by change Nat.card (Fin 2 → F) = 4; rw [Nat.card_fun,hF]; norm_num
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcP]; decide)
  let : IsKleinFour P := ⟨hcP,IsElementaryAbelian.exponent_eq_prime⟩
  have hcL : Nat.card (LocalStar e) = 6 := h.localStar_card_six_of_field_card_two m hF
  obtain ⟨a⟩ := h.localStar_equiv_psl hB m
  have hcSL : Nat.card SL(2,F) = 6 := by
    rw [← Nat.card_congr (a.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm).toEquiv,hcL]
  let n : SL(2,F) ≃* MulAut P := MulEquiv.ofBijective (Matrix.SL2.naturalAction F)
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨Matrix.SL2.naturalAction_injective _,by
      rw [IsKleinFour.card_mulAut,hcSL]⟩)
  obtain ⟨α,hα⟩ := exists_moved_quotient_action (e := e)
  let β : LocalStar e →* MulAut P := (MulAut.congr m.moduleIso).toMonoidHom.comp α
  let f := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (movedFixed e))
  have hf : Function.Surjective f := m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hβ (g : H) (w : moved e) : β (QuotientGroup.mk' (localKernel e) g) (f w) =
      f (movedConjugate e g w) := by
    change m.moduleIso (α (QuotientGroup.mk' (localKernel e) g)
      (m.moduleIso.symm (m.moduleIso (QuotientGroup.mk' (movedFixed e) w)))) = _
    rw [m.moduleIso.symm_apply_apply,hα]
    rfl
  obtain ⟨ρ,l,hfaith,hl,hcoords,hconj,_,_⟩ := h.exists_faithful_natural_action m
  have hiβ : Function.Injective β := by
    intro x y he
    apply hfaith
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := hf (Multiplicative.ofAdd v)
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (localKernel e) x
    obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (localKernel e) y
    have hc := congrArg (fun b : MulAut P => (b (f w)).toAdd) he
    rw [hβ,hβ] at hc
    change ρ _ (f w).toAdd = ρ _ (f w).toAdd
    change (f (movedConjugate e g w)).toAdd = (f (movedConjugate e j w)).toAdd at hc
    change ρ _ (m.moduleIso (QuotientGroup.mk' (movedFixed e) w)).toAdd =
      ρ _ (m.moduleIso (QuotientGroup.mk' (movedFixed e) w)).toAdd
    rw [←hcoords,←hconj,←hconj,hcoords,hcoords]
    exact hc
  have hsβ : Function.Surjective β :=
    ((Nat.bijective_iff_injective_and_card β).mpr ⟨hiβ,by rw [hcL,IsKleinFour.card_mulAut]⟩).2
  let q := n.symm.toMonoidHom.comp (β.comp (QuotientGroup.mk' (localKernel e)))
  have hq : Function.Surjective q := n.symm.surjective.comp (hsβ.comp (QuotientGroup.mk'_surjective _))
  refine ⟨q,f,hq,?_,hf,?_⟩
  · ext g
    change n.symm (β (QuotientGroup.mk' (localKernel e) g)) = 1 ↔ g ∈ localKernel e
    rw [n.symm.map_eq_one_iff]
    constructor
    · intro hg
      exact (QuotientGroup.eq_one_iff g).mp (hiβ (hg.trans β.map_one.symm))
    · intro hg
      exact (congrArg β ((QuotientGroup.eq_one_iff g).mpr hg)).trans β.map_one
  · intro g w
    have hh := hβ g w
    have hn : n (q g) = β (QuotientGroup.mk' (localKernel e) g) := n.apply_symm_apply _
    rw [←hn] at hh
    exact (congrArg Multiplicative.toAdd hh).symm

theorem InLocalClass.exists_campbell_projection (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) :
    ∃ (q : H →* SL(2,F)) (f : moved e →* Multiplicative (Fin 2 → F)),
      Function.Surjective q ∧ q.ker = localKernel e ∧ Function.Surjective f ∧
      ∀ (g : H) (w : moved e), (f (movedConjugate e g w)).toAdd = Matrix.mulVec (q g).val (f w).toAdd := by
  have ht : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases ht.eq_or_lt with h2 | hl
  · exact InLocalClass.exists_binary_campbell_projection h hB m h2.symm
  · exact h.exists_large_campbell_projection hB m hl

variable {J : Type*} [Group J]
theorem InLocalClass.maxElementary_sup_core_eq_sylow (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) (hAQ : ¬ A ≤ pCore 2 H) :
    A ⊔ pCore 2 H = (d.sylow : Subgroup H) := by
  obtain ⟨q,f,hq,hk,hf,he⟩ := InLocalClass.exists_campbell_projection h hB m
  have hmap := (maxElementary_image_and_index_of_natural_projection h d q hq hk f hf he A hA hAQ).1
  have hSK : (d.sylow : Subgroup H) ⊓ q.ker = pCore 2 H := by
    rw [hk]; exact d.sylow_inf_eq_core _ h.core_le_localKernel h.kernel_noPartialComplement
  apply le_antisymm (sup_le hA.1 (pCore_isPGroup.le_sylow_of_normal d.sylow))
  intro x hx
  have hqx : q x ∈ A.map q := hmap ▸ mem_map_of_mem q hx
  obtain ⟨a,ha,hax⟩ := hqx
  have hi : a⁻¹*x ∈ pCore 2 H := by
    rw [←hSK]
    constructor
    · exact (d.sylow : Subgroup H).mul_mem ((d.sylow : Subgroup H).inv_mem (hA.1 ha)) hx
    · change q (a⁻¹*x) = 1
      rw [map_mul,map_inv,hax,inv_mul_cancel]
  have hh := (A ⊔ pCore 2 H).mul_mem (mem_sup_left ha) (mem_sup_right hi)
  simpa only [mul_inv_cancel_left] using hh

theorem InLocalClass.maxElementary_commutator_V_eq_sylow (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) (hAQ : ¬ A ≤ pCore 2 H) :
    ⁅A,Campbell.V H⁆ = ⁅(d.sylow : Subgroup H),Campbell.V H⁆ := by
  apply le_antisymm (commutator_mono hA.1 le_rfl)
  rw [←InLocalClass.maxElementary_sup_core_eq_sylow h hB m d A hA hAQ]
  apply commutator_le.mpr
  intro x hx v hv
  obtain ⟨a,ha,q,hq,rfl⟩ := mem_sup_of_normal_right.mp hx
  have hC : Campbell.V H ≤ centralizer (pCore 2 H : Set H) :=
    Campbell.V_le_omegaCore.trans (fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
  have hqv : ⁅q,v⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hC hv q hq)
  rw [commutatorElement_mul_left_eq_conj_mul,hqv,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator ha hv

theorem InLocalClass.campbell_commutator_identities (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) (hAQ : ¬ A ≤ pCore 2 H) :
    ⁅A,Campbell.F H⁆ = ⁅(d.sylow : Subgroup H),Campbell.V H⁆ ∧
      ⁅Campbell.J (d.sylow : Subgroup H),Campbell.F H⁆ =
        ⁅(d.sylow : Subgroup H),Campbell.V H⁆ := by
  have ha : ⁅A,Campbell.F H⁆ = ⁅(d.sylow : Subgroup H),Campbell.V H⁆ :=
    (h.maxElementary_commutator_campbellF_eq hB m d A hA).trans
      (InLocalClass.maxElementary_commutator_V_eq_sylow h hB m d A hA hAQ)
  refine ⟨ha,?_⟩
  rw [h.thompson_commutator_campbellF_eq hB m d]
  apply le_antisymm (commutator_mono (sSup_le fun _ hA => hA.1) le_rfl)
  rw [←InLocalClass.maxElementary_commutator_V_eq_sylow h hB m d A hA hAQ]
  exact commutator_mono (le_sSup hA) le_rfl
end CFSG.Quasithin.ChapterC.GlaubermanNiles
