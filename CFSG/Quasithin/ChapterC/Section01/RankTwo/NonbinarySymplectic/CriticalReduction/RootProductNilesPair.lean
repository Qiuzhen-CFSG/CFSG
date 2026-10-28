module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductNormalizer
public import Theory.SpecificGroups.SL2.OriginalSylowPair
public import Theory.GroupTheory.SylowImageCoreKernel

/-!
# The original Niles pair and its literal vertex kernel

For the same F₀ and original Baumann Sylow, the normalized root image has
order at most q, while its abstract SL₂ quotient has Sylow order q. The
index product therefore identifies O₂(F₀) with F₀ intersect Q-alpha. The
entire original U-alpha embeds in its central omega, including all fixed
central attachments. A conjugator in O²(F₀) gives two Baumann Sylows which
generate F₀ and meet exactly in this core, at the unchanged field degree.

Source: MS93 (5.1), printed p.913, and Niles (1979), Lemma 2.2 and
Proposition 4.2, printed pp.29,44. These are original-group inputs to
pushing-up; the Niles commutator conclusion and distance exclusion are
still required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

theorem Input.replacement_root_product_F0_niles_pair
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
      ∃ C : Subgroup (FreeAmalgam d.radical), C ≤ I ∧ (C.subgroupOf I).Normal ∧
        C ⊔ (pCore 2 I).map I.subtype = I ∧
        Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
        generalizedFitting C = pCore 2 C ∧
        (pResidual 2 C).map C.subtype = (pResidual 2 I).map I.subtype ∧
        ∃ P : Sylow 2 C,
          (P : Subgroup C).map C.subtype = Glauberman.baumannSubgroup (Q d.radical t) ∧
          Order.HasUniqueMaximalOver (P : Subgroup C) ⊤ ∧
          NoCharacteristicNormal (P : Subgroup C) ∧
          (pCore 2 C).map C.subtype = C ⊓ Q d.radical a ∧
          U d.radical a ≤ C ∧
          (U d.radical a).subgroupOf C ≤ omegaCenterIn (pCore 2 C) ∧
          Nonempty ((P ⧸ (pCore 2 C).subgroupOf (P : Subgroup C)) ≃* Multiplicative E.Carrier) ∧
          (pCore 2 C).relIndex (P : Subgroup C) = Nat.card F ∧
          ∃ x : C, x ∈ pResidual 2 C ∧
            (P : Subgroup C) ⊔ (P : Subgroup C).map (MulAut.conj x).toMonoidHom = ⊤ ∧
            (P : Subgroup C) ⊓ (P : Subgroup C).map (MulAut.conj x).toMonoidHom = pCore 2 C := by
  obtain ⟨E,hE,f,hf,hfQ,hTn,hE₁f,hE₂f,hJf,hJE⟩ :=
    h.replacement_normalized_root_product d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  obtain ⟨E',hE',I,hI,C,hCI,hCn,hgen,⟨eC⟩,hfit,hres,P,hP,hunique,hno⟩ :=
    h.replacement_root_product_F0_noCharacteristicNormal d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let V := stabilizer d.radical a
  have hCa : C ≤ V := hCI.trans hI
  let := finite_stabilizer d.radical a
  let : Finite C := Finite.of_injective (inclusion hCa) (inclusion_injective hCa)
  let r := eC.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hr : Function.Surjective r := eC.surjective.comp (QuotientGroup.mk'_surjective _)
  have hrk : r.ker = pCore 2 C := by
    ext x
    change eC (QuotientGroup.mk' (pCore 2 C) x) = 1 ↔ _
    rw [eC.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hcard' : Nat.card E'.Carrier = Nat.card F := by rw [E'.card_eq,hE',h.field_card]
  have hidx : (pCore 2 C).relIndex (P : Subgroup C) = Nat.card F :=
    (Matrix.SpecialLinearGroup.sylow_core_relIndex r hr hrk P).trans hcard'
  obtain ⟨j,hj,hjr,hjR,hjQ,_⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hk : IsPGroup 2 f.ker := by
    have hq : IsPGroup 2 (Q d.radical a) := hjQ ▸ pCore_isPGroup.map j
    exact (hfQ.symm ▸ hq).of_injective
      (f.ker.equivMapOfInjective V.subtype V.subtype_injective).toMonoidHom
      (f.ker.equivMapOfInjective V.subtype V.subtype_injective).injective
  let q := f.comp (inclusion hCa)
  have hqk : IsPGroup 2 q.ker := hk.comap_of_injective
    (inclusion hCa) (inclusion_injective hCa)
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F ^ 2)
  obtain ⟨M,hM,hJM,hTh,hBa,_⟩ := h.replacement_root_product_baumann_control
    d geometry hb ha hat E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  have hBJ : Glauberman.baumannSubgroup (Q d.radical t) ≤ J := by
    change _ ≤ Subgroup.SmallMover.join _ _ _ _
    rw [hJM]
    exact hBa
  have hPq : (P : Subgroup C).map q ≤
      (rootFamily (none : Option E.Carrier)).map unipotent.subtype := by
    rintro _ ⟨x,hx,rfl⟩
    have hxB : x.val ∈ Glauberman.baumannSubgroup (Q d.radical t) :=
      hP ▸ mem_map_of_mem C.subtype hx
    exact hJf ▸ mem_map_of_mem f (show inclusion hCa x ∈ J.subgroupOf V from hBJ hxB)
  have hqcore : q.ker = pCore 2 C := by
    apply ker_eq_pCore_of_small_sylow_image q hqk P
    calc
      Nat.card ((P : Subgroup C).map q) ≤
          Nat.card ((rootFamily (none : Option E.Carrier)).map unipotent.subtype) :=
        Nat.card_le_card_of_injective (inclusion hPq) (inclusion_injective hPq)
      _ = Nat.card E.Carrier := by
        rw [Nat.card_congr ((rootFamily (none : Option E.Carrier)).equivMapOfInjective
          unipotent.subtype unipotent.subtype_injective).symm.toEquiv,card_rootFamily]
      _ = (pCore 2 C).relIndex (P : Subgroup C) := by rw [hidx,hcard]
  have hqQ : q.ker = (Q d.radical a).subgroupOf C := by
    ext x
    change f (inclusion hCa x) = 1 ↔ x.val ∈ Q d.radical a
    rw [←hfQ]
    constructor
    · intro hx
      exact mem_map_of_mem V.subtype (show inclusion hCa x ∈ f.ker from hx)
    · rintro ⟨y,hy,he⟩
      have he' : y = inclusion hCa x := Subtype.ext he
      exact he' ▸ hy
  have hcore : (pCore 2 C).map C.subtype = C ⊓ Q d.radical a := by
    rw [←hqcore,hqQ]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · rintro ⟨hx,hq⟩
      exact ⟨⟨x,hx⟩,hq,rfl⟩
  obtain ⟨_,hWe,hWn,hWQ,_,_⟩ := h.replacement_root_product_thompson_layer
    d geometry hb ha hat E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let W := omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a
  let : IsElementaryAbelian 2 W := hWe
  have hWB : W ≤ Glauberman.baumannSubgroup (Q d.radical t) :=
    Glauberman.elementary_layer_le_baumann _ W (hWQ.trans hQT) le_sup_left
  have hUC : U d.radical a ≤ C := by
    have hBC : Glauberman.baumannSubgroup (Q d.radical t) ≤ C := hP ▸ map_subtype_le _
    exact le_sup_right.trans (hWB.trans hBC)
  let U₀ := (U d.radical a).subgroupOf C
  let : IsElementaryAbelian 2 (U d.radical a) := IsElementaryAbelian.of_le
    (show U d.radical a ≤ W from le_sup_right)
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf hUC
  have hUcore : U₀ ≤ pCore 2 C := by
    rw [←hqcore,hqQ]
    exact comap_mono (le_sup_right.trans hWQ)
  have hUomega : U₀ ≤ omegaCenterIn (pCore 2 C) := by
    intro u hu
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hUcore hu,?_,elemPow_eq_one_of_isElementaryAbelian u hu⟩
    intro k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := by
      rw [←hqcore,hqQ] at hk
      exact hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  refine ⟨E',hE',I,hI,C,hCI,hCn,hgen,⟨eC⟩,hfit,hres,P,hP,hunique,hno,
    hcore,hUC,hUomega,?_,hidx,?_⟩
  · exact Matrix.SpecialLinearGroup.sylow_quotient_equiv_additive_of_core_kernel r hr hrk P
  · exact Matrix.SpecialLinearGroup.exists_residual_generating_sylow_pair r hr hrk P

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
