module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.BorelGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairNatural
public import Theory.Representation.NormalComponentConstituents
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
/-!
# Excluding the larger-field paired natural chief action

The marked product in the original two-factor alternative identifies each
literal factor with SL₂ over the same binary field. Its first and second
coordinate maps come from the marked action on the quotient by the offender
subgroup's fixed space. The embedded factors are actual simple components.
When the field has at least four elements, the source residual-centralizer
hypothesis forces both Borel normalizers to fix a seed from V, and hence both
natural coordinates vanish. Faithfulness and irreducibility make the quotient
map injective, so the original seed vanishes too.

Thus a nonzero source seed forces the paired natural field to be binary. The
seed's construction and its identification with the relevant chief action
remain with the source assembly; no replacement classification witness is used.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, proof of 3.1.9(5), printed p.578.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter3
open ChapterB QuasisimpleSource SourceInduction Theory.GroupTheory HigherFieldBorelFixedSpaces

private def firstEquiv {Y K : Type*} [Group Y] [Group K]
    (e : Y ≃* K × K) (A : Subgroup Y)
    (hA : ((⊤ : Subgroup K).prod ⊥).map e.symm.toMonoidHom = A) : A ≃* K :=
  (MulEquiv.subgroupCongr hA.symm).trans
    ((e.symm.subgroupMap ((⊤ : Subgroup K).prod ⊥)).symm.trans
      (((⊤ : Subgroup K).prodEquiv ⊥).trans (MulEquiv.prodUnique.trans Subgroup.topEquiv)))

private theorem firstEquiv_apply {Y K : Type*} [Group Y] [Group K]
    (e : Y ≃* K × K) (A : Subgroup Y)
    (hA : ((⊤ : Subgroup K).prod ⊥).map e.symm.toMonoidHom = A) (a : A) :
    firstEquiv e A hA a = (e a).1 := by rfl

private def secondEquiv {Y K : Type*} [Group Y] [Group K]
    (e : Y ≃* K × K) (A : Subgroup Y)
    (hA : ((⊥ : Subgroup K).prod ⊤).map e.symm.toMonoidHom = A) : A ≃* K :=
  (MulEquiv.subgroupCongr hA.symm).trans
    ((e.symm.subgroupMap ((⊥ : Subgroup K).prod ⊤)).symm.trans
      (((⊥ : Subgroup K).prodEquiv ⊤).trans
        (MulEquiv.prodComm.trans (MulEquiv.prodUnique.trans Subgroup.topEquiv))))

private theorem secondEquiv_apply {Y K : Type*} [Group Y] [Group K]
    (e : Y ≃* K × K) (A : Subgroup Y)
    (hA : ((⊥ : Subgroup K).prod ⊤).map e.symm.toMonoidHom = A) (a : A) :
    secondEquiv e A hA a = (e a).2 := by rfl

private theorem naturalFactor_structure {D : Type*} [Group D] [Finite D]
    (Y : Subgroup D) [Y.Normal] (A : Subgroup Y) [A.Normal]
    (F : BinaryField) (hF : 4 ≤ Nat.card F.Carrier) (e : A ≃* SL(2,F.Carrier)) :
    IsSimpleGroup (A.map Y.subtype) ∧ IsComponent D (A.map Y.subtype) ∧
      2 ∣ Nat.card (A.map Y.subtype) := by
  let : IsSimpleGroup PSL(2,F.Carrier) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  let : IsSimpleGroup SL(2,F.Carrier) := Atlas.RankOneFieldAutomorphisms.slEquivPSL.isSimpleGroup
  let : Group.IsPerfect SL(2,F.Carrier) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier (by omega)
  let : IsQuasisimple SL(2,F.Carrier) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F.Carrier))).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  let em := A.equivMapOfInjective Y.subtype Y.subtype_injective
  let ec := em.symm.trans e
  let : IsSimpleGroup (A.map Y.subtype) := ec.isSimpleGroup
  let : IsQuasisimple (A.map Y.subtype) := IsQuasisimple.of_mulEquiv ec.symm
  refine ⟨inferInstance, ⟨(inferInstance : A.Normal).isSubnormal.trans'
    (inferInstance : Y.Normal).isSubnormal, inferInstance⟩, ?_⟩
  rw [Nat.card_congr ec.toEquiv]
  apply dvd_trans (b := Nat.card (upperUnipotent F.Carrier))
  · rw [card_upperUnipotent, F.card_eq]
    exact dvd_pow_self 2 F.degree_pos.ne'
  · exact (upperUnipotent F.Carrier).card_subgroup_dvd_card

variable {G D W : Type*} [Group G] [Finite G] [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- Both literal source factors force the original seed to vanish over a larger field. -/
theorem QrcHypotheses.paired_natural_fixed_seed_zero
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤
      centralizer (V : Set G))
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) (v : W)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (hF : 4 ≤ Nat.card F.Carrier)
    (c : d.MarkedProduct (linearNatural F 2)) : v = 0 := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  let := d.product.first_normal
  let := d.product.second_normal
  let e₁ := firstEquiv c.action.groupEquiv d.first c.first_eq
  let e₂ := secondEquiv c.action.groupEquiv d.second c.second_eq
  let m₁ := d.first.equivMapOfInjective Y.subtype Y.subtype_injective
  let m₂ := d.second.equivMapOfInjective Y.subtype Y.subtype_injective
  let f := c.action.linearEquiv.toLinearMap.comp (fixed (ρ.comp Y.subtype)).toSubmodule.mkQ
  let f₁ := (LinearMap.fst (ZMod 2) (Fin 2 → F.Carrier) (Fin 2 → F.Carrier)).comp f
  let f₂ := (LinearMap.snd (ZMod 2) (Fin 2 → F.Carrier) (Fin 2 → F.Carrier)).comp f
  have hf : ∀ g : Y, ∀ w, f (ρ (g : D) w) =
      (linearNatural F 2 ((c.action.groupEquiv g).1) ((f w).1),
       linearNatural F 2 ((c.action.groupEquiv g).2) ((f w).2)) := by
    intro g w
    exact (congrArg c.action.linearEquiv
      ((fixed (ρ.comp Y.subtype)).quotientRepresentation_mk g w).symm).trans
        (c.action.intertwines g _)
  have hf₁ : ∀ (g : d.first.map Y.subtype) w,
      f₁ (ρ (g : D) w) = binaryNatural 2 ((m₁.symm.trans e₁) g) (f₁ w) := by
    intro g w
    obtain ⟨a,rfl⟩ := m₁.surjective g
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change (f (ρ (a : Y) w)).1 = linearNatural F 2 (e₁ a) ((f w).1)
    rw [hf]
    rw [show e₁ a = (c.action.groupEquiv a).1 from firstEquiv_apply _ _ _ _]
  have hf₂ : ∀ (g : d.second.map Y.subtype) w,
      f₂ (ρ (g : D) w) = binaryNatural 2 ((m₂.symm.trans e₂) g) (f₂ w) := by
    intro g w
    obtain ⟨a,rfl⟩ := m₂.surjective g
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change (f (ρ (a : Y) w)).2 = linearNatural F 2 (e₂ a) ((f w).2)
    rw [hf]
    rw [show e₂ a = (c.action.groupEquiv a).2 from secondEquiv_apply _ _ _ _]
  obtain ⟨hs₁,hL₁,he₁⟩ := naturalFactor_structure Y d.first F hF e₁
  obtain ⟨hs₂,hL₂,he₂⟩ := naturalFactor_structure Y d.second F hF e₂
  let := hs₁
  let := hs₂
  have h₁ := h.natural_component_fixed_seed_coordinate_zero hP hres q hq hc hn ρ v hv
    hL₁ he₁ hF (m₁.symm.trans e₁) f₁ hf₁
  have h₂ := h.natural_component_fixed_seed_coordinate_zero hP hres q hq hc hn ρ v hv
    hL₂ he₂ hF (m₂.symm.trans e₂) f₂ hf₂
  have hz : f v = 0 := Prod.ext h₁ h₂
  have hY : Y ≠ ⊥ := by
    let : IsSimpleGroup d.first := m₁.isSimpleGroup
    let : Nontrivial Y := Function.Injective.nontrivial d.first.subtype_injective
    exact (Subgroup.nontrivial_iff_ne_bot Y).mp inferInstance
  have hfix : (fixed (ρ.comp Y.subtype)).toSubmodule = ⊥ :=
    fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hfaith hirr Y hY
  have hquot : (fixed (ρ.comp Y.subtype)).toSubmodule.mkQ v = 0 :=
    c.action.linearEquiv.injective (hz.trans c.action.linearEquiv.map_zero.symm)
  have hm : v ∈ (fixed (ρ.comp Y.subtype)).toSubmodule :=
    (Submodule.Quotient.mk_eq_zero _).mp hquot
  simpa only [hfix, Submodule.mem_bot] using hm

/-- A nonzero source seed restricts the marked paired natural action to the binary field. -/
theorem QrcHypotheses.paired_natural_field_degree_eq_one
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤
      centralizer (V : Set G))
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) (v : W) (hv0 : v ≠ 0)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2)) : F.degree = 1 := by
  by_contra hdeg
  have hd : 2 ≤ F.degree := by have := F.degree_pos; omega
  have hF : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hd
  exact hv0 (h.paired_natural_fixed_seed_zero hP hres q hq hc hn ρ hfaith hirr v hv d F hF c)

end CFSG.Quasithin.Chapter3
