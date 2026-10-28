module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceDualGeometry
public import Theory.GroupTheory.Commutator.CentralRow
public import Theory.Representation.BinaryOffender.QuadraticDualOffender

/-!
# The genuine dual-FF alternative in D.1.4

The single-vector commutator identity bounds |[U,Q]| by the actual image
of Q on V. Its displacements span a subspace of [U,Q], and Q acts
quadratically. The literal nontrivial Q image inside Aut_G₁(V) is therefore
an offender on the dual of the original faithful representation.
If this alternative fails, Q centralizes V, proving relative normality
of R∩R₂ and elementary structure of U. Residual generation and the later
Thompson and FF conclusions remain the following source stage.
Source: Aschbacher–Smith, D.1.4, printed pp.175–176.
-/

public section
namespace CFSG.Quasithin.ChapterD.UniqueFactor
open Subgroup
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}
theorem coreClosure_normalizes_seed (d : QRCConfiguration G₁ G₂ T V) :
    intersectionClosure G₁ G₂ ≤ normalizer (V : Set G) :=
  (((intersectionClosure_le_right_core.trans (right_core_le_sylow d)).trans
    (sylow_le_left d)).trans d.module_normalized)

theorem source_coreClosure_card_le_actionImage
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V) :
    Nat.card (⁅conjugateSpan G₂ V, intersectionClosure G₁ G₂⁆ : Subgroup G) ≤
      Nat.card (internalActionImage (intersectionClosure G₁ G₂) V (coreClosure_normalizes_seed d)) := by
  let Q := intersectionClosure G₁ G₂
  let := d.finite_right
  have hQH : Q ≤ G₂ := intersectionClosure_le_right_core.trans (twoCore_le G₂)
  let : Finite Q := Finite.of_injective (inclusion hQH) (inclusion_injective hQH)
  obtain ⟨v,hv,_,he,hc,_⟩ := source_coreClosure_commutator_geometry d hV hu
  have hcentral : ⁅zpowers v,Q⁆ ≤ centralizer (Q : Set G) :=
    he.symm.le.trans (hc.trans (le_centralizer_iff.mp (coreClosure_centralizes_seed_fixed d)))
  have hvQ : v ∈ Q := (span_le_intersectionClosure d hV) ((le_conjugateSpan G₂ V) hv)
  rw [he]
  apply card_central_commutator_le_range Q hvQ hcentral (actionHom Q V (coreClosure_normalizes_seed d))
  intro q hq
  rw [actionHom_ker] at hq
  exact hq v hv
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}
theorem source_dualFF_of_coreClosure_not_centralizes
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V)
    (hnc : ¬ intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) : DualFF d := by
  let := d.module_elementary
  let := d.finite_left
  let : Finite V := Finite.of_injective (inclusion d.module_le) (inclusion_injective d.module_le)
  let Q := intersectionClosure G₁ G₂
  let f := actionHom Q V (coreClosure_normalizes_seed d)
  let J := internalActionImage G₁ V d.module_normalized
  let L := f.range
  have hQG₁ : Q ≤ G₁ := (intersectionClosure_le_right_core.trans
    (right_core_le_sylow d)).trans (sylow_le_left d)
  have hLJ : L ≤ J := by
    rintro a ⟨q,rfl⟩
    exact ⟨⟨q,hQG₁ q.property⟩,rfl⟩
  let A : Subgroup J := L.subgroupOf J
  let ρ := imageRepresentation G₁ V d.module_normalized
  have hact (a : J) (ha : a ∈ A) : ∃ q : Q, ∀ w : Additive V,
      ((ρ a w).toMul : G) = (q : G) * (w.toMul : G) * (q : G)⁻¹ := by
    obtain ⟨q,hq⟩ := ha
    refine ⟨q, ?_⟩
    intro w
    change ((J.subtype a w.toMul : V) : G) = _
    rw [← hq]
    rfl
  have hAne : A ≠ ⊥ := by
    intro he
    apply hnc
    intro q hq
    let q0 : Q := ⟨q,hq⟩
    let a : J := ⟨f q0,hLJ ⟨q0,rfl⟩⟩
    have ha : a ∈ A := ⟨q0,rfl⟩
    have ha1 : a = 1 := mem_bot.mp (he ▸ ha)
    have hq1 : f q0 = 1 := congrArg Subtype.val ha1
    have hk : q0 ∈ (centralizer (V : Set G)).subgroupOf Q := by
      rw [← actionHom_ker Q V (coreClosure_normalizes_seed d)]
      exact MonoidHom.mem_ker.mpr hq1
    exact hk
  let C := ⁅conjugateSpan G₂ V,Q⁆
  obtain ⟨v,hv,_,_,hCD,hCquad⟩ := source_coreClosure_commutator_geometry d hV hu
  have hCV : C ≤ V := hCD.trans inf_le_left
  have hCc : C ≤ centralizer (Q : Set G) := commutator_eq_bot_iff_le_centralizer.mp hCquad
  have hdispl (a : J) (ha : a ∈ A) (w : Additive V) :
      ((ρ a w - w).toMul : G) ∈ C := by
    obtain ⟨q,hq⟩ := hact a ha
    change ((ρ a w).toMul : G) / (w.toMul : G) ∈ C
    rw [hq]
    have hm : ⁅(q : G),(w.toMul : G)⁆ ∈ C := by
      change ⁅(q : G),(w.toMul : G)⁆ ∈ ⁅conjugateSpan G₂ V,Q⁆
      rw [commutator_comm]
      exact (commutator_mono le_rfl (le_conjugateSpan G₂ V))
        (commutator_mem_commutator q.property w.toMul.property)
    simpa only [commutatorElement_def, div_eq_mul_inv] using hm
  have hquadratic : IsQuadratic ρ A := by
    intro a ha b hb w
    obtain ⟨q,hq⟩ := hact a ha
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hq]
    exact mul_inv_eq_iff_eq_mul.mpr (hCc (hdispl b hb w) q q.property)
  let W : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 (C.subgroupOf V).toAddSubgroup
  have hker : Coinvariants.ker (ρ.comp A.subtype) ≤ W := by
    rw [Coinvariants.ker, Submodule.span_le]
    rintro w ⟨⟨a,x⟩,rfl⟩
    exact hdispl a a.property x
  let e : W ≃ C :=
    { toFun := fun w => ⟨w.val.toMul,w.property⟩
      invFun := fun c => ⟨Additive.ofMul ⟨c,hCV c.property⟩,c.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hWcard : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
  have hWlog : Module.finrank (ZMod 2) W = Nat.log 2 (Nat.card C) := by
    rw [← Nat.card_congr e,hWcard,Nat.log_pow (by decide : 1 < 2)]
  have hAc : Nat.card A = Nat.card L := Nat.card_congr (subgroupOfEquivOfLe hLJ).toEquiv
  have hcard : Nat.card C ≤ Nat.card L := source_coreClosure_card_le_actionImage d hV hu
  have hdim : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp A.subtype)) ≤ rank A := by
    calc
      _ ≤ Module.finrank (ZMod 2) W := Submodule.finrank_mono hker
      _ = Nat.log 2 (Nat.card C) := hWlog
      _ ≤ Nat.log 2 (Nat.card L) := Nat.log_monotone hcard
      _ = rank A := by rw [rank,hAc]
  exact ⟨A, dual_offender_of_quadratic_moved_bound ρ
    (imageRepresentation_injective G₁ V d.module_normalized) A hAne hquadratic hdim⟩
theorem source_dualFF_or_coreClosure_centralizes
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V) :
    DualFF d ∨ intersectionClosure G₁ G₂ ≤ centralizer (V : Set G) := by
  by_cases hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)
  · exact Or.inr hc
  · exact Or.inl (source_dualFF_of_coreClosure_not_centralizes d hV hu hc)

theorem source_dualFF_or_normal_elementary
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V) :
    DualFF d ∨
      (G₂ ≤ normalizer ((twoCoreIn G₁ ⊓ twoCoreIn G₂ : Subgroup G) : Set G) ∧
        IsElementaryAbelian 2 (conjugateSpan G₂ V)) := by
  rcases source_dualFF_or_coreClosure_centralizes d hV hu with hf | hc
  · exact Or.inl hf
  · exact Or.inr ⟨intersection_normalized_of_centralizes d hc,
      span_elementary_of_centralizes d hV hc⟩

end CFSG.Quasithin.ChapterD.UniqueFactor
