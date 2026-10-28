module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SeedGeometry
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLinesAt

/-!
# The original amalgam omega seed from guarded structure

The augmentation Sylow fixed-space bound gives at least four vectors in
V intersect Z. Escape and the fixed-hyperplane argument bound all of Z by
four, proving Z=V intersect Z and its splitting into the two fixed lines.
The same-G,T structural premise suffices in both covering rows. This feeds
the equal-core and nonsolvable branches without an assumed omega count.
Source: Aschbacher--Smith 13.4.7(1), printed pp.899--900.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
/-- The original central seed has at least four elements, independently of escape. -/
theorem four_le_original_central_seed_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    4 ≤ Nat.card (V ⊓ omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) := by
  let hn := normalizer_component_le_module_at h structural D m
  obtain ⟨q,he,_,_⟩ := Nonsolvable.exists_core_normalizer_permutation D m hn
  let a : T →* Equiv.Perm (Fin 6) := q.comp (inclusion D.sylow_normalizes_component)
  let P := a.range
  have hP : IsPGroup 2 P := T.isPGroup'.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  have hb := BinaryPermutation.SixCoreSylow.four_le_card_fixed_of_twoGroup P hP
  let Z := V ⊓ omegaOneCenterAmbient (T : Subgroup G)
  let f : fixedSpace (BinaryPermutation.coreRepresentation (Fin 6)) P → Z := fun w =>
    ⟨(m.coordinate.symm (Multiplicative.ofAdd w.val)).val, by
      let v := m.coordinate.symm (Multiplicative.ofAdd w.val)
      refine ⟨v.property,(mem_omegaOneCenterAmbient_iff _ _).mpr ⟨D.le_sylow v.property,?_,?_⟩⟩
      · let := D.elementary
        exact elemPow_eq_one_of_isElementaryAbelian v.val v.property
      · intro t ht
        let t' : T := ⟨t,ht⟩
        have hw := w.property ⟨a t',⟨t',rfl⟩⟩
        have hv := he (inclusion D.sylow_normalizes_component t') v
        have hvcoord : m.coordinate v = Multiplicative.ofAdd w.val :=
          m.coordinate.apply_symm_apply _
        simp only [hvcoord,toAdd_ofAdd] at hv
        have hc : V.normalizerMonoidHom (inclusion hn
            (inclusion D.sylow_normalizes_component t')) v = v := by
          apply m.coordinate.injective
          apply Multiplicative.toAdd.injective
          rw [hvcoord,toAdd_ofAdd]
          exact hv.trans hw
        exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hc)⟩
  have hf : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    have hh := congrArg (fun x : Z => (m.coordinate ⟨x.val,x.property.1⟩).toAdd) hvw
    simpa only [f,m.coordinate.apply_symm_apply,toAdd_ofAdd] using hh
  exact hb.trans (Nat.card_le_card_of_injective f hf)

variable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
include h structural D m hTA hTB eA eB hne hindexL hindexA hindexB hcentral

/-- The initial geometry of 13.4.7(1), for every admitted original pair. -/
theorem original_pair_source_seed_at :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let F₁ := Z ⊓ centralizer (A : Set G)
    let F₂ := Z ⊓ centralizer (B : Set G)
    A ⊔ B ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G) ∧
      Z = V ⊓ Z ∧ Nat.card Z = 4 ∧ Nat.card F₁ = 2 ∧ Nat.card F₂ = 2 ∧
      F₁ ⊓ F₂ = ⊥ ∧ F₁ ⊔ F₂ = Z ∧
      Z ⊓ centralizer (L : Set G) = V ⊓ centralizer (L : Set G) := by
  have ho := original_pair_outside h.toHypothesis1221 D m hTA hTB eA eB hne
    hindexL hindexA hindexB hcentral
  have hd := pair_fixed_subgroups_ne hTA hTB eA eB hne (hcentral ho.1).2.2
  obtain ⟨hZ,hF₁,hF₂,hinf,hsup,hZL⟩ := original_pair_fixed_lines_at h structural D m
    ho.2 hindexL hindexA hindexB hd
  have hs : V ⊓ omegaOneCenterAmbient (T : Subgroup G) =
      omegaOneCenterAmbient (T : Subgroup G) := by
    apply eq_of_le_of_card_ge inf_le_right
    rw [hZ]
    exact four_le_original_central_seed_at h structural D m
  exact ⟨ho,hs.symm,hZ,hF₁,hF₂,hinf,hsup,hZL⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
