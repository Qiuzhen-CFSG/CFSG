module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy
public import Theory.GroupAction.QuaternionCentralizerPlacement

/-!
# Root coordinates for a self-centralizing order-sixty-four subgroup

For a normal UT₃(F₄) subgroup, self-centralization makes the conjugation
kernel its four-element center and the preimage of the inner automorphisms
exactly the subgroup itself. An overgroup of order 1152 consequently has
image order 288. Its full center action and central cubic quotient coset
transport to the intrinsic automizer invariants. The proved automizer
classification then gives coordinates with the standard inner–actor image.

Source application: DGS, *Groups and Graphs* (1985), (10.9), p.163;
Aschbacher, *Sporadic Groups* (1994), 8.15 and 46.14.
This identifies the action image; it does not assert a split extension.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Four.RootNormalizerModel.SourceAction
variable {A : Type*} [Group A] (Q : Subgroup A) [Q.Normal]

def conjugation (e : Q ≃* Root) : A →* MulAut Root :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : A →* MulAut Q)

theorem kernel (e : Q ≃* Root) :
    (conjugation Q e).ker = centralizer (Q : Set A) := by
  rw [conjugation,MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e).injective,
    MulAut.conjNormal_ker_eq_centralizer]

theorem inner_image (e : Q ≃* Root) :
    Q.map (conjugation Q e) = (MulAut.conj : Root →* MulAut Root).range := by
  apply le_antisymm
  · rintro _ ⟨q,hq,rfl⟩
    refine ⟨e ⟨q,hq⟩,?_⟩
    apply MulEquiv.ext
    intro x
    change e ⟨q,hq⟩ * x * (e ⟨q,hq⟩)⁻¹ = e (MulAut.conjNormal q (e.symm x))
    rw [←e.apply_symm_apply x,←map_mul,←map_inv,←map_mul,e.symm_apply_apply]
    rfl
  · rintro _ ⟨r,rfl⟩
    refine ⟨e.symm r,(e.symm r).property,?_⟩
    apply MulEquiv.ext
    intro x
    change e (MulAut.conjNormal (e.symm r : A) (e.symm x)) = r*x*r⁻¹
    change e (e.symm r * e.symm x * (e.symm r)⁻¹) = _
    rw [map_mul,map_mul,map_inv,e.apply_symm_apply,e.apply_symm_apply]

theorem inner_preimage (e : Q ≃* Root)
    (hc : centralizer (Q : Set A) ≤ Q) :
    ((MulAut.conj : Root →* MulAut Root).range).comap (conjugation Q e) = Q := by
  rw [←inner_image Q e,comap_map_eq_self (by rw [kernel]; exact hc)]

theorem range_card (e : Q ≃* Root)
    (hc : centralizer (Q : Set A) ≤ Q) (hA : Nat.card A = 1152) :
    Nat.card (conjugation Q e).range = 288 := by
  have hcenter : centralizer (Q : Set A) = (center Q).map Q.subtype := by
    apply le_antisymm
    · intro x hx
      exact ⟨⟨x,hc hx⟩,mem_center_iff.mpr (fun y => Subtype.ext (hx y y.property)),rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hk : Nat.card (conjugation Q e).ker = 4 := by
    rw [kernel,hcenter,card_map_of_injective Q.subtype_injective,
      Nat.card_congr (centerCongr e).toEquiv]
    exact AutomizerConjugacy.center_card
  have h := (conjugation Q e).ker.card_mul_index
  rw [hk,index_ker,hA] at h
  omega

theorem invariants (e : Q ≃* Root)
    (hc : centralizer (Q : Set A) ≤ Q) (hA : Nat.card A = 1152)
    (hZ : ∀ b : MulAut (center Q), ∃ a : A,
      ∀ z : center Q, MulAut.conjNormal a z = (b z : Q))
    (hthree : ∃ a : A, a ∉ Q ∧ a ^ 3 ∈ Q ∧ ∀ x : A, ⁅a,x⁆ ∈ Q) :
    AutomizerInvariants (conjugation Q e).range := by
  have hm (a : A) : conjugation Q e a ∈ (MulAut.conj : Root →* MulAut Root).range ↔ a ∈ Q :=
    SetLike.ext_iff.mp (inner_preimage Q e hc) a
  refine ⟨?_,range_card Q e hc hA,?_,?_⟩
  · rw [←inner_image Q e]
    exact map_le_range _ _
  · intro b
    let ec := centerCongr e
    obtain ⟨a,ha⟩ := hZ (MulAut.congr ec.symm b)
    refine ⟨conjugation Q e a,⟨a,rfl⟩,fun z => ?_⟩
    have hz := congrArg e (ha (ec.symm z))
    change e (MulAut.conjNormal a (e.symm (z : Root))) =
      e (e.symm (b (ec (ec.symm z)) : Root)) at hz
    rw [ec.apply_symm_apply,e.apply_symm_apply] at hz
    exact hz
  · obtain ⟨a,ha,ha3,hax⟩ := hthree
    refine ⟨conjugation Q e a,⟨a,rfl⟩,(hm a).not.mpr ha,?_,?_⟩
    · rw [←map_pow,hm]
      exact ha3
    · rintro _ ⟨x,rfl⟩
      rw [←map_commutatorElement,hm]
      exact hax x

theorem exists_adjusted_coordinates (e : Q ≃* Root)
    (hc : centralizer (Q : Set A) ≤ Q) (hA : Nat.card A = 1152)
    (hZ : ∀ b : MulAut (center Q), ∃ a : A,
      ∀ z : center Q, MulAut.conjNormal a z = (b z : Q))
    (hthree : ∃ a : A, a ∉ Q ∧ a ^ 3 ∈ Q ∧ ∀ x : A, ⁅a,x⁆ ∈ Q) :
    ∃ d : Q ≃* Root, (conjugation Q d).range =
      (MulAut.conj : Root →* MulAut Root).range ⊔ actor := by
  obtain ⟨a,ha⟩ := AutomizerConjugacy.exists_adjustment_of_invariants _
    (invariants Q e hc hA hZ hthree)
  refine ⟨e.trans a,?_⟩
  have he : conjugation Q (e.trans a) =
      (MulAut.congr a).toMonoidHom.comp (conjugation Q e) := by
    apply MonoidHom.ext
    intro g
    apply MulEquiv.ext
    intro x
    rfl
  rw [he,MonoidHom.range_comp]
  exact ha

end Matrix.PSL3Four.RootNormalizerModel.SourceAction
