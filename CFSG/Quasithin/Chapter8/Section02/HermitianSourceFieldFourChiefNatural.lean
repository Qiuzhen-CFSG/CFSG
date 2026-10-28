module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourChief

/-!
# The original natural section survives in the moved chief quotient

Transitivity of SL₂(4) on the nonzero vectors makes every invariant
interval in the marked B₀/U trivial or full. If a normalized section has
nontrivial displacement confined to B₀, this forces B₀ into its numerator
and makes its denominator intersect B₀ in exactly U. The full natural
section therefore survives, with its original field and action coordinates.
Faithfulness of the natural SL₂ action also identifies its full kernel
with O₂(R).

The companion Chapter 12 theorem applies these facts to the actual RH-chief
section moved by the original V, and identifies its R-kernel exactly.
Source: Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree
open scoped IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Normalizer.SmallOvergroups
variable {G : Type*} [Group G]
set_option backward.isDefEq.respectTransparency false

/-- An invariant interval in the original natural section has no intermediate subgroup. -/
theorem NaturalSectionAction.invariant_interval {R W U : Subgroup G}
    (h : NaturalSectionAction R W U) (D : Subgroup G)
    (hUD : U ≤ D) (hDW : D ≤ W) (hRD : R ≤ normalizer (D : Set G)) :
    D = U ∨ D = W := by
  obtain ⟨hRW,hRU,hUW,eW,eR,he⟩ := h
  let := hUW
  let p := eW.toMonoidHom.comp (QuotientGroup.mk' (U.subgroupOf W))
  have hk : p.ker = U.subgroupOf W := by
    ext w
    change eW (QuotientGroup.mk' (U.subgroupOf W) w) = 1 ↔ _
    rw [eW.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff w
  let C := (D.subgroupOf W).map p
  have hi : ∀ g w, w ∈ C → Matrix.SL2.naturalAction (E 1) g w ∈ C := by
    intro g w hw
    obtain ⟨r,hr⟩ := (eR.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 R))) g
    change eR (QuotientGroup.mk' (pCore 2 R) r) = g at hr
    obtain ⟨d,hd,rfl⟩ := hw
    let d' := W.normalizerMonoidHom (inclusion hRW r) d
    refine ⟨d', (mem_normalizer_iff.mp (hRD r.property) d.val).mp hd,?_⟩
    change eW (QuotientGroup.mk' (U.subgroupOf W) d') = _
    rw [←sectionAction_apply R W U hRW hRU r d,he]
    rw [hr]
    rfl
  rcases Matrix.SL2.naturalAction_irreducible (E 1) C hi with hb | ht
  · left
    apply le_antisymm _ hUD
    intro d hd
    have hh : p ⟨d,hDW hd⟩ ∈ C := mem_map_of_mem p hd
    rw [hb] at hh
    have hker : (⟨d,hDW hd⟩ : W) ∈ p.ker := mem_bot.mp hh
    rw [hk] at hker
    exact hker
  · right
    have hkd : p.ker ≤ D.subgroupOf W := by rw [hk]; exact fun _ hu => hUD hu
    have hdtop : D.subgroupOf W = ⊤ := by
      have hh := congrArg (comap p) ht
      rw [comap_map_eq_self hkd,comap_top] at hh
      exact hh
    exact le_antisymm hDW (subgroupOf_eq_top.mp hdtop)

/-- Nontrivial movement confined to the original natural section forces that
whole section to survive, retaining exactly its original denominator U. -/
theorem NaturalSectionAction.survives_moved_interval {R W U : Subgroup G}
    (h : NaturalSectionAction R W U) (hUW : U ≤ W)
    (N D A : Subgroup G) (hUD : U ≤ D) (hDN : D ≤ N)
    (hRN : R ≤ normalizer (N : Set G)) (hRD : R ≤ normalizer (D : Set G))
    (hAN : A ≤ normalizer (N : Set G))
    (hmove : ⁅N,A⁆ ≤ W) (hne : ¬ ⁅N,A⁆ ≤ D) :
    W ≤ N ∧ W ⊓ D = U := by
  have hWN := h.invariant_interval (W ⊓ N) (le_inf hUW (hUD.trans hDN)) inf_le_left
    ((le_inf h.choose hRN).trans inf_normalizer_le_normalizer_inf)
  have hCN : ⁅N,A⁆ ≤ N := le_normalizer_iff_commutator_le_left.mp hAN
  have hwN : W ≤ N := by
    rcases hWN with hu | hw
    · exact (hne ((le_inf hmove hCN).trans (hu.le.trans hUD))).elim
    · rw [←hw]
      exact inf_le_right
  have hWD := h.invariant_interval (W ⊓ D) (le_inf hUW hUD) inf_le_left
    ((le_inf h.choose hRD).trans inf_normalizer_le_normalizer_inf)
  refine ⟨hwN,hWD.resolve_right ?_⟩
  intro hw
  exact hne (hmove.trans (hw.symm.le.trans inf_le_right))



/-- The original natural section detects exactly the full two-core of R. -/
theorem NaturalSectionAction.kernel {R W U : Subgroup G}
    (h : NaturalSectionAction R W U) (r : R) :
    (∀ w : W, ⁅(r : G),(w : G)⁆ ∈ U) ↔ r ∈ pCore 2 R := by
  obtain ⟨hRW,hRU,hUW,eW,eR,he⟩ := h
  let := hUW
  let f := sectionAction R W U hRW hRU
  rw [←mem_sectionAction_ker R W U hRW hRU r]
  constructor
  · intro hr
    have ha : Matrix.SL2.naturalAction (E 1) (eR (QuotientGroup.mk' (pCore 2 R) r)) = 1 := by
      apply MulEquiv.ext
      intro x
      obtain ⟨w,rfl⟩ := eW.surjective x
      rw [←he]
      exact congrArg eW (MulEquiv.congr_fun hr w)
    have heq : eR (QuotientGroup.mk' (pCore 2 R) r) = 1 :=
      Matrix.SL2.naturalAction_injective (E 1) (ha.trans (map_one _).symm)
    apply (QuotientGroup.eq_one_iff r).mp
    exact eR.map_eq_one_iff.mp heq
  · intro hr
    have hqr : QuotientGroup.mk' (pCore 2 R) r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    apply MulEquiv.ext
    intro w
    apply eW.injective
    rw [he,hqr,map_one,map_one]
    rfl

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
