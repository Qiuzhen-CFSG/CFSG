module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel.Swap
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedFive
public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.QuasithinBasic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The swapped paired A₅ action and its Borel stabilizer

The concrete overgroup is (S₅ × S₅) ⋊ C₂, acting on the orthogonal sum of
the two five-point augmentation cores. The action is faithful and the
interchange is the literal linear swap. Component signs give a homomorphism
to (C₂ × C₂) ⋊ C₂, of order eight, with kernel the specified A₅ product.

The point stabilizer in that product is the product of the two actual
point-four stabilizers, with their coordinate-preserving A₄ markings. In
every intermediate overgroup, its quotient is a two-group. Consequently
its two-residual is precisely the embedded Borel product, conditional only
on the stated two-perfectness of A₄ × A₄. Its three-rank transports through
the same isomorphism; the numerical A₄-product rank is a separate input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.11.2(12),
printed p.364, and the Borel calculation in 12.8.13(7), printed p.856.
-/

@[expose] public section
open Subgroup
namespace BinaryPermutation.TerminalOrthogonal.PairedBorel
open PairedFive
abbrev S5 := Equiv.Perm (Fin 5)
abbrev A5 := alternatingGroup (Fin 5)
abbrev A4 := alternatingGroup (Fin 4)
abbrev Model := Swapped S5

noncomputable def factorAction : S5 →* (Factor ≃ₗ[ZMod 2] Factor) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Factor).toMonoidHom.comp
    (coreRepresentation (Fin 5)).asGroupHom

noncomputable def pairAction : (S5 × S5) →* (Space ≃ₗ[ZMod 2] Space) where
  toFun g := LinearEquiv.prodCongr (factorAction g.1) (factorAction g.2)
  map_one' := by ext v <;> simp [factorAction]
  map_mul' g h := by ext v <;> simp [factorAction, map_mul]

def linearSwitch : C2 →* (Space ≃ₗ[ZMod 2] Space) where
  toFun c := if c = 1 then 1 else PairedFive.swap
  map_one' := by simp
  map_mul' c d := by
    change ZMod 2 at c d
    fin_cases c <;> fin_cases d <;> ext v <;> simp <;> rfl

noncomputable def modelAction : Model →* (Space ≃ₗ[ZMod 2] Space) :=
  SemidirectProduct.lift pairAction linearSwitch (by
    intro c
    apply MonoidHom.ext
    intro a
    apply LinearEquiv.ext
    intro v
    change ZMod 2 at c
    fin_cases c <;> simp [switch, linearSwitch, pairAction, MulAut.conj_apply] <;> rfl)

lemma modelAction_base (a b : S5) (v : Space) :
    modelAction (base (a,b)) v =
      (coreRepresentation (Fin 5) a v.1, coreRepresentation (Fin 5) b v.2) := by
  rw [modelAction, base, SemidirectProduct.lift_inl]
  rfl

lemma modelAction_interchange (v : Space) :
    modelAction (interchange : Model) v = PairedFive.swap v := by
  rw [modelAction, interchange, SemidirectProduct.lift_inr]
  simp [linearSwitch]

lemma modelAction_apply (g : Model) (v : Space) :
    modelAction g v = if g.right = 1 then
      (coreRepresentation (Fin 5) g.left.1 v.1, coreRepresentation (Fin 5) g.left.2 v.2)
    else (coreRepresentation (Fin 5) g.left.1 v.2, coreRepresentation (Fin 5) g.left.2 v.1) := by
  change pairAction g.left (linearSwitch g.right v) = _
  by_cases h : g.right = 1 <;> simp [linearSwitch, h, pairAction, factorAction, PairedFive.swap]
  all_goals exact ⟨rfl, rfl⟩

lemma modelAction_form (g : Model) (v : Space) :
    PairedFive.form (modelAction g v) = PairedFive.form v := by
  rw [modelAction_apply]
  split <;> simp [PairedFive.factor_form_invariant, add_comm]

private lemma factorAction_faithful (g : S5)
    (h : ∀ v : Factor, coreRepresentation (Fin 5) g v = v) : g = 1 := by
  have test : ∀ g : S5, (∀ v : Full (Fin 5), (∑ i, v i) = 0 →
      representation (Fin 5) g v = v) → g = 1 := by decide +kernel
  exact test g (fun v hv => congrArg Subtype.val (h ⟨v, hv⟩))

lemma modelAction_injective : Function.Injective modelAction := by
  apply (injective_iff_map_eq_one modelAction).mpr
  intro g hg
  have hact (v : Space) : modelAction g v = v := LinearEquiv.congr_fun hg v
  have hr : g.right = 1 := by
    by_contra hn
    have hh := congrArg Prod.snd (hact (factorPoint, 0))
    rw [modelAction_apply, if_neg hn] at hh
    have hz : factorPoint = 0 := (factorAction g.left.2).injective (by
      rw [map_zero]
      exact hh)
    exact point_ne_zero (Prod.ext hz hz)
  have ha : g.left.1 = 1 := factorAction_faithful _ (fun v => by
    simpa only [modelAction_apply, if_pos hr] using congrArg Prod.fst (hact (v, 0)))
  have hb : g.left.2 = 1 := factorAction_faithful _ (fun v => by
    simpa only [modelAction_apply, if_pos hr] using congrArg Prod.snd (hact (0, v)))
  exact SemidirectProduct.ext (Prod.ext ha hb) hr

def pairedInclusion : Actor →* Model := base.comp (A5.subtype.prodMap A5.subtype)

lemma pairedInclusion_injective : Function.Injective pairedInclusion := by
  intro a b h
  have hh := congrArg SemidirectProduct.left h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh))
    (Subtype.ext (congrArg Prod.snd hh))

lemma modelAction_paired (g : Actor) (v : Space) :
    modelAction (pairedInclusion g) v = PairedFive.action g v :=
  modelAction_base _ _ _

def parity : Model →* Swapped ℤˣ := swappedMap Equiv.Perm.sign

lemma parity_target_twoGroup : IsPGroup 2 (Swapped ℤˣ) := by
  apply IsPGroup.of_card (n := 3)
  rw [SemidirectProduct.card, Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card]

lemma paired_range_eq_ker : pairedInclusion.range = parity.ker := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    apply SemidirectProduct.ext
    · exact Prod.ext a.1.property a.2.property
    · rfl
  · intro h
    have hl := congrArg SemidirectProduct.left h
    have hr := congrArg SemidirectProduct.right h
    refine ⟨(⟨g.left.1, congrArg Prod.fst hl⟩,
      ⟨g.left.2, congrArg Prod.snd hl⟩), ?_⟩
    exact SemidirectProduct.ext rfl hr.symm

instance : pairedInclusion.range.Normal := by
  rw [paired_range_eq_ker]
  infer_instance

abbrev factorBorel := AlternatingFiveBorel.B
def pairedBorel : Subgroup Actor := factorBorel.prod factorBorel

noncomputable def borelEquiv : pairedBorel ≃* A4 × A4 :=
  (Subgroup.prodEquiv _ _).trans
    (MulEquiv.prodCongr AlternatingFiveBorel.marking.symm AlternatingFiveBorel.marking.symm)

lemma mem_pairedBorel (g : Actor) :
    g ∈ pairedBorel ↔ PairedFive.action g point = point :=
  (PairedFive.point_fixed_iff g).symm

noncomputable def pointStabilizer : Subgroup Model where
  carrier := {g | modelAction g point = point}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change modelAction a point = point at ha
    change modelAction b point = point at hb
    change modelAction (a*b) point = point
    rw [map_mul, LinearEquiv.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    apply (modelAction a).injective
    simpa [← LinearEquiv.mul_apply, ← map_mul] using ha.symm

@[simp] lemma mem_pointStabilizer (g : Model) :
    g ∈ pointStabilizer ↔ modelAction g point = point := Iff.rfl

lemma pointStabilizer_coordinates (g : Model) :
    g ∈ pointStabilizer ↔ g.left.1 4 = 4 ∧ g.left.2 4 = 4 := by
  rw [mem_pointStabilizer, modelAction_apply]
  split <;> simp only [point, Prod.mk.injEq, factorPoint_fixed_iff]

def embeddedBorel : Subgroup Model := pairedBorel.map pairedInclusion

lemma embeddedBorel_eq : embeddedBorel = pointStabilizer ⊓ pairedInclusion.range := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨by change modelAction (pairedInclusion a) point = point
              rw [modelAction_paired]; exact (mem_pairedBorel a).mp ha,
      ⟨a, rfl⟩⟩
  · rintro ⟨hg, a, rfl⟩
    refine ⟨a, ?_, rfl⟩
    apply (mem_pairedBorel a).mpr
    exact (modelAction_paired a point).symm.trans hg

noncomputable def embeddedBorelEquiv : embeddedBorel ≃* A4 × A4 :=
  (pairedBorel.equivMapOfInjective pairedInclusion pairedInclusion_injective).symm.trans borelEquiv

noncomputable def stabilizerIn (H : Subgroup Model) : Subgroup H :=
  pointStabilizer.subgroupOf H

noncomputable def stabilizerMap (H : Subgroup Model) : stabilizerIn H →* Model :=
  H.subtype.comp (stabilizerIn H).subtype

noncomputable def borelInclusion (H : Subgroup Model) (hH : pairedInclusion.range ≤ H) :
    pairedBorel →* stabilizerIn H where
  toFun a := ⟨⟨pairedInclusion a, hH ⟨a, rfl⟩⟩, by
    change modelAction (pairedInclusion a) point = point
    rw [modelAction_paired]
    exact (mem_pairedBorel a).mp a.property⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _

lemma borelInclusion_injective (H : Subgroup Model) (hH : pairedInclusion.range ≤ H) :
    Function.Injective (borelInclusion H hH) := by
  intro a b h
  apply Subtype.ext
  apply pairedInclusion_injective
  exact congrArg (fun g : stabilizerIn H => g.val.val) h

lemma borelInclusion_range (H : Subgroup Model) (hH : pairedInclusion.range ≤ H) :
    (borelInclusion H hH).range = (parity.comp (stabilizerMap H)).ker := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    change pairedInclusion a.val ∈ parity.ker
    rw [← paired_range_eq_ker]
    exact ⟨a, rfl⟩
  · intro hg
    have hp : g.val.val ∈ pairedInclusion.range := paired_range_eq_ker.symm ▸ hg
    obtain ⟨a, ha⟩ := hp
    have hb : a ∈ pairedBorel := by
      rw [mem_pairedBorel, ← modelAction_paired, ha]
      exact g.property
    exact ⟨⟨a, hb⟩, Subtype.ext (Subtype.ext ha)⟩

lemma stabilizer_quotient_twoGroup (H : Subgroup Model) :
    IsPGroup 2 (stabilizerIn H ⧸ (parity.comp (stabilizerMap H)).ker) := by
  exact (parity_target_twoGroup.of_injective _
    (parity.comp (stabilizerMap H)).range.subtype_injective).of_equiv
      (QuotientGroup.quotientKerEquivRange (parity.comp (stabilizerMap H))).symm

lemma residual_eq_borel (H : Subgroup Model) (hH : pairedInclusion.range ≤ H)
    (hperfect : pResidual 2 (A4 × A4) = ⊤) :
    pResidual 2 (stabilizerIn H) = (borelInclusion H hH).range := by
  have hB : pResidual 2 pairedBorel = ⊤ := by
    rw [← map_pResidual 2 borelEquiv.symm, hperfect,
      map_top_of_surjective _ borelEquiv.symm.surjective]
  apply le_antisymm
  · rw [borelInclusion_range]
    exact sInf_le ⟨inferInstance, stabilizer_quotient_twoGroup H⟩
  · have h := map_pResidual_le 2 (borelInclusion H hH)
    rw [hB] at h
    rintro g ⟨a, rfl⟩
    exact h ⟨a, mem_top _, rfl⟩

noncomputable def residualEquiv (H : Subgroup Model) (hH : pairedInclusion.range ≤ H)
    (hperfect : pResidual 2 (A4 × A4) = ⊤) :
    pResidual 2 (stabilizerIn H) ≃* A4 × A4 :=
  (MulEquiv.subgroupCongr (residual_eq_borel H hH hperfect)).trans
    ((MonoidHom.ofInjective (borelInclusion_injective H hH)).symm.trans borelEquiv)

lemma residual_threeRank (H : Subgroup Model) (hH : pairedInclusion.range ≤ H)
    (hperfect : pResidual 2 (A4 × A4) = ⊤) (hrank : primeRank 3 (A4 × A4) = 2) :
    primeRank 3 (pResidual 2 (stabilizerIn H)) = 2 := by
  rw [Theory.GroupTheory.primeRank_equiv 3 (residualEquiv H hH hperfect), hrank]

/-- The residual equality in the original overgroup coordinates. -/
lemma residual_map_stabilizer (H : Subgroup Model) (hH : pairedInclusion.range ≤ H)
    (hperfect : pResidual 2 (A4 × A4) = ⊤) :
    (pResidual 2 (stabilizerIn H)).map (stabilizerMap H) = embeddedBorel := by
  rw [residual_eq_borel H hH hperfect]
  ext g
  constructor
  · rintro ⟨s, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨borelInclusion H hH ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩

lemma stabilizer_threeRank_ge (H : Subgroup Model) (hH : pairedInclusion.range ≤ H)
    (hrank : primeRank 3 (A4 × A4) = 2) : 2 ≤ primeRank 3 (stabilizerIn H) := by
  calc
    2 = primeRank 3 pairedBorel :=
      (Theory.GroupTheory.primeRank_equiv 3 borelEquiv).trans hrank |>.symm
    _ ≤ primeRank 3 (stabilizerIn H) :=
      Theory.GroupTheory.primeRank_le_of_injective 3 (borelInclusion H hH)
        (borelInclusion_injective H hH)

end BinaryPermutation.TerminalOrthogonal.PairedBorel
