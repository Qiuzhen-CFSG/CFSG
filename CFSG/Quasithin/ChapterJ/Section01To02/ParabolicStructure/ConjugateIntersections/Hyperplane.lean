module
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Basic
public import Theory.GroupTheory.QuotientActionCentralizer
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The hyperplane argument in J.2.2(5)

Write A for an L-conjugate of U and assume A ∩ Q ≤ HC. Conjugation by
C_Q(Zα) normalizes A, so [A,C_Q(Zα)] lies in A ∩ Q and vanishes on Q/HC.
The map q ↦ [q,zα] has image in Z of order at most two. Every displacement
of A on the actual dual-natural Q/HC section therefore has binary rank at
most one. Excluding rank one makes the faithful H/Q action trivial, so A ≤ Q.
This also proves A ∩ Q is not contained in HC whenever A leaves Q.

The dual-natural section and absence of rank-one displacements remain
explicit earlier inputs. Their source-theorem assembly owner is
qt-j12-parabolic-structure, with producers qt-j12-quotient-natural and
qt-6-02-natural-semilinear-normalizer. No assertion about distinct conjugates
is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(5), printed pp.432–433 (PDF pp.443–444).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.ConjugateIntersections
open Subgroup Representation
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

/-- No element of the literal dual action has a one-dimensional displacement. -/
def NoRankOne (d : LocalSetup G) : Prop :=
  ∀ g : S5, Module.finrank (ZMod 2)
    (LinearMap.range (d.ru2.naturalAction.action.dual g - LinearMap.id)) ≠ 1

private theorem dual_injective (r : L2FourAction) :
    Function.Injective r.action.dual := by
  intro g h he
  apply inv_injective
  apply r.injective
  apply LinearMap.ext
  intro v
  apply (Module.evalEquiv (ZMod 2) FourSpace).injective
  apply LinearMap.ext
  intro f
  exact congrArg (fun a : Module.Dual (ZMod 2) FourSpace => a v)
    (LinearMap.congr_fun he f)

private def evaluation (d : LocalSetup G) (z : d.toTypeRuSetup.U) :
    d.toTypeRuSetup.Q →* d.toTypeRuSetup.Z where
  toFun q := ⟨⁅(q : G), (z : G)⁆, d.toTypeRuSetup.commutator_Q_U_le_Z
    (commutator_mem_commutator q.property z.property)⟩
  map_one' := Subtype.ext (commutatorElement_one_left _)
  map_mul' a b := by
    apply Subtype.ext
    change ⁅(a : G) * b, (z : G)⁆ = ⁅(a : G), (z : G)⁆ * ⁅(b : G), (z : G)⁆
    have ha := d.toTypeRuSetup.commutator_Q_U_le_Z
      (commutator_mem_commutator a.property z.property)
    have hb := d.toTypeRuSetup.commutator_Q_U_le_Z
      (commutator_mem_commutator b.property z.property)
    have hcentral := (pCoreIn_le 2 d.toTypeRuSetup.H a.property) _ hb
    rw [commutatorElement_mul_left_eq_conj_mul, ← hcentral, mul_inv_cancel_right]
    exact (d.ru2.natural.section_le (d.ru2.natural.kernel_le ha)) _ hb

private theorem zero_of_small_displacement
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (f : Module.End (ZMod 2) W)
    (hc : Nat.card (LinearMap.range f) ≤ 2)
    (hn : Module.finrank (ZMod 2) (LinearMap.range f) ≠ 1) : f = 0 := by
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range f)
  rw [Nat.card_zmod] at hpow
  have hdim : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega :
      2 ≤ Module.finrank (ZMod 2) (LinearMap.range f))
    rw [← hpow] at hh
    omega
  exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))

/-- If the intersection with Q centralizes U, then the conjugate is contained
in Q. The commutator with Zα bounds every displacement on Q/HC by rank one;
the model hypothesis excludes that rank, and faithfulness kills the star image. -/
theorem conjugateU_le_Q_of_inf_le_HC (d : LocalSetup G)
    (sectionQ : BinaryConjugationSection d.toTypeRuSetup.H d.toTypeRuSetup.Q
      d.toTypeRuSetup.HC (d.ru2.naturalAction.action.dual.comp d.ru2.quotientMap))
    (hNoRank : NoRankOne d) (l : G) (hl : l ∈ d.L)
    (hinter : conjugateU d l ⊓ d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.HC) :
    conjugateU d l ≤ d.toTypeRuSetup.Q := by
  let : Finite (Module.Dual (ZMod 2) FourSpace) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) FourSpace => (f : FourSpace → ZMod 2))
      DFunLike.coe_injective
  have htwo : Nat.card (conjugateZ d l) = 2 := by
    rw [conjugateZ, card_map_of_injective (MulAut.conj l).injective, d.card_Z]
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : conjugateZ d l)).mp htwo
  have hzU := (conjugateZ_le_V d l hl).trans (le_conjugateSpan d.toTypeRuSetup.H d.V) z.property
  let ev := evaluation d ⟨z, hzU⟩
  have hnorm (q : d.toTypeRuSetup.Q) (hq : q ∈ ev.ker) :
      (q : G) ∈ normalizer (conjugateU d l) := by
    apply conjugateU_normalized d l
    intro w hw
    by_cases hw1 : w = 1
    · simp [hw1]
    have hwz : w = (z : G) := congrArg Subtype.val
      (huniq ⟨w, hw⟩ (fun he => hw1 (congrArg Subtype.val he)))
    rw [hwz]
    have he : ⁅(q : G), (z : G)⁆ = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hq)
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  intro a ha
  have haH := conjugateU_le_H d l hl ha
  let aH : d.toTypeRuSetup.H := ⟨a, haH⟩
  let D : Module.End (ZMod 2) (Module.Dual (ZMod 2) FourSpace) :=
    d.ru2.naturalAction.action.dual (d.ru2.quotientMap aH) - LinearMap.id
  let δ : d.toTypeRuSetup.Q →* Multiplicative (Module.Dual (ZMod 2) FourSpace) :=
    (AddMonoidHom.toMultiplicative D.toAddMonoidHom).comp sectionQ.coordinates
  have hker : ev.ker ≤ δ.ker := by
    intro q hq
    have hconjQ : a * (q : G) * a⁻¹ ∈ d.toTypeRuSetup.Q :=
      (mem_normalizer_iff.mp (d.ru2.six.normalized haH) q).mp q.property
    have hcommQ : ⁅a, (q : G)⁆ ∈ d.toTypeRuSetup.Q :=
      d.toTypeRuSetup.Q.mul_mem hconjQ (d.toTypeRuSetup.Q.inv_mem q.property)
    have hcommA : ⁅a, (q : G)⁆ ∈ conjugateU d l := by
      have hh := (mem_normalizer_iff.mp (hnorm q hq) a⁻¹).mp
        ((conjugateU d l).inv_mem ha)
      simpa only [commutatorElement_def, mul_assoc] using (conjugateU d l).mul_mem ha hh
    have hc := hinter ⟨hcommA, hcommQ⟩
    let c : d.toTypeRuSetup.Q := ⟨a * (q : G) * a⁻¹, hconjQ⟩
    have he : sectionQ.coordinates c = sectionQ.coordinates q := by
      have hh : sectionQ.coordinates (c * q⁻¹) = 1 :=
        (sectionQ.coordinates_eq_one_iff _).mpr hc
      simpa only [map_mul, map_inv, mul_inv_eq_one] using hh
    have hact := sectionQ.equivariant aH q
    change (sectionQ.coordinates c).toAdd =
      d.ru2.naturalAction.action.dual (d.ru2.quotientMap aH)
        (sectionQ.coordinates q).toAdd at hact
    rw [he] at hact
    change D (sectionQ.coordinates q).toAdd = 0
    exact sub_eq_zero.mpr hact.symm
  have hcardδ : Nat.card δ.range ≤ 2 := by
    have hh := card_map_le_card_map_of_ker_le (⊤ : Subgroup d.toTypeRuSetup.Q) δ ev hker
    rw [← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map] at hh
    exact hh.trans ((Nat.card_le_card_of_injective _ ev.range.subtype_injective).trans_eq d.card_Z)
  have hcardD : Nat.card (LinearMap.range D) = Nat.card δ.range := by
    let e : δ.range ≃ LinearMap.range D := {
      toFun x := ⟨x.val.toAdd, by
        obtain ⟨q, hq⟩ := x.property
        exact ⟨(sectionQ.coordinates q).toAdd, congrArg Multiplicative.toAdd hq⟩⟩
      invFun x := ⟨Multiplicative.ofAdd x.val, by
        obtain ⟨v, hv⟩ := x.property
        obtain ⟨q, hq⟩ := sectionQ.onto (Multiplicative.ofAdd v)
        exact ⟨q, by change Multiplicative.ofAdd (D _) = _; rw [hq]; exact congrArg Multiplicative.ofAdd hv⟩⟩
      left_inv x := by apply Subtype.ext; rfl
      right_inv x := by apply Subtype.ext; rfl }
    exact (Nat.card_congr e).symm
  have hD : D = 0 := zero_of_small_displacement D (hcardD.symm ▸ hcardδ)
    (hNoRank (d.ru2.quotientMap aH))
  have hact : d.ru2.naturalAction.action.dual (d.ru2.quotientMap aH) = 1 :=
    sub_eq_zero.mp hD
  have hstar : d.ru2.quotientMap aH = 1 := dual_injective d.ru2.naturalAction
    (by simpa only [map_one] using hact)
  have hk : aH ∈ d.ru2.quotientMap.ker := hstar
  rw [d.ru2.quotient_kernel] at hk
  exact hk

/-- The source's strict middle inclusion, conditional only on leaving Q. -/
theorem inf_Q_not_le_HC (d : LocalSetup G)
    (sectionQ : BinaryConjugationSection d.toTypeRuSetup.H d.toTypeRuSetup.Q
      d.toTypeRuSetup.HC (d.ru2.naturalAction.action.dual.comp d.ru2.quotientMap))
    (hNoRank : NoRankOne d) (l : G) (hl : l ∈ d.L)
    (hn : ¬ conjugateU d l ≤ d.toTypeRuSetup.Q) :
    ¬ conjugateU d l ⊓ d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.HC :=
  fun h => hn (conjugateU_le_Q_of_inf_le_HC d sectionQ hNoRank l hl h)

end CFSG.Quasithin.ChapterJ.ConjugateIntersections
