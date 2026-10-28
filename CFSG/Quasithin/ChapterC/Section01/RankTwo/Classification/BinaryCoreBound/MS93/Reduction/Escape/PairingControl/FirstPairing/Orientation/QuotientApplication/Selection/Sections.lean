module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Selection.Model

/-!
# Selecting a flag from the full natural section

Decompose an element modulo the radical into its natural and fixed parts.
A parabolic fixing the natural coordinate then fixes the original element
modulo that same radical. Inner relative markings transfer a nonzero fixed
vector to the specified natural subgroup, preserving the quotient projection.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), printed p.883.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Selection
open RankOnePairing
variable {A : Type*} [Group A] {π : A →* SL} {Q L H N : Subgroup A}

/-- Selection in the full natural section retains its radical N[H,Q]. -/
theorem section_fixed_flag (s : SingleNaturalSection π Q L H N)
    (x : A) (hx : x ∈ H) :
    ∃ (flag : SL) (side : Bool) (w : Fin 3 → ZMod 2),
      w ≠ 0 ∧
      (∀ a ∈ modelParabolic flag side, (s.natural.marking a).val.mulVec w = w) ∧
      ⁅zpowers x, parabolic π flag side⁆ ≤ radicalPreimage Q H N := by
  let D := radicalPreimage Q H N
  let T := movingPreimage Q H N
  let := s.radical_normal
  let : T.Normal := ⟨fun y hy a =>
    (mem_normalizer_iff.mp (s.natural.normalized (mem_top a)) y).mp hy⟩
  obtain ⟨m, hm, c, hc, hmc⟩ := mem_sup_of_normal_left.mp (s.decomposition ▸ hx)
  let m₀ : T := ⟨m, hm⟩
  obtain ⟨flag, side, w, hw, hfix, hfw⟩ :=
    exists_fixed_flag s.natural.marking (s.natural.coordinates m₀).toAdd
  refine ⟨flag, side, w, hw, hfw, ?_⟩
  let C := centralizerModulo (⊤ : Subgroup A) (parabolic π flag side) D
  have hxC : x ∈ C := by
    apply mem_centralizerModulo_iff.mpr
    refine ⟨mem_top _, ?_⟩
    intro a ha
    have hym : a * m * a⁻¹ ∈ T :=
      (mem_normalizer_iff.mp (s.natural.normalized (mem_top a)) m).mp hm
    let y : T := ⟨a * m * a⁻¹, hym⟩
    have hcoord : s.natural.coordinates y = s.natural.coordinates m₀ := by
      apply Multiplicative.toAdd.injective
      exact (s.natural.action a (mem_top a) m₀ y rfl).trans (hfix (π a) ha)
    have hker : y * m₀⁻¹ ∈ s.natural.coordinates.ker := by
      change s.natural.coordinates (y * m₀⁻¹) = 1
      rw [map_mul, map_inv, hcoord, mul_inv_cancel]
    have ham : ⁅a, m⁆ ∈ D := by
      rw [s.natural.kernel] at hker
      exact hker
    have hac : ⁅a, c⁆ ∈ D := (mem_centralizerModulo_iff.mp hc).2 a (mem_top _)
    let q := QuotientGroup.mk' D
    have hmcomm : Commute (q a) (q m) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr ham
    have hccomm : Commute (q a) (q c) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hac
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅a, x⁆ = 1
    rw [map_commutatorElement, ← hmc, map_mul]
    exact commutatorElement_eq_one_iff_commute.mpr (hmcomm.mul_right hccomm)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha z hz
  exact (mem_centralizerModulo_iff.mp (zpowers_le.mpr hxC hz)).2 a ha

private noncomputable def changeCoordinates (g : SL) :
    Multiplicative (Fin 3 → ZMod 2) ≃* Multiplicative (Fin 3 → ZMod 2) :=
  AddEquiv.toMultiplicative (Matrix.SpecialLinearGroup.toLin' g⁻¹).toAddEquiv

private theorem untwist (g a : SL) (v : Fin 3 → ZMod 2) :
    g⁻¹.val.mulVec ((g * a * g⁻¹).val.mulVec v) =
      a.val.mulVec (g⁻¹.val.mulVec v) := by
  have h : g⁻¹ * (g * a * g⁻¹) = a * g⁻¹ := by
    simp only [mul_assoc, inv_mul_cancel_left]
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec] using
    congrArg (fun b : SL => b.val.mulVec v) h

/-- Inner relative markings carry an actual nonzero fixed vector to a
nonidentity element of the supplied natural subgroup. -/
theorem fixed_subgroup_of_inner {Z P : Subgroup A}
    (z : NaturalFactor π ⊤ Z ⊥) (σ : MulAut SL)
    (same : z.marking.symm.trans σ ∈ MulAut.innerSubgroup SL)
    (w : Fin 3 → ZMod 2) (hw : w ≠ 0)
    (hfix : ∀ a ∈ P, (σ (π a)).val.mulVec w = w) :
    Z ⊓ centralizer (P : Set A) ≠ ⊥ := by
  obtain ⟨g, hg⟩ := same
  have hm (a : A) : σ (π a) = g * z.marking (π a) * g⁻¹ := by
    have he := congrArg (fun f : MulAut SL => f (z.marking (π a))) hg
    simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply]
      using he.symm
  let t := changeCoordinates g
  let u : Z := z.equivOfBot.symm (t (Multiplicative.ofAdd w))
  have hu : z.coordinates u = t (Multiplicative.ofAdd w) := z.equivOfBot.apply_symm_apply _
  have hne : (u : A) ≠ 1 := by
    intro h
    have hu1 : u = 1 := Subtype.ext h
    have ht : t (Multiplicative.ofAdd w) = t 1 := by
      rw [← hu, hu1, map_one, map_one]
    exact hw (congrArg Multiplicative.toAdd (t.injective ht))
  have huc : (u : A) ∈ centralizer (P : Set A) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    have hyn : a * (u : A) * a⁻¹ ∈ Z :=
      (mem_normalizer_iff.mp (z.normalized (mem_top a)) _).mp u.property
    let y : Z := ⟨_, hyn⟩
    have hf : (z.marking (π a)).val.mulVec
        (t (Multiplicative.ofAdd w)).toAdd = (t (Multiplicative.ofAdd w)).toAdd := by
      have h := congrArg (fun v => g⁻¹.val.mulVec v) (hfix a ha)
      rw [hm, untwist] at h
      exact h
    have hy : z.coordinates y = z.coordinates u := by
      apply Multiplicative.toAdd.injective
      rw [z.action a (mem_top _) u y rfl, hu, hf]
    have he : a * (u : A) * a⁻¹ = (u : A) :=
      congrArg Subtype.val (z.equivOfBot.injective hy)
    exact mul_inv_eq_iff_eq_mul.mp he
  intro hbot
  exact hne (mem_bot.mp (hbot ▸ (show (u : A) ∈ Z ⊓ centralizer (P : Set A)
    from ⟨u.property, huc⟩)))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Selection
