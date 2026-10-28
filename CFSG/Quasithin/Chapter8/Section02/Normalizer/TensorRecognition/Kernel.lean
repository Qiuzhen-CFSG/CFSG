module

public import Theory.GroupTheory.CommutingActionKernels
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The kernel on the two-conjugate core section

Work inside Y=L_U I: all normality assumptions below are relative to this
local group. Write R=L_U, P=O₂(I), and B=V∩P. The H.4/H.15/H.16 calculations
identify the R-kernel on B/U with O₂(R). Conjugating B by the literal h⁻¹
and using P=B B^h extends this kernel to P/U. The commutator conclusion
8.2.8(2) makes the two action images commute. E.2.14 supplies the I-kernel
and its centerless quotient, giving their direct product and O₂(Y).

The exact quotient-conjugation formula is retained. The theorem does not
assume the R-kernel on P/U or the full kernel equality. Its earlier local
module and E.2.14 inputs remain explicit for the normalizer assembly owner.

Source: Aschbacher–Smith, Proposition 8.2.8(4), printed p.718 (PDF p.735).
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
variable {G : Type*} [Group G]

private theorem two_conjugate_commutator (Q B U P : Subgroup G) [Q.Normal] [U.Normal]
    (h : G) (hgen : B ⊔ B.map (MulAut.conj h⁻¹).toMonoidHom = P)
    (hc : ⁅Q, B⁆ ≤ U) : ⁅Q, P⁆ ≤ U := by
  have hQ : Q.map (MulAut.conj h⁻¹).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top _))
  have hU : U.map (MulAut.conj h⁻¹).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top _))
  have hc' : ⁅Q, B.map (MulAut.conj h⁻¹).toMonoidHom⁆ ≤ U := by
    have hh := map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hc
    rwa [map_commutator, hQ, hU] at hh
  let q := QuotientGroup.mk' U
  have hf (D : Subgroup G) (hD : ⁅Q, D⁆ ≤ U) :
      D.map q ≤ centralizer (Q.map q : Set (G ⧸ U)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hD)
  have hP : P.map q ≤ centralizer (Q.map q : Set (G ⧸ U)) := by
    rw [← hgen, Subgroup.map_sup]
    exact sup_le (hf _ hc) (hf _ hc')
  have hh : (⁅Q, P⁆ : Subgroup G).map q = ⊥ := by
    rw [map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hP)
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hh

private theorem centerless_of_equiv {A D : Type*} [Group A] [Group D]
    (e : A ≃* D) (hz : center A = ⊥) : center D = ⊥ := by
  apply bot_unique
  intro d hd
  have ha : e.symm d ∈ center A := by
    rw [mem_center_iff]
    intro a
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hd (e a)
  rw [hz] at ha
  have he := congrArg e (show e.symm d = 1 from ha)
  simpa using he

private theorem centerless_action_image {D : Type*} [Group D]
    (f : G →* D) (I : Subgroup G)
    (hk : (f.comp I.subtype).ker = pCore 2 I)
    (hz : center (I ⧸ pCore 2 I) = ⊥) : center (I.map f) = ⊥ := by
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange (f.comp I.subtype)).trans
      (MulEquiv.subgroupCongr (show (f.comp I.subtype).range = I.map f by
        rw [MonoidHom.range_comp, range_subtype])))
  exact centerless_of_equiv e hz

variable (R I V U : Subgroup G) [R.Normal] [I.Normal] [U.Normal]

local instance : (I.pCoreIn 2).Normal := by unfold pCoreIn; infer_instance
local instance : (R.pCoreIn 2).Normal := by unfold pCoreIn; infer_instance

/-- The literal P/U action has kernel P O₂(R)=O₂(Y), with its marked product image. -/
theorem pairSection_kernel [Finite G]
    (hgen : R ⊔ I = ⊤) (h : G)
    (hP : (V ⊓ I.pCoreIn 2) ⊔
      (V ⊓ I.pCoreIn 2).map (MulAut.conj h⁻¹).toMonoidHom = I.pCoreIn 2)
    (hcomm : ⁅R, I⁆ ≤ R.pCoreIn 2)
    (hB : ∀ r : R,
      (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G), (b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R)
    (f : G →* MulAut (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)))
    (hact : ∀ (g : G) (p : I.pCoreIn 2),
      f g (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p) =
        QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) (MulAut.conjNormal g p))
    (hI : (f.comp I.subtype).ker = pCore 2 I)
    (hcenter : center (I ⧸ pCore 2 I) = ⊥) :
    pCore 2 G = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
      f.ker = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
      ∃ e : R.map f × I.map f ≃* f.range,
        ∀ r i, (e (r, i) : MulAut (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) =
          (r : MulAut _) * (i : MulAut _) := by
  have hQB : ⁅R.pCoreIn 2, V ⊓ I.pCoreIn 2⁆ ≤ U := by
    apply commutator_le.mpr
    rintro r ⟨a, ha, rfl⟩ b hb
    exact (hB a).mpr ha ⟨b, hb⟩
  have hQP := two_conjugate_commutator (R.pCoreIn 2) (V ⊓ I.pCoreIn 2) U
    (I.pCoreIn 2) h hP hQB
  have hkill : R.pCoreIn 2 ≤ f.ker := by
    intro r hr
    apply MonoidHom.mem_ker.mpr
    ext w
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf (I.pCoreIn 2)) w
    rw [hact]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (r * (p : G) * r⁻¹) / (p : G) ∈ U
    simpa only [commutatorElement_def, div_eq_mul_inv] using
      hQP (commutator_mem_commutator hr p.property)
  have hR : (f.comp R.subtype).ker = pCore 2 R := by
    ext r
    constructor
    · intro hr
      apply (hB r).mp
      intro b
      let p : I.pCoreIn 2 := ⟨b, b.property.2⟩
      have he := congrArg
        (fun a : MulAut (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) =>
          a (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p))
        (show f (r : G) = 1 from hr)
      rw [hact] at he
      have hb := QuotientGroup.eq_iff_div_mem.mp he
      change ((r : G) * (b : G) * (r : G)⁻¹) / (b : G) ∈ U at hb
      simpa only [commutatorElement_def, div_eq_mul_inv] using hb
    · intro hr
      exact hkill (mem_map_of_mem R.subtype hr)
  have hs := action_core_product f R I hgen (hcomm.trans hkill)
    (centerless_action_image f I hI hcenter) hR hI
  rw [sup_comm] at hs
  exact ⟨hs.1.trans hs.2.1, hs.2⟩

end CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
