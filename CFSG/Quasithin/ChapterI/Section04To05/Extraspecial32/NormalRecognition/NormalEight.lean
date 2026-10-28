module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Defs
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Recognizing the quotient in the normal elementary-eight case

Suppose the source fusion analysis supplies a normal self-centralizing
elementary eight containing `z`. Conjugation embeds its ambient quotient
in `Aut(E₈) = GL₃(2)`. The centralizer of `z` has image of order 24 and
index seven in that automorphism group. Its properness in the ambient group
forces the full conjugation image to be all of `GL₃(2) = PSL₃(2)`.

The final theorem applies this quotient argument to the canonical fusion
subgroup and produces precisely the original elementary-eight alternative.
It requires no simplicity or splitting assumption. The fusion geometry and
ambient normality remain explicit premises of this conditional result.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.5, 2.8 and Proposition 4.12(1).
-/

namespace CFSG.Quasithin.Extraspecial32

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G] {z : G}

namespace Hypotheses

/-- The literal quotient by a normal self-centralizing elementary eight
containing `z` is the concrete binary projective special linear group. -/
public theorem normal_eight_quotient (h : Hypotheses z) (V : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hV : Nat.card V = 8)
    (hzV : z ∈ V) (hC : centralizer (V : Set G) = V) :
    Nonempty ((G ⧸ V) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let f : G →* MulAut V := MulAut.conjNormal
  have hker : f.ker = V := (MulAut.conjNormal_ker_eq_centralizer V).trans hC
  have hVH : V ≤ Centralizer z := by
    intro v hv
    have hvC : v ∈ centralizer (V : Set G) := by rwa [hC]
    exact mem_centralizer_singleton_iff.mpr (hvC z hzV).symm
  let fH := f.comp (Centralizer z).subtype
  have hkerH : fH.ker = V.subgroupOf (Centralizer z) := by
    change f.ker.comap (Centralizer z).subtype = _
    rw [hker]
    rfl
  have hHcard : Nat.card fH.range = 24 := by
    have hh := fH.ker.card_mul_index
    rw [index_ker, hkerH, Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv,
      hV, h.centralizer_card] at hh
    omega
  have hHR : fH.range ≤ f.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have hproper : fH.range ≠ f.range := by
    intro he
    apply h.centralizer_ne_top
    apply eq_top_iff.mpr
    intro g _
    have hg : f g ∈ fH.range := he ▸ (show f g ∈ f.range from ⟨g, rfl⟩)
    obtain ⟨a, ha⟩ := hg
    have hk : (a : G)⁻¹ * g ∈ V := by
      rw [← hker]
      change f ((a : G)⁻¹ * g) = 1
      simp only [map_mul, map_inv]
      change f (a : G) = f g at ha
      rw [ha, inv_mul_cancel]
    have hm := (Centralizer z).mul_mem a.property (hVH hk)
    simpa only [mul_inv_cancel_left] using hm
  have hAut : Nat.card (MulAut V) = 168 := card_mulAut_of_elementary_eight V hV
  have hHindex : fH.range.index = 7 := by
    have hh := fH.range.card_mul_index
    rw [hHcard, hAut] at hh
    omega
  have hRindex : f.range.index ∣ 7 := hHindex ▸ index_dvd_of_le hHR
  have hsurj : Function.Surjective f := by
    rcases (show Nat.Prime 7 by decide).eq_one_or_self_of_dvd _ hRindex with h1 | h7
    · exact MonoidHom.range_eq_top.mp (index_eq_one.mp h1)
    · have hRcard : Nat.card f.range = 24 := by
        have hh := f.range.card_mul_index
        rw [h7, hAut] at hh
        omega
      exact (hproper (eq_of_le_of_card_ge hHR (by omega))).elim
  let e : (G ⧸ V) ≃* MulAut V :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  exact ⟨e.trans ((elementaryEight_mulAut_equiv_GL V hV).some.trans
    (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv))⟩

/-- The normal case of the canonical fusion eight gives source alternative (1).
The source fusion deductions are the explicit `FusionEightData` premise. -/
public theorem elementaryEightAlternative_of_normal_fusion (h : Hypotheses z)
    (d : FusionEightData z) (hn : (fusionCore z).Normal) : ElementaryEightAlternative G := by
  let : (fusionCore z).Normal := hn
  let : IsElementaryAbelian 2 (fusionCore z) := d.elementary
  exact ⟨fusionCore z, hn, d.elementary, d.card,
    h.normal_eight_quotient (fusionCore z) d.card h.involution_mem_fusionCore
      d.centralizer_eq⟩

end Hypotheses
end CFSG.Quasithin.Extraspecial32
