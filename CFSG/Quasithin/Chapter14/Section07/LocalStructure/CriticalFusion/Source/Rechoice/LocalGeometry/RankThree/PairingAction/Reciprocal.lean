module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.PairingAction.Centralizers

/-!
# The reciprocal radical, with the original source conjugator

Conjugate the original rank-three commutator back from Uα to U. The
reversed source actor has a two-dimensional displacement in this subgroup's
two-dimensional image in U/V₁. Equality follows, so the cover's displacement
complement excludes the natural kernel. The centralizer bound then gives
exactly Zα as the reciprocal radical. This also proves [V₁,Qα]=Zα.

The reversed actor is an explicit input from the reversal of source
hypotheses in 14.7.39, together with 14.7.64 and 14.7.69. It is an element
of the literal inverse-conjugate U, with its image specified under the
original qH. No ambient element interchanging endpoints, reciprocal radical
identity, or new 14.7.70 action conclusion is assumed. Earlier-source
discharge belongs to qt-14-07, and [U,QH]=V₁ belongs to qt-14-05.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.39 and proof of 14.7.70, printed pp.1060 and 1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {d : Data T L V F W} {c : CriticalPath (L := L) F}

namespace Preliminary
variable (h : Preliminary d c)
include h

/-- Reversal uses the same path conjugator and the original marked actor.
The image equality is derived from displacement and the prepared order eight. -/
theorem reciprocal_commutator_image (s : d.ActionDescent)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    tilde d (conjugate (Fcomm c) c.conjugator⁻¹) =
      (d.action a - LinearMap.id).range := by
  let A := conjugate (Fcomm c) c.conjugator⁻¹
  have hU : conjugate c.Uα c.conjugator⁻¹ = F.U := by
    simpa only [CriticalPath.Uα, inv_inv] using conjugate_conjugate_inv F.U c.conjugator⁻¹
  have hAU : A ≤ F.U := (map_mono (h.commutator_le.trans inf_le_right)).trans_eq hU
  have hAP : F.Vi 1 ≤ A := by
    have hp := map_mono (f := (MulAut.conj (c.conjugator⁻¹)⁻¹).toMonoidHom) h.opposite_le
    change conjugate c.Zα c.conjugator⁻¹ ≤ conjugate (Fcomm c) c.conjugator⁻¹ at hp
    have hZ : conjugate c.Zα c.conjugator⁻¹ = F.Vi 1 := by
      simpa only [CriticalPath.Zα, inv_inv] using
        conjugate_conjugate_inv (F.Vi 1) c.conjugator⁻¹
    exact hZ ▸ hp
  have hcard : Nat.card A = 8 := by
    change Nat.card ((Fcomm c).map (MulAut.conj (c.conjugator⁻¹)⁻¹).toMonoidHom) = 8
    rw [card_map_of_injective (MulAut.conj _).injective, h.commutator_card]
  have hdim : Module.finrank (ZMod 2) (tilde d A) = 2 := by
    let := finite_original d
    have hc := card_eq_tilde_mul d A hAU hAP
    rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    have he : 2 ^ Module.finrank (ZMod 2) (tilde d A) = 2 ^ 2 := by omega
    exact Nat.pow_right_injective (by decide : 1 < 2) he
  have hcomm : ⁅conjugate F.U c.conjugator⁻¹, F.U⁆ ≤ A := by
    calc
      ⁅conjugate F.U c.conjugator⁻¹, F.U⁆ =
          ⁅conjugate F.U c.conjugator⁻¹, conjugate c.Uα c.conjugator⁻¹⁆ :=
        congrArg (fun B => ⁅conjugate F.U c.conjugator⁻¹, B⁆) hU.symm
      _ ≤ A := by
        change ⁅F.U.map _, c.Uα.map _⁆ ≤ (⁅F.U, c.Uα⁆).map _
        rw [map_commutator]
  have hle := d.conjugationSection.displacement_range_le_imageSpace_of_commutator_le
    (conjugate F.U c.conjugator⁻¹) A hcomm a ha
  let := finite_original d
  exact (Submodule.eq_of_le_of_finrank_eq hle
    ((displacement_finrank d s a t ht hmark).trans hdim.symm)).symm

/-- The original marked-cover complement proves the reciprocal intersection;
it is not postulated as a symmetry assumption. -/
theorem reciprocal_commutator_inf_fixed (s : d.ActionDescent)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    conjugate (Fcomm c) c.conjugator⁻¹ ⊓ d.U₀ = F.Vi 1 := by
  have hU : conjugate c.Uα c.conjugator⁻¹ = F.U := by
    simpa only [CriticalPath.Uα, inv_inv] using conjugate_conjugate_inv F.U c.conjugator⁻¹
  have hAU : conjugate (Fcomm c) c.conjugator⁻¹ ≤ F.U :=
    (map_mono (h.commutator_le.trans inf_le_right)).trans_eq hU
  have hP : F.Vi 1 ≤ conjugate (Fcomm c) c.conjugator⁻¹ := by
    have hp := map_mono (f := (MulAut.conj (c.conjugator⁻¹)⁻¹).toMonoidHom) h.opposite_le
    change conjugate c.Zα c.conjugator⁻¹ ≤ conjugate (Fcomm c) c.conjugator⁻¹ at hp
    have hZ : conjugate c.Zα c.conjugator⁻¹ = F.Vi 1 := by
      simpa only [CriticalPath.Zα, inv_inv] using
        conjugate_conjugate_inv (F.Vi 1) c.conjugator⁻¹
    exact hZ ▸ hp
  refine le_antisymm ?_ (le_inf hP d.point_le_U₀)
  intro x hx
  let u : F.U := ⟨x, hAU hx.1⟩
  have hm : (d.conjugationSection.coordinates u).toAdd ∈
      tilde d (conjugate (Fcomm c) c.conjugator⁻¹) :=
    (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨u, hx.1, rfl⟩
  rw [h.reciprocal_commutator_image s a ha t ht hmark] at hm
  have hk := (d.mem_U₀ u).mp hx.2
  have hz := Submodule.disjoint_def.mp (s.original_upper_complement a t ht hmark).1 _ hm hk
  exact (d.conjugationSection.coordinates_eq_one_iff u).mp hz

/-- The reciprocal radical is derived by transport along the actual source
conjugator, using the same nontrivial earlier commutator. -/
theorem commutator_inf_reciprocal_core_centralizer (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    Fcomm c ⊓ centralizer (c.Qα : Set G) = c.Zα := by
  have hQ : conjugate c.Qα c.conjugator⁻¹ = F.H.pCoreIn 2 := by
    unfold conjugate CriticalPath.Qα
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj _).injective]
    congr 1
    simpa only [conjugate, inv_inv] using conjugate_conjugate_inv F.H c.conjugator⁻¹
  have hc : conjugate (centralizer (c.Qα : Set G)) c.conjugator⁻¹ ≤
      centralizer (F.H.pCoreIn 2 : Set G) := by
    rw [← hQ]
    exact map_centralizer_le_centralizer_image _ _
  have hU : conjugate c.Uα c.conjugator⁻¹ = F.U := by
    simpa only [CriticalPath.Uα, inv_inv] using conjugate_conjugate_inv F.U c.conjugator⁻¹
  have hAU : conjugate (Fcomm c) c.conjugator⁻¹ ≤ F.U :=
    (map_mono (h.commutator_le.trans inf_le_right)).trans_eq hU
  have hle : conjugate (Fcomm c ⊓ centralizer (c.Qα : Set G)) c.conjugator⁻¹ ≤ F.Vi 1 := by
    rw [conjugate_inf]
    calc
      _ ≤ conjugate (Fcomm c) c.conjugator⁻¹ ⊓ d.U₀ :=
        le_inf inf_le_left ((inf_le_inf hAU hc).trans (core_centralizer_le_U₀ d s h21))
      _ = F.Vi 1 := h.reciprocal_commutator_inf_fixed s a ha t ht hmark
  apply le_antisymm
  · have hm := map_mono (f := (MulAut.conj c.conjugator⁻¹).toMonoidHom) hle
    change conjugate (conjugate (Fcomm c ⊓ centralizer (c.Qα : Set G))
      c.conjugator⁻¹) c.conjugator ≤ c.Zα at hm
    rwa [conjugate_conjugate_inv] at hm
  · refine le_inf h.opposite_le ?_
    have hm := map_mono (f := (MulAut.conj c.conjugator⁻¹).toMonoidHom)
      ((point_le_core_centralizer d).trans inf_le_right)
    apply hm.trans
    have hQ' : conjugate (F.H.pCoreIn 2) c.conjugator = c.Qα := by
      exact map_pCoreIn_of_injective 2 F.H _ (MulAut.conj _).injective
    rw [← hQ']
    exact map_centralizer_le_centralizer_image _ _

/-- The second source cross-commutator follows from the proved reciprocal
radical and the distinct original points. -/
theorem point_commutator (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    ⁅F.Vi 1, c.Qα⁆ = c.Zα := by
  have hα : ⁅c.Uα, c.Qα⁆ = c.Zα := by
    have hm := congrArg (fun A : Subgroup G => A.map (MulAut.conj c.conjugator⁻¹).toMonoidHom) h21
    rw [map_commutator, map_pCoreIn_of_injective 2 F.H _ (MulAut.conj _).injective] at hm
    exact hm
  have hle := (commutator_mono (h.point_le.trans (h.commutator_le.trans inf_le_right)) le_rfl).trans_eq hα
  have hn : ⁅F.Vi 1, c.Qα⁆ ≠ ⊥ := by
    intro hb
    have hp : F.Vi 1 ≤ c.Zα := by
      rw [← h.commutator_inf_reciprocal_core_centralizer s h21 a ha t ht hmark]
      exact le_inf h.point_le (commutator_eq_bot_iff_le_centralizer.mp hb)
    have hpbot : F.Vi 1 ≤ ⊥ := by
      calc
        F.Vi 1 ≤ F.Vi 1 ⊓ c.Zα := le_inf le_rfl hp
        _ = ⊥ := h.opposite_disjoint_point.eq_bot
    have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [bot_unique hpbot, card_bot] at hc
    omega
  apply eq_of_le_of_card_ge hle
  have hh := (one_lt_card_iff_ne_bot _).mpr hn
  rw [opposite_card c]
  omega

end Preliminary
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
