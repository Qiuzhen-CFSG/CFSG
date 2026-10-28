module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.Cover
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.Coordinates

/-!
# The source core marking and the intersection bound

If C_V(L) is nontrivial, the actual augmentation cover constructed from
the original Irr⁺ choice is an isomorphism: its domain has dimension seven,
while V/C_V(L) has dimension six and the kernel is nonzero. The resulting
marking preserves both conjugation by L and the original quotient map.

This marking removes the model and dimension premises from the core
intersection argument. Once the earlier element-fusion, TI and centralizer
control statements are supplied, nonidentity intersection vectors have
weight four, and the literal parameter r(G,V) is at least four. The fusion
and centralizer statements remain this source branch's obligations; no
fixed-space elimination is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), opening of
§12.6, printed p.822, and Lemma 12.6.20(1,3), printed pp.828–829.
-/

public section

open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

theorem OrthogonalMarking.core_marking_of_fixed_ne_bot
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hz : ZV L V ≠ ⊥) :
    ∃ E : Additive V ≃ₗ[ZMod 2] core (Fin 8),
      (∀ l w, E (seedRepresentation L V chosen.normalizes l w) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) ∧
      ∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w) := by
  have hfix : (fixedSeed L V chosen.normalizes).toSubmodule ≠ ⊥ := by
    intro hf
    apply hz
    apply le_antisymm _ bot_le
    intro z hz'
    have hm := (mem_fixedSeed_iff L V chosen.normalizes
      (Additive.ofMul (show V from ⟨z,hz'.1⟩))).mpr hz'
    rw [hf] at hm
    have he : Additive.ofMul (show V from ⟨z,hz'.1⟩) = 0 := hm
    exact congrArg (fun a : Additive V => (a.toMul : G)) he
  obtain ⟨f,hf,he,hp⟩ := D.core_cover chosen
  have hpos : 0 < Module.finrank (ZMod 2) (fixedSeed L V chosen.normalizes).toSubmodule :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hfix)
  have hsum := Submodule.finrank_quotient_add_finrank
    (fixedSeed L V chosen.normalizes).toSubmodule
  have hquot : Module.finrank (ZMod 2) (Vhat L V chosen.normalizes) = 6 := by
    rw [D.coordinates.finrank_eq, finrank_natural_even _ (by decide)]
    rfl
  have hupper := LinearMap.finrank_le_finrank_of_surjective hf
  have hdim : Module.finrank (ZMod 2) (core (Fin 8)) =
      Module.finrank (ZMod 2) (Additive V) := by
    rw [finrank_core] at hupper ⊢
    change Module.finrank (ZMod 2) (Vhat L V chosen.normalizes) + _ = _ at hsum
    rw [hquot] at hsum
    simp only [Fintype.card_fin] at hupper ⊢
    omega
  let F : core (Fin 8) ≃ₗ[ZMod 2] Additive V := LinearEquiv.ofBijective f
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hf,hf⟩
  refine ⟨F.symm, ?_, ?_⟩
  · intro l w
    apply F.injective
    rw [F.apply_symm_apply]
    exact ((he l (F.symm w)).trans
      (congrArg (seedRepresentation L V chosen.normalizes l) (F.apply_symm_apply w))).symm
  · intro w
    exact (hp (F.symm w)).symm.trans
      (congrArg (fun a : Additive V => D.coordinates (Submodule.Quotient.mk a))
        (F.apply_symm_apply w))

open CentralLine

theorem OrthogonalMarking.core_intersections_of_centralizer_control
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hz : ZV L V ≠ ⊥)
    (hf : ControlsElementFusion L V) (hTI : HasTIConjugatesIn V (M L))
    (hfixed : ∀ z ∈ ZV L V, z ≠ 1 → Gv z ≤ M L)
    (hcontrol : ∀ v : V, D.Nonsingular v → Gv (v : G) ≤ M L) :
    (∀ g ∉ normalizer (V : Set G),
      Nat.log 2 (Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ 3) ∧
      4 ≤ ChapterE.globalR V := by
  obtain ⟨E, _, hproj⟩ := D.core_marking_of_fixed_ne_bot chosen hz
  have hbound (X : Submodule (ZMod 2) (core (Fin 8)))
      (hX : ∀ x ∈ X, x ≠ 0 → coreWeightFour x) : Module.finrank (ZMod 2) X ≤ 3 := by
    apply EightGeometry.finrank_weight_four_le X
    intro x hx hn
    simpa only [coreWeightFour, Fintype.card_subtype, hammingNorm] using hX x hx hn
  have hC : ∀ v ∈ V, v ≠ 1 → v ∉ markedVectors E coreWeightFour →
      centralizer ({v} : Set G) ≤ M L := by
    intro v hv hv1 hnot
    let w : Additive V := Additive.ofMul ⟨v,hv⟩
    by_cases hzero : (Submodule.Quotient.mk w : Vhat L V chosen.normalizes) = 0
    · exact hfixed v ((mem_fixedSeed_iff L V chosen.normalizes w).mp
        ((Submodule.Quotient.mk_eq_zero _).mp hzero)) hv1
    · apply hcontrol ⟨v,hv⟩
      intro hs
      have hq : coreToNatural (Fin 8) (E w) ≠ 0 := by
        rw [hproj]
        exact fun hh => hzero (D.coordinates.injective (hh.trans D.coordinates.map_zero.symm))
      have hw : hammingNorm (E w).val = 4 :=
        (EightGeometry.nonzero_singular_core_iff (E w)).mp
          ⟨hq, by rw [hproj]; exact hs⟩
      apply hnot
      refine ⟨hv, ?_⟩
      simpa only [coreWeightFour, Fintype.card_subtype, hammingNorm] using hw
  obtain ⟨hi,hr⟩ := core_intersections_and_globalR E hbound chosen.normalizes hf hTI hC
  exact ⟨fun g hg => (hi g hg).2, hr⟩

end CFSG.Quasithin.Chapter12.Section06
