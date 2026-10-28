module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternating
public import Theory.Representation.BinaryPermutation.SixCoreOrbits
public import Theory.GroupTheory.TwoOddOrbitsFusion

/-!
# Global TI for the actual six-letter augmentation core

The given faithful-action marking uses L/C_L(V), without replacing that
quotient by L/O₂(L). Its constant word supplies the unique nonidentity
L-fixed element z. Structural1222 makes N_G(L) normalize V and fix z;
NoEscape makes z weakly closed in V.

Off that line the actual A₆-orbits are the weight-two and weight-four
classes, both of size fifteen. The normalizer either merges them or
preserves them. In the latter case each orbit has a T-fixed representative.
Common-Sylow fusion and N_G(T) ≤ N_G(L) then control their ambient fusion.
Local TI therefore gives global TI for the original chosen V.

The final application removes the six-letter premise from the existing
alternating-row assembly. The eight-letter geometry and the proof of the
Sylow-normalizer containment remain with their original owners.

Source: Aschbacher–Smith, 12.2.16, printed pp.799–800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
open BinaryPermutation

private theorem globalTI_of_six_core_marking
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (π : L →* alternatingGroup (Fin 6)) (hπ : Function.Surjective π)
    (f : Multiplicative (core (Fin 6)) ≃* V)
    (hf : ∀ (l : L) (v : core (Fin 6)),
      (f (Multiplicative.ofAdd (alternatingCoreRepresentation (Fin 6) (π l) v)) : G) =
        (l : G) * f (Multiplicative.ofAdd v) * (l : G)⁻¹) : IsTISubgroup V := by
  let F : core (Fin 6) → G := fun v => f (Multiplicative.ofAdd v)
  let z := F sixCoreConstant
  have hF : Function.Injective F := Subtype.val_injective.comp
    (f.injective.comp Multiplicative.ofAdd.injective)
  have hF0 : F 0 = 1 := congrArg Subtype.val f.map_one
  have hFV (v : core (Fin 6)) : F v ∈ V := (f (Multiplicative.ofAdd v)).property
  have hFsurj (x : G) (hx : x ∈ V) : ∃ v, F v = x := by
    obtain ⟨v,hv⟩ := f.surjective ⟨x,hx⟩
    exact ⟨v.toAdd,congrArg Subtype.val hv⟩
  have hz1 : z ≠ 1 := fun he => sixCoreConstant_ne_zero (hF (he.trans hF0.symm))
  have hzL : z ∈ centralizer (L : Set G) := by
    intro l hl
    have he := hf ⟨l,hl⟩ sixCoreConstant
    rw [sixCoreConstant_fixed] at he
    exact mul_inv_eq_iff_eq_mul.mp he.symm
  have hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z := by
    intro w hw hwL
    obtain ⟨v,rfl⟩ := hFsurj w hw
    have hv : ∀ a, alternatingCoreRepresentation (Fin 6) a v = v := by
      intro a
      obtain ⟨l,rfl⟩ := hπ a
      apply hF
      exact (hf l v).trans (mul_inv_eq_iff_eq_mul.mpr (hwL l l.property))
    rcases (sixCore_fixed_iff v).mp hv with rfl | rfl
    · exact Or.inl hF0
    · exact Or.inr rfl
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rcases ((structural G T L h).2.2 V D).2.2.2 with hm | he
    · exact hm
    · exact (hz1 (mem_bot.mp (he ▸ (show z ∈ V ⊓ centralizer (L : Set G) from
        ⟨hFV _,hzL⟩)))).elim
  have hMz := normalizer_centralizes_fixed_line h D structural (hFV _) hz1 hzL hfixed
  have himage (v : core (Fin 6)) :
      F '' (Set.range fun a => alternatingCoreRepresentation (Fin 6) a v) =
        conjugacyOrbit L (F v) := by
    ext x
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      obtain ⟨l,rfl⟩ := hπ a
      exact ⟨l,(hf l v).symm⟩
    · rintro ⟨l,rfl⟩
      exact ⟨_,⟨π l,rfl⟩,hf l v⟩
  have hmem (v w : core (Fin 6)) :
      F w ∈ conjugacyOrbit L (F v) ↔
        ∃ a, alternatingCoreRepresentation (Fin 6) a v = w := by
    rw [← himage]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,he⟩
      exact ⟨a,hF he⟩
    · rintro ⟨a,ha⟩
      exact ⟨w,⟨a,ha⟩,rfl⟩
  let U : Set G := {x | x ∈ V ∧ x ≠ 1 ∧ x ≠ z}
  have hoff {v : core (Fin 6)} (hv : F v ∈ U) : v ≠ 0 ∧ v ≠ sixCoreConstant :=
    ⟨fun he => hv.2.1 ((congrArg F he).trans hF0), fun he => hv.2.2 (congrArg F he)⟩
  have hUinv : ∀ m ∈ normalizer (L : Set G), ∀ x ∈ U, m * x * m⁻¹ ∈ U := by
    intro m hm x hx
    refine ⟨(hMV hm x).mp hx.1, ?_, ?_⟩
    · exact fun he => hx.2.1 ((MulAut.conj m).map_eq_one_iff.mp he)
    · intro he
      apply hx.2.2
      apply (MulAut.conj m).injective
      exact he.trans (mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp (hMz hm))).symm
  have hodd : ∀ x ∈ U, Odd (conjugacyOrbit L x).ncard := by
    intro x hx
    obtain ⟨v,rfl⟩ := hFsurj x hx.1
    rw [← himage,Set.ncard_image_of_injective _ hF,
      sixCore_orbit_card v (hoff hx).1 (hoff hx).2]
    decide
  have hcover : ∀ x ∈ U, ∀ y ∈ U, y ∉ conjugacyOrbit L x →
      U ⊆ conjugacyOrbit L x ∪ conjugacyOrbit L y := by
    intro x hx y hy hne w hw
    obtain ⟨v,rfl⟩ := hFsurj x hx.1
    obtain ⟨u,rfl⟩ := hFsurj y hy.1
    obtain ⟨a,rfl⟩ := hFsurj w hw.1
    rcases sixCore_two_orbits v u (hoff hx).1 (hoff hx).2 (hoff hy).1 (hoff hy).2
      (fun he => hne ((hmem v u).mpr he)) a (hoff hw).1 (hoff hw).2 with he | he
    · exact Or.inl ((hmem v a).mpr he)
    · exact Or.inr ((hmem u a).mpr he)
  apply globalTI_of_fusion h D structural hnone
  intro x y hx hy hx1 hy1 hxy
  have hc : IsConj x y := isConj_iff.mpr hxy
  by_cases hxz : x = z
  · subst x
    have hyz := fixed_line_weakly_closed h D structural hnone
      (hFV _) hz1 hzL hfixed hy hc
    exact ⟨1,one_mem _,by simp [hyz,z]⟩
  have hyz : y ≠ z := by
    intro he
    subst y
    exact hxz (fixed_line_weakly_closed h D structural hnone
      (hFV _) hz1 hzL hfixed hx hc.symm)
  obtain ⟨m,hm⟩ := fusion_of_two_odd_orbits T L (normalizer (L : Set G))
    L.le_normalizer (structural G T L h).1 hNT U hUinv hodd hcover
    ⟨hx,hx1,hxz⟩ ⟨hy,hy1,hyz⟩ hc
  exact ⟨m,m.property,hm⟩

/-- The six-letter branch on the literal faithful action of the chosen module. -/
theorem globalTI_of_alternating_six_core
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (alternatingCoreRepresentation (Fin 6))) :
    IsTISubgroup V := by
  let := D.actionCentralizer_normal
  let π := e.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L))
  let f := e.linearEquiv.symm.toAddEquiv.toMultiplicative.trans D.spaceEquiv
  apply globalTI_of_six_core_marking h D structural hnone hNT π
    (e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)) f
  intro l v
  have he := e.intertwines
    (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l) (e.linearEquiv.symm v)
  have he' : e.linearEquiv.symm (alternatingCoreRepresentation (Fin 6) (π l) v) =
      D.chosenAction l (e.linearEquiv.symm v) := by
    apply e.linearEquiv.injective
    simpa only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      D.faithfulAction_mk, LinearEquiv.apply_symm_apply] using he.symm
  change (D.spaceEquiv (Multiplicative.ofAdd (e.linearEquiv.symm
    (alternatingCoreRepresentation (Fin 6) (π l) v))) : G) =
      (l : G) * D.spaceEquiv (Multiplicative.ofAdd (e.linearEquiv.symm v)) * (l : G)⁻¹
  rw [he',D.spaceEquiv_apply,D.spaceEquiv_apply]
  rfl

/-- The original alternating-row consumer, with the six-letter input discharged.
Only the independent eight-letter core geometry remains explicit. -/
theorem alternating_of_eight_core_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (eight : Chapter6.Source.IsConjugationModel L V
      (alternatingCoreRepresentation (Fin 8)) →
        IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V))
    (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural n)) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V) := by
  exact alternating_of_core_geometry D h.quasisimple hne
    (globalTI_of_alternating_six_core h D structural hnone hNT) eight n hlo hhi e

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
