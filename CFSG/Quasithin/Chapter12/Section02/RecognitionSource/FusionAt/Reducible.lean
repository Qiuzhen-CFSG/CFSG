module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Normalizer

/-!
# Fusion at the original ambient group and Sylow subgroup: Reducible

These are ambient-local versions of the existing source fusion proofs. Only
the structural premise changes: each use is at the original G,T,L,V. The
literal module actions, quotient maps, point Sylow subgroups and conjugators
are preserved. The universal APIs remain available in their original modules.

Source: Aschbacher–Smith, 12.2.16, printed pp.799–800; the reducible
normalizer argument uses 3.3.1 and B.5.1 as in the original proofs.
-/

/- Adapted from FusionReducibleSLThree. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

open Section04.SmallFusion Representation.OneCohomology

open ChapterI.Section06To08

public theorem globalTI_of_slThree_four_dimensional_at
    {K : GroupClass} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hd : Module.finrank (ZMod 2) D.space = 4)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) : IsTISubgroup V := by
  obtain ⟨E⟩ := slThreeExtension_of_four_dimensional D e hd hne
  exact globalTI_of_slThree_extension_at h D structural hnone E hne

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionReducibleRows. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 ChapterB.QuasisimpleSource

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem reducible_of_alternating_and_g2_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (alternating : ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
      (letI := D.actionCentralizer_normal
       ActionEquiv D.faithfulCentralAction (alternatingNatural n)) →
      IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V))
    (g2 : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype) →
      IsTISubgroup V) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V) := by
  cases rows with
  | linear n _ action =>
      exact Or.inl (globalTI_of_natural_at h D structural hnone
        (D.conjugationModel_of_quotientAction action))
  | linearThreeExtension e hd _ =>
      exact Or.inl (globalTI_of_slThree_four_dimensional_at h D structural hnone e hd hne)
  | linearFiveExterior _ _ hi =>
      exact (hne (fixedSubgroup_eq_bot_of_irreducible D hi)).elim
  | alternating n hlo hhi action => exact alternating n hlo hhi action
  | alternatingSevenFour e hd =>
      let := D.actionCentralizer_normal
      exact Or.inl (globalTI_of_alternating_seven_four_at h D structural hnone e hd)
  | g2 action => exact Or.inl (g2 action)
  | tripleSix _ _ _ hi =>
      exact (hne (fixedSubgroup_eq_bot_of_irreducible D hi)).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionReducibleAdjustment. -/
section
open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

variable {G : Type*} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

namespace AlternatingEightFusionSeed

variable (C : AlternatingEightFusionSeed T L V)

include C in

public theorem exists_adjusted_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V) :
    Nonempty (AlternatingEightFusion T L V) := by
  have hTz : (T : Subgroup G) ≤ centralizer ({(C.z : G)} : Set G) :=
    (structural L h).1.trans
      (normalizer_centralizes_fixed_line_at h D structural
        C.z.property C.z_ne C.z_fixed C.fixed_line)
  have hy : (C.sylow : Subgroup (centralizer ({(C.v : G)} : Set G))).map
      (centralizer ({(C.v : G)} : Set G)).subtype ≤
        centralizer ({(C.v : G) * (C.z : G)} : Set G) := by
    rw [C.sylow_image]
    intro t ht
    apply mem_centralizer_singleton_iff.mpr
    have hv := mem_centralizer_singleton_iff.mp ht.2
    have hz := mem_centralizer_singleton_iff.mp (hTz ht.1)
    calc
      t * ((C.v : G) * (C.z : G)) = (t * (C.v : G)) * (C.z : G) := (mul_assoc _ _ _).symm
      _ = ((C.v : G) * t) * (C.z : G) := by rw [hv]
      _ = (C.v : G) * ((C.z : G) * t) := by rw [mul_assoc, hz]
      _ = ((C.v : G) * (C.z : G)) * t := (mul_assoc _ _ _).symm
  obtain ⟨g,hg,he⟩ := exists_normalizer_conjugator_of_centralizer_sylow
    (C.v : G) ((C.v : G) * (C.z : G)) C.sylow hy
    (isConj_iff.mpr ⟨C.g,C.conjugates⟩)
  have hout : g ∉ normalizer (L : Set G) := by
    intro hm
    apply C.outside
    apply conjugator_mem_of_centralizer_le (hnone _ C.v.property C.v_ne)
    exact ⟨g,hm,he.trans C.conjugates.symm⟩
  refine ⟨{
    groupEquiv := C.groupEquiv
    vectorEquiv := C.vectorEquiv
    intertwines := C.intertwines
    v := C.v
    z := C.z
    weight_two := C.weight_two
    constant := C.constant
    z_ne := C.z_ne
    z_fixed := C.z_fixed
    fixed_line := C.fixed_line
    sylow := C.sylow
    sylow_image := C.sylow_image
    g := g
    outside := hout
    conjugates := he
    normalizes := ?_ }⟩
  rwa [C.sylow_image] at hg

end AlternatingEightFusionSeed

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end

/- Adapted from FusionReducible. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 ChapterB.QuasisimpleSource

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem reducible_of_geometric_rows_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (alternating : ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
      (letI := D.actionCentralizer_normal
       ActionEquiv D.faithfulCentralAction (alternatingNatural n)) →
      IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V))
    (g2 : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype) →
      IsTISubgroup V) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V) := by
  apply reducible_of_alternating_and_g2_at h D structural hnone rows hne _ g2
  intro n hlo hhi action
  rcases alternating n hlo hhi action with ht | hC
  · exact Or.inl ht
  · let C : AlternatingEightFusionSeed T L V := Classical.choice hC
    exact Or.inr (C.exists_adjusted_at h D structural hnone)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionReducibleAlternatingSix. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 ChapterB.QuasisimpleSource

universe u

variable {G : Type u} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

open BinaryPermutation

private theorem globalTI_of_six_core_marking_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
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
    rcases ((structural L h).2.2 V D).2.2.2 with hm | he
    · exact hm
    · exact (hz1 (mem_bot.mp (he ▸ (show z ∈ V ⊓ centralizer (L : Set G) from
        ⟨hFV _,hzL⟩)))).elim
  have hMz := normalizer_centralizes_fixed_line_at h D structural (hFV _) hz1 hzL hfixed
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
  apply globalTI_of_fusion_at h D structural hnone
  intro x y hx hy hx1 hy1 hxy
  have hc : IsConj x y := isConj_iff.mpr hxy
  by_cases hxz : x = z
  · subst x
    have hyz := fixed_line_weakly_closed_at h D structural hnone
      (hFV _) hz1 hzL hfixed hy hc
    exact ⟨1,one_mem _,by simp [hyz,z]⟩
  have hyz : y ≠ z := by
    intro he
    subst y
    exact hxz (fixed_line_weakly_closed_at h D structural hnone
      (hFV _) hz1 hzL hfixed hx hc.symm)
  obtain ⟨m,hm⟩ := fusion_of_two_odd_orbits T L (normalizer (L : Set G))
    L.le_normalizer (structural L h).1 hNT U hUinv hodd hcover
    ⟨hx,hx1,hxz⟩ ⟨hy,hy1,hyz⟩ hc
  exact ⟨m,m.property,hm⟩

public theorem globalTI_of_alternating_six_core_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (alternatingCoreRepresentation (Fin 6))) :
    IsTISubgroup V := by
  let := D.actionCentralizer_normal
  let π := e.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L))
  let f := e.linearEquiv.symm.toAddEquiv.toMultiplicative.trans D.spaceEquiv
  apply globalTI_of_six_core_marking_at h D structural hnone hNT π
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

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionReducibleAlternatingEightGeometryOrbits. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open BinaryPermutation ChapterI.Section06To08

variable {G : Type*} [Group G] [Finite G] {K : GroupClass}

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace AlternatingEightCoreCoordinates

variable (C : AlternatingEightCoreCoordinates L V)

public theorem outside_weights_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (v w : V) (hv : (v : G) ≠ 1) {g : G}
    (hout : g ∉ normalizer (L : Set G)) (hg : g * (v : G) * g⁻¹ = w) :
    (C.weight v = 2 ∧ C.weight w = 6) ∨ (C.weight v = 6 ∧ C.weight w = 2) := by
  have hw : (w : G) ≠ 1 := fun he => hv ((MulAut.conj g).map_eq_one_iff.mp (hg.trans he))
  have hn : C.weight v ≠ C.weight w := by
    intro he
    obtain ⟨l,hl,he⟩ := C.conjugator_of_weight v w he
    exact hout (conjugator_mem_of_centralizer_le (hnone v v.property hv)
      ⟨l,L.le_normalizer hl,he.trans hg.symm⟩)
  have hvz : v ≠ C.z := by
    intro he
    subst v
    exact hout (conjugator_mem_of_fixed_line_image_at h D structural hnone C.z.property
      C.z_ne C.z_fixed C.fixed_line (hg ▸ w.property))
  have hwz : w ≠ C.z := by
    intro he
    subst w
    have hi : g⁻¹ * (C.z : G) * (g⁻¹)⁻¹ = v := by rw [← hg]; group
    have hm := conjugator_mem_of_fixed_line_image_at h D structural hnone C.z.property
      C.z_ne C.z_fixed C.fixed_line (hi ▸ v.property)
    exact hout (by simpa only [inv_inv] using (normalizer (L : Set G)).inv_mem hm)
  have hv0 : C.weight v ≠ 0 := fun he => hv (congrArg Subtype.val ((C.weight_zero_iff v).mp he))
  have hw0 : C.weight w ≠ 0 := fun he => hw (congrArg Subtype.val ((C.weight_zero_iff w).mp he))
  have hv8 : C.weight v ≠ 8 := fun he => hvz ((C.weight_eight_iff v).mp he)
  have hw8 : C.weight w ≠ 8 := fun he => hwz ((C.weight_eight_iff w).mp he)
  have hvw := EightCore.weights (C.word v)
  have hww := EightCore.weights (C.word w)
  change C.weight v = 0 ∨ C.weight v = 2 ∨ C.weight v = 4 ∨
    C.weight v = 6 ∨ C.weight v = 8 at hvw
  change C.weight w = 0 ∨ C.weight w = 2 ∨ C.weight w = 4 ∨
    C.weight w = 6 ∨ C.weight w = 8 at hww
  have hc := conjugate_normalizerOrbit_card hnone v w hv hw hg
  have hv4 : C.weight v ≠ 4 := by
    intro h4
    have hw26 : C.weight w = 2 ∨ C.weight w = 6 := by omega
    have hb := C.normalizerOrbit_two_six_le hMV w hw26
    rw [← hc,C.normalizerOrbit_four hMV v h4] at hb
    omega
  have hw4 : C.weight w ≠ 4 := by
    intro h4
    have hv26 : C.weight v = 2 ∨ C.weight v = 6 := by omega
    have hb := C.normalizerOrbit_two_six_le hMV v hv26
    rw [hc,C.normalizerOrbit_four hMV w h4] at hb
    omega
  omega

end AlternatingEightCoreCoordinates

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionReducibleAlternatingEightGeometry. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open BinaryPermutation ChapterI.Section06To08 Representation ChapterB.QuasisimpleSource

universe u

variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace AlternatingEightCoreCoordinates

variable (C : AlternatingEightCoreCoordinates L V)

public theorem seed_of_pair_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (v : V) (hv : C.weight v = 2) {g : G}
    (hout : g ∉ normalizer (L : Set G))
    (hg : g * (v : G) * g⁻¹ = (v : G) * (C.z : G)) :
    Nonempty (AlternatingEightFusionSeed T L V) := by
  obtain ⟨m,hm,S,hS⟩ := T.exists_conjugate_local_centralizer_sylow
    (normalizer (L : Set G)) (structural L h).1 (v : G) (D.le_sylow v.property)
  let w : V := ⟨m * (v : G) * m⁻¹,(mem_normalizer_iff.mp (hMV hm) v).mp v.property⟩
  have hw : C.weight w = 2 := C.selected_weight_two hnone v w hv hout hg hm rfl
  have hw1 : (w : G) ≠ 1 := by
    intro hh
    have h0 : C.weight w = 0 := (C.weight_zero_iff w).mpr (Subtype.ext hh)
    omega
  have hcentral : normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G) =
      centralizer ({(w : G)} : Set G) := inf_eq_right.mpr (hnone w w.property hw1)
  have hs : ∃ R : Sylow 2 (centralizer ({(w : G)} : Set G)),
      (R : Subgroup (centralizer ({(w : G)} : Set G))).map
        (centralizer ({(w : G)} : Set G)).subtype =
          (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) := by
    have hh : ∃ R : Sylow 2 (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G) : Subgroup G),
        (R : Subgroup _).map
          (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G)).subtype =
            (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) := ⟨S,hS⟩
    rw [hcentral] at hh
    exact hh
  obtain ⟨R,hR⟩ := hs
  have hmz : m * (C.z : G) * m⁻¹ = C.z := mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp
      (normalizer_centralizes_fixed_line_at h D structural C.z.property C.z_ne
        C.z_fixed C.fixed_line hm))
  refine ⟨{
    groupEquiv := C.groupEquiv
    vectorEquiv := C.vectorEquiv
    intertwines := C.intertwines
    v := w
    z := C.z
    weight_two := hw
    constant := C.constant
    sylow := R
    sylow_image := hR
    g := m*g*m⁻¹
    outside := ?_
    conjugates := ?_ }⟩
  · intro hh
    apply hout
    have hn := (normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem hm) hh) hm
    simpa [mul_assoc] using hn
  · calc
      (m*g*m⁻¹) * (w : G) * (m*g*m⁻¹)⁻¹ = m * (g * (v : G) * g⁻¹) * m⁻¹ := by
        dsimp only [w]; group
      _ = m * ((v : G) * (C.z : G)) * m⁻¹ := by rw [hg]
      _ = (w : G) * (m * (C.z : G) * m⁻¹) := by dsimp only [w]; group
      _ = (w : G) * (C.z : G) := by rw [hmz]

end AlternatingEightCoreCoordinates

public theorem alternatingEight_core_geometry_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hcore : Chapter6.Source.IsConjugationModel L V
      (alternatingCoreRepresentation (Fin 8))) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V) := by
  classical
  obtain ⟨e,f,hf⟩ := hcore
  let C : AlternatingEightCoreCoordinates L V := ⟨e,f,hf⟩
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) :=
    (((structural L h).2.2 V D).2.2.2).resolve_right hne
  by_cases hTI : IsTISubgroup V
  · exact Or.inl hTI
  right
  have hn := mt (isTISubgroup_iff V).mpr hTI
  push Not at hn
  obtain ⟨g,hg,x,hx,hgx,hx1⟩ := hn
  have hout : g ∉ normalizer (L : Set G) := fun hh => hg (hMV hh)
  let v : V := ⟨x,hx⟩
  let w : V := ⟨g*x*g⁻¹,hgx⟩
  rcases C.outside_weights_at h D structural hnone hMV v w hx1 hout rfl with hc | hc
  · obtain ⟨a,ha,hea⟩ := C.align_pair v w hc.1 hc.2 hout rfl
    exact C.seed_of_pair_at h D structural hnone hMV v hc.1 ha hea
  · have hi : g⁻¹ * (w : G) * (g⁻¹)⁻¹ = v := by dsimp only [w,v]; group
    have hout' : g⁻¹ ∉ normalizer (L : Set G) := fun hh =>
      hout (by simpa only [inv_inv] using (normalizer (L : Set G)).inv_mem hh)
    obtain ⟨a,ha,hea⟩ := C.align_pair w v hc.2 hc.1 hout' hi
    exact C.seed_of_pair_at h D structural hnone hMV w hc.2 ha hea

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionReducibleAlternatingComplete. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 ChapterB.QuasisimpleSource

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem alternating_of_sylow_normalizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural n)) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V) := by
  exact alternating_of_core_geometry D h.quasisimple hne
    (globalTI_of_alternating_six_core_at h D structural hnone hNT)
    (alternatingEight_core_geometry_at h D structural hnone hne) n hlo hhi e

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionReducibleG2Fusion. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08

variable {G : Type*} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

public theorem globalTI_of_sylow_central_representatives_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    (hcentral : ∀ x ∈ V, x ≠ 1 → x ≠ z →
      ∃ m ∈ normalizer (L : Set G),
        (T : Subgroup G) ≤ centralizer ({m * x * m⁻¹} : Set G)) : IsTISubgroup V := by
  apply globalTI_of_fusion_at h D structural hnone
  intro x y hx hy hx1 hy1 hxy
  have hc : IsConj x y := isConj_iff.mpr hxy
  by_cases hxz : x = z
  · subst x
    have hyz := fixed_line_weakly_closed_at h D structural hnone hz hz1 hzL hfixed hy hc
    exact ⟨1,one_mem _,by simp [hyz]⟩
  have hyz : y ≠ z := by
    intro he
    subst y
    exact hxz (fixed_line_weakly_closed_at h D structural hnone hz hz1 hzL hfixed hx hc.symm)
  obtain ⟨a,ha,hax⟩ := hcentral x hx hx1 hxz
  obtain ⟨b,hb,hby⟩ := hcentral y hy hy1 hyz
  let x' := a*x*a⁻¹
  let y' := b*y*b⁻¹
  let S := T.subtype hax
  have hST : (S : Subgroup (centralizer ({x'} : Set G))).map
      (centralizer ({x'} : Set G)).subtype = (T : Subgroup G) := by
    exact map_subgroupOf_eq_of_le hax
  have hxy' : IsConj x' y' :=
    (isConj_iff.mpr ⟨a,rfl⟩).symm.trans (hc.trans (isConj_iff.mpr ⟨b,rfl⟩))
  obtain ⟨c,hcN,he⟩ := exists_normalizer_conjugator_of_centralizer_sylow x' y' S
    (hST ▸ hby) hxy'
  rw [hST] at hcN
  refine ⟨b⁻¹*c*a,mul_mem (mul_mem (inv_mem hb) (hNT hcN)) ha,?_⟩
  have he' : c*(a*x*a⁻¹)*c⁻¹ = b*y*b⁻¹ := he
  calc
    (b⁻¹*c*a)*x*(b⁻¹*c*a)⁻¹ = b⁻¹*(c*(a*x*a⁻¹)*c⁻¹)*b := by group
    _ = b⁻¹*(b*y*b⁻¹)*b := by rw [he']
    _ = y := by group

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionReducibleG2Transport. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 ChapterB.QuasisimpleSource Atlas.G2.Natural

local notation "F" => ZMod 2

local notation "E" => TraceZero F

private abbrev DerivedActor_at := _root_.commutator (Atlas.G2.Model F)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem globalTI_of_g2_weyl_action_at
    {K : GroupClass} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (a : ActionEquiv D.quotientAction (OrthogonalCover.action F)) : IsTISubgroup V := by
  let := D.elementary
  let b : V ≃* Multiplicative E :=
    D.spaceEquiv.symm.trans a.linearEquiv.toAddEquiv.toMultiplicative
  have hb (l : L) (v : V) :
      b.symm (Multiplicative.ofAdd (OrthogonalCover.action F
        (a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) (b v).toAdd)) =
      V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ v := by
    apply b.injective
    rw [b.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    let w := (D.spaceEquiv.symm v).toAdd
    have he := a.intertwines (QuotientGroup.mk' (pCore 2 L) l) w
    have hw : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) =
        V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ v := by
      apply Subtype.ext
      rw [D.spaceEquiv_apply]
      have hv : (w.val.toMul.val : G) = (v : G) :=
        (D.spaceEquiv_apply w).symm.trans
          (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
      change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _
      rw [hv]
      rfl
    change _ = a.linearEquiv (D.spaceEquiv.symm
      (V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ v)).toAdd
    rw [←hw,D.spaceEquiv.symm_apply_apply]
    exact he.symm
  have hsurj : Function.Surjective
      (fun l : L => a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) :=
    a.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let zi := b.symm (Multiplicative.ofAdd (identity F))
  let z : G := zi.val
  have hz : z ∈ V := zi.property
  have hz1 : z ≠ 1 := by
    intro he
    have hh : zi = 1 := Subtype.ext he
    have hh' := congrArg (fun v : V => (b v).toAdd) hh
    have hi : identity F = 0 := by
      change (b (b.symm (Multiplicative.ofAdd (identity F)))).toAdd = (b 1).toAdd at hh'
      rw [b.apply_symm_apply,map_one] at hh'
      exact hh'
    exact Atlas.SplitOctonion.unit_ne_zero (congrArg Subtype.val hi)
  have hzL : z ∈ centralizer (L : Set G) := by
    intro l hl
    have he := hb ⟨l,hl⟩ zi
    rw [show (b zi).toAdd = identity F from congrArg Multiplicative.toAdd (b.apply_symm_apply _)] at he
    rw [show OrthogonalCover.action F (a.groupEquiv
      (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)) (identity F) = identity F from
      traceZeroAction_identity F _] at he
    have hc : l*z*l⁻¹ = z := (congrArg Subtype.val he).symm
    exact mul_inv_eq_iff_eq_mul.mp hc
  have hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z := by
    intro w hw hwL
    let wi : V := ⟨w,hw⟩
    have hfix : (b wi).toAdd ∈ Representation.OneCohomology.fixed
        (OrthogonalCover.action F) := by
      intro g
      obtain ⟨l,rfl⟩ := hsurj g
      have hh := hb l wi
      have hc : V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ wi = wi := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (hwL l l.property)
      rw [hc] at hh
      have hh' := congrArg (fun v : V => (b v).toAdd) hh
      rw [b.apply_symm_apply] at hh'
      exact hh'
    rw [OrthogonalCover.fixed_eq_scalarLine,OrthogonalCover.binary_scalar_iff] at hfix
    rcases hfix with he | he
    · left
      have hh : b wi = 1 := he
      exact congrArg Subtype.val (b.map_eq_one_iff.mp hh)
    · right
      have hh : b wi = b zi := he.trans (congrArg Multiplicative.toAdd (b.apply_symm_apply _)).symm
      exact congrArg Subtype.val (b.injective hh)
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rcases ((structural L h).2.2 V D).2.2.2 with hn | he
    · exact hn
    · exact (hz1 (mem_bot.mp (he ▸ (show z ∈ V ⊓ centralizer (L : Set G) from ⟨hz,hzL⟩)))).elim
  have hMz := normalizer_centralizes_fixed_line_at h D structural hz hz1 hzL hfixed
  let M := normalizer (L : Set G)
  let c : Additive V ≃ₗ[F] E := by
    let ca : Additive V ≃+ E := {
      toFun v := (b v.toMul).toAdd
      invFun w := Additive.ofMul (b.symm (Multiplicative.ofAdd w))
      left_inv v := congrArg Additive.ofMul (b.symm_apply_apply v.toMul)
      right_inv w := congrArg Multiplicative.toAdd (b.apply_symm_apply _)
      map_add' v w := congrArg Multiplicative.toAdd (map_mul b v.toMul w.toMul) }
    exact { ca with map_smul' := ZMod.map_smul ca }
  let ρ := elementaryRepresentation (p := 2)
    (V.normalizerMonoidHom.comp (inclusion hMV))
  let σ : Representation F M E := c.conjRingEquiv.toMonoidHom.comp ρ
  have hσ (m : M) (v : E) :
      (b.symm (Multiplicative.ofAdd (σ m v)) : G) =
        (m : G)*(b.symm (Multiplicative.ofAdd v) : G)*(m : G)⁻¹ := by
    change (b.symm (b (V.normalizerMonoidHom ⟨m,hMV m.property⟩
      (b.symm (Multiplicative.ofAdd v)))) : G) = _
    rw [b.symm_apply_apply]
    rfl
  have hσi (m : M) : σ m (identity F) = identity F := by
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hσ]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hMz m.property))
  have hσn (m : M) (g : DerivedActor_at) : ∃ j : DerivedActor_at, ∀ x,
      σ m (OrthogonalCover.action F g x) = OrthogonalCover.action F j (σ m x) := by
    obtain ⟨l,rfl⟩ := hsurj g
    let l' : L := ⟨(m : G)*l*(m : G)⁻¹,(mem_normalizer_iff.mp m.property l).mp l.property⟩
    refine ⟨a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l'),?_⟩
    intro x
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hσ]
    have hh (k : L) (w : E) :
        (b.symm (Multiplicative.ofAdd (OrthogonalCover.action F
          (a.groupEquiv (QuotientGroup.mk' (pCore 2 L) k)) w)) : G) =
          (k : G)*(b.symm (Multiplicative.ofAdd w) : G)*(k : G)⁻¹ := by
      have hh := congrArg Subtype.val (hb k (b.symm (Multiplicative.ofAdd w)))
      rw [b.apply_symm_apply] at hh
      exact hh
    rw [hh,hh,hσ]
    dsimp only [l']
    group
  have hσq (m : M) (x : E) : OrthogonalCover.form F (σ m x) = OrthogonalCover.form F x :=
    OrthogonalCover.binary_form_normalized (σ m) (hσi m) (hσn m) x
  have hTM : (T : Subgroup G) ≤ M := (structural L h).1
  let τ := σ.comp (inclusion hTM)
  obtain ⟨v,hv,hvq,hvT⟩ := OrthogonalCover.binary_exists_fixed_singular T.isPGroup' τ
    (fun t x => hσq (inclusion hTM t) x)
  have hvn : mk F v ≠ 0 := by
    intro he
    have hs : v ∈ scalarLine F := (Submodule.Quotient.mk_eq_zero _).mp he
    rcases (OrthogonalCover.binary_scalar_iff v).mp hs with he | rfl
    · exact hv he
    · exact one_ne_zero ((OrthogonalCover.form_identity F).symm.trans hvq)
  apply globalTI_of_sylow_central_representatives_at h D structural hnone hNT hz hz1 hzL hfixed
  intro x hx hx1 hxz
  let xi : V := ⟨x,hx⟩
  have hxn : mk F (b xi).toAdd ≠ 0 := by
    intro he
    have hs : (b xi).toAdd ∈ scalarLine F := (Submodule.Quotient.mk_eq_zero _).mp he
    rcases (OrthogonalCover.binary_scalar_iff _).mp hs with he | he
    · exact hx1 (congrArg Subtype.val (b.map_eq_one_iff.mp he))
    · have hh : xi = zi := b.injective (he.trans (congrArg Multiplicative.toAdd (b.apply_symm_apply _)).symm)
      exact hxz (congrArg Subtype.val hh)
  obtain ⟨g,hg⟩ := OrthogonalCover.binary_orbit_pair hvn hxn
  obtain ⟨l,rfl⟩ := hsurj g
  refine ⟨l,L.le_normalizer l.property,?_⟩
  intro t ht
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  have hcentral (w : E) (hw : ∀ t : T, τ t w = w) :
      t*(b.symm (Multiplicative.ofAdd w) : G)*t⁻¹ = (b.symm (Multiplicative.ofAdd w) : G) := by
    have hh := hσ (inclusion hTM ⟨t,ht⟩) w
    change (b.symm (Multiplicative.ofAdd (τ ⟨t,ht⟩ w)) : G) = _ at hh
    rw [hw] at hh
    exact hh.symm
  have hxcoord : (b.symm (Multiplicative.ofAdd (OrthogonalCover.action F
      (a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) (b xi).toAdd)) : G) =
      (l : G)*x*(l : G)⁻¹ := congrArg Subtype.val (hb l xi)
  rw [←hxcoord]
  rcases hg with he | he
  · rw [he]
    exact hcentral v hvT
  · rw [he]
    apply hcentral
    intro s
    rw [map_add,hvT]
    exact congrArg (v + ·) (hσi (inclusion hTM s))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionReducibleG2. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 ChapterB.QuasisimpleSource

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem globalTI_of_g2_row_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype)) :
    IsTISubgroup V := by
  obtain ⟨a,_,_⟩ := g2_weyl_model D hne e
  exact globalTI_of_g2_weyl_action_at h D structural hnone hNT a

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end
