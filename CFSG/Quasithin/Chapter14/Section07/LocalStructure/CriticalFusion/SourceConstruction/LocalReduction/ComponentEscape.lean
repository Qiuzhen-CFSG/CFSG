module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreePrimeComponent
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Component escape and the literal reduced local

A perfect normal subgroup of an original local contained in N_G(L)
acts trivially on the four-element seed quotient: its permutation image
is solvable. Normality propagates this to the full local span, whose
kernel is O₂(I), forcing the subgroup to be trivial. Apply this to the
Sylow span of a C-component to obtain escape and the literal member
⟨Kᵀ⟩L₁T of the same H_z. All normality statements remain relative to I.

Source: Aschbacher–Smith, 14.5.19, printed p.1018, and its reduction in
14.7.7, printed p.1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem local_action_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    (F.localTildeAction I hI.2.1).ker = pCore 2 I := by
  let := h.chosen.elementary
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  exact F.localKernel_eq_pCore h.source.simpleQTKE L _ I (by decide)
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique structural uniqueness).2
    (h.seed_centralizer_le structural uniqueness) h.centralizer_L hI

private theorem seed_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    Nat.card (F.tilde V) = 4 := by
  let := h.chosen.elementary
  let f := F.tildeMap V ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  have hk : f.ker = (F.Vi 1).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, ← Subtype.val_inj]
    change (F.tildeProjection ⟨v, _⟩ = 1) ↔ (v : G) ∈ F.Vi 1
    exact QuotientGroup.eq_one_iff _
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  have he := QuotientGroup.quotientKerEquivOfSurjective f (F.tildeMap_surjective V _)
  have hker : Nat.card f.ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv]
    simpa using F.card 1 (by decide)
  have hV : Nat.card V = 8 := by simpa only [F.last, Nat.reducePow] using F.card 3 (by decide)
  rw [Nat.card_congr he.toEquiv, hker, hV] at hc
  omega

/-- A perfect normal subgroup of an original local cannot be contained in M.
The action on the four-element seed quotient is solvable, and normality
propagates its triviality to the whole local span. -/
theorem local_normal_perfect_eq_bot_of_le_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (N : Subgroup G) (hNI : N ≤ I) (hn : (N.subgroupOf I).Normal)
    [Group.IsPerfect N] (hNM : N ≤ normalizer (L : Set G)) : N = ⊥ := by
  classical
  let := h.chosen.elementary
  let := hn
  have hNH := hNI.trans hI.2.1
  have hNV : N ≤ normalizer (V : Set G) :=
    (le_inf hNM hNH).trans ((h.flag_normalizer_le structural F (by decide) (by decide)).trans inf_le_right)
  let f := F.tildeAction N V hNH hNV
  let e : F.tilde V ≃ Fin 4 := Finite.equivFinOfCardEq (seed_card h)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (F.tilde V)) :=
    Group.isSolvable_of_isSolvable_injective (f := (Equiv.permCongrHom e).toMonoidHom)
      (Equiv.permCongrHom e).injective
  let g := (MulAction.toPermHom (MulAut (F.tilde V)) (F.tilde V)).comp f
  let : Group.IsPerfect g.range := Group.IsPerfect.range g
  have hsub : Subsingleton g.range := by
    by_contra! hnt
    exact Group.IsPerfect.not_isSolvable g.range inferInstance
  have hf (a : N) : f a = 1 := by
    have hg : g a = 1 := congrArg Subtype.val (Subsingleton.elim (g.rangeRestrict a) 1)
    apply MulEquiv.ext
    intro v
    exact congrArg (fun z : Equiv.Perm (F.tilde V) => z v) hg
  have hNseed : N.subgroupOf I ≤
      ChapterF.Section08.Setup.quotientCentralizer (F.f8SourceSetup L I) hI.2.1 V := by
    intro a ha
    apply (ChapterF.Section08.Setup.mem_quotientCentralizer_iff (F.f8SourceSetup L I) hI.2.1 V
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) a).mpr
    intro v hv
    have hh := (F.mem_tildeAction_ker_iff N V hNH
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) hNV ⟨a,ha⟩).mp (hf ⟨a,ha⟩) v hv
    simpa only [commutatorElement_inv] using (F.Vi 1).inv_mem hh
  have hNcore : N.subgroupOf I ≤ pCore 2 I := by
    rw [←local_action_kernel h structural I hI,←F.f8Source_core_eq_kernel L I hI.2.1
      (h.chosen.le_sylow.trans (F.sylow_le_of_mem_Hz hI))]
    exact normal_le_normalCore.mpr hNseed
  have hp : IsPGroup 2 N :=
    (pCore_isPGroup.to_le hNcore).of_equiv (subgroupOfEquivOfLe hNI)
  by_contra hne
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hne
  exact Group.IsPerfect.not_isNilpotent N hp.isNilpotent

/-- Source 14.5.19: a genuine local C-component escapes N_G(L). -/
theorem local_component_not_le_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    ¬ K.map I.subtype ≤ normalizer (L : Set G) := by
  intro hKM
  let N := conjugateSpanBy K ((T : Subgroup G).subgroupOf I)
  let : N.Normal := local_component_sylow_span_normal h I hI K hK
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect N := conjugateSpanBy_isPerfect K _
  let : Group.IsPerfect (N.map I.subtype) := Group.IsPerfect.map _
  have hNT : N.map I.subtype = conjugateSpanBy (K.map I.subtype) (T : Subgroup G) := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)]
  have hNM : N.map I.subtype ≤ normalizer (L : Set G) := by
    rw [hNT]
    apply conjugateSpanBy_le hKM
    exact (h.sylow_normalizes structural).trans (normalizer (L : Set G)).le_normalizer
  have hn : ((N.map I.subtype).subgroupOf I).Normal := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using (inferInstance : N.Normal)
  have hb := local_normal_perfect_eq_bot_of_le_normalizer h structural I hI
    (N.map I.subtype) (map_subtype_le N) hn hNM
  have hNb : N = ⊥ := (map_eq_bot_iff_of_injective _ I.subtype_injective).mp hb
  exact hK.ne_bot (bot_unique ((le_conjugateSpanBy K _).trans hNb.le))

/-- The literal K-orbit and point parabolic form a member of the same H_z,
with relative normality of the orbit in the original local retained. -/
theorem local_component_reduced_mem_Hz
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
    let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
    (N.subgroupOf I).Normal ∧ J ≤ I ∧ J ∈ F.Hz L (normalizer (L : Set G)) := by
  let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
  let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  have hNI : N ≤ I := conjugateSpanBy_le (map_subtype_le K)
    ((F.sylow_le_of_mem_Hz hI).trans I.le_normalizer)
  have hJI : J ≤ I := sup_le hNI (sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI))
  have hJH := hJI.trans hI.2.1
  have hn : (N.subgroupOf I).Normal := by
    have he : N = (conjugateSpanBy K ((T : Subgroup G).subgroupOf I)).map I.subtype := by
      rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)]
    rw [he,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective]
    exact local_component_sylow_span_normal h I hI K hK
  refine ⟨hn,hJI,?_,hJH,?_⟩
  · have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    have hpoint : F.Vi 1 ≤ J.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hcard))
        ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans le_sup_right))) hJH
    refine ⟨?_,fun _ hx => hx.elim (fun ha => mem_sup_right (mem_sup_left ha))
      (fun ha => mem_sup_right (mem_sup_right ha))⟩
    intro he
    have hp := le_bot_iff.mp (he ▸ hpoint)
    simp [hp] at hcard
  · intro hJM
    exact local_component_not_le_normalizer h structural I hI K hK
      ((le_conjugateSpanBy _ _).trans (le_sup_left.trans hJM))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
