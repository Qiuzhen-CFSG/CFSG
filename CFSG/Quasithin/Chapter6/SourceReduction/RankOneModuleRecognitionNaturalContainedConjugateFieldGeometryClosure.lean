module
public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Natural
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryDefs
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.ReducedNormal.Equiv
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# The field-fixed quotient and its normalizer closure

Displacement identifies B/U equivariantly with the natural module U, so
the embedded residual O²(N_L(U)) acts irreducibly on the subgroup interval
[U,B]. This discharges the module premise in G.2.1, with the residual of
the normalizer as actor. Its point-normalizer residual is itself.

The relative Sylow, normalization, and characteristic-two conditions give
the remaining G.2.1 hypotheses. G.2.2 then makes the actual closure B_U
reduced modulo U and central modulo U under O₂(N_G(U)). The earlier
zeroth weak-closure bound makes B_U elementary abelian. These earlier
geometric assumptions remain explicit and are to be supplied by the
contained-centralizer assembly owner.

Source: Aschbacher–Smith, 6.1.14(4), printed p.671; G.2.1–2, p.332.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] {K B U : Subgroup G} {m : ℕ}

private theorem invariant_interval_of_natural_quotient
    (hnatural : IsNaturalModule K U m)
    (hKB : K ≤ normalizer (B : Set G))
    (d : B →* U) (hker : d.ker = U.subgroupOf B)
    (he : ∀ (l : K) (b b' : B),
      (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
      (d b' : G) = (l : G) * (d b : G) * (l : G)⁻¹)
    (A : Subgroup G) (hUA : U ≤ A) (hAB : A ≤ B)
    (hKA : K ≤ normalizer (A : Set G)) : A = U ∨ A = B := by
  let J := ((A.subgroupOf B).map d).map U.subtype
  have hJU : J ≤ U := map_subtype_le _
  have hfwd (l : K) (x : G) (hx : x ∈ J) : (l : G) * x * (l : G)⁻¹ ∈ J := by
    obtain ⟨u, ⟨b, hb, rfl⟩, rfl⟩ := hx
    let b' := B.normalizerMonoidHom ⟨l, hKB l.property⟩ b
    have hb' : b' ∈ A.subgroupOf B :=
      (mem_normalizer_iff.mp (hKA l.property) b).mp hb
    exact ⟨d b', ⟨b', hb', rfl⟩, he l b b' rfl⟩
  have hKJ : K ≤ normalizer (J : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl x hx
    exact hfwd ⟨l, hl⟩ x hx
  rcases hnatural.invariant_subgroup J hJU hKJ with hzero | hfull
  · left
    apply le_antisymm _ hUA
    intro x hx
    let b : B := ⟨x, hAB hx⟩
    have hh : (d b : G) ∈ J := ⟨d b, ⟨b, hx, rfl⟩, rfl⟩
    rw [hzero, mem_bot] at hh
    have hk : b ∈ d.ker := by exact Subtype.ext hh
    rw [hker] at hk
    exact hk
  · right
    have hmap : (A.subgroupOf B).map d = ⊤ := by
      apply map_injective U.subtype_injective
      simpa only [← MonoidHom.range_eq_map, U.range_subtype] using hfull
    have hk : d.ker ≤ A.subgroupOf B := by
      rw [hker]
      exact comap_mono hUA
    have hh := comap_map_eq_self hk
    rw [hmap, comap_top] at hh
    exact le_antisymm hAB (subgroupOf_eq_top.mp hh.symm)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {L M B U : Subgroup G} {n : ℕ}

/-- Irreducibility of the literal quotient B/U under O²(N_L(U)). -/
theorem field_fixedSpace_invariant_interval
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n) :
    U ≠ B ∧ ∀ A : Subgroup G, U ≤ A → A ≤ B →
      fieldLocalResidual L U ≤ normalizer (A : Set G) → A = U ∨ A = B := by
  obtain ⟨m, _, _, hRU⟩ := field_fixedSpace_natural hn hnatural hfield hUne
  obtain ⟨d, hd, hk, he⟩ := field_fixedSpace_displacement hnatural hfield hUne
  have hres : fieldLocalResidual L U ≤ L ⊓ normalizer (U : Set G) := map_subtype_le _
  have hLB : L ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural
    exact hm.normalizes
  constructor
  · intro hUB
    obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    obtain ⟨b, hb⟩ := hd u
    have hbker : b ∈ d.ker := by
      rw [hk]
      change (b : G) ∈ U
      rw [hUB]
      exact b.property
    exact hu (hb.symm.trans hbker)
  · intro A hUA hAB hRA
    exact invariant_interval_of_natural_quotient hRU (hres.trans inf_le_left |>.trans hLB)
      d hk (fun l b b' hb => he (inclusion hres l) b b' hb) A hUA hAB hRA

/-- The corrected G.2.1 data for the fixed space, using O²(N_L(U)). -/
@[expose] def fieldNormalizerSetup (L B U S : Subgroup G) : ChapterG.Section02.Setup G where
  V := B
  V₁ := U
  L := fieldLocalResidual L U
  T := S
  H := normalizer (U : Set G)

/-- The point-normalizer residual in G.2.1 is the same original residual. -/
theorem fieldNormalizerSetup_local_actor (S : Subgroup G) :
    (fieldNormalizerSetup L B U S).L₁ = fieldLocalResidual L U := by
  have hK : fieldLocalResidual L U ≤ normalizer (U : Set G) :=
    (map_subtype_le _).trans inf_le_right
  change (pResidual 2 (fieldLocalResidual L U ⊓ normalizer (U : Set G) : Subgroup G)).map
    (fieldLocalResidual L U ⊓ normalizer (U : Set G)).subtype = _
  rw [inf_eq_left.mpr hK]
  have hr : pResidual 2 (fieldLocalResidual L U) = ⊤ :=
    (pResidual_eq_top_iff 2 _).mpr
      (isPPerfect_embedded_pResidual 2 (L ⊓ normalizer (U : Set G)))
  rw [hr, ← MonoidHom.range_eq_map, range_subtype]

/-- Fixed-field descent supplies the missing module conditions of G.2.1. -/
theorem fieldNormalizerSetup_hypothesis
    (S : Subgroup G) (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hn : 2 < n)
    (hbase : (fieldNormalizerSetup L B U S).BaseHypothesis) :
    (fieldNormalizerSetup L B U S).Hypothesis := by
  obtain ⟨hproper, hirr⟩ := field_fixedSpace_invariant_interval
    hnatural hfield hbase.point_ne_bot hn
  have hLB : L ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural
    exact hm.normalizes
  refine { hbase with
    local_normalizes_V := ?_
    quotient_nonzero := hproper
    irreducible := ?_ }
  · rw [fieldNormalizerSetup_local_actor]
    exact sup_le ((map_subtype_le _).trans (inf_le_left.trans hLB)) hbase.T_normalizes_V
  · intro A hUA hAB hNA
    apply hirr A hUA hAB
    rw [fieldNormalizerSetup_local_actor] at hNA
    exact le_sup_left.trans hNA

/-- G.2.2 gives reducedness in N_G(U)/U and the actual core commutator bound. -/
theorem field_closure_reduced_and_core
    (S : Subgroup G) (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hn : 2 < n)
    (hbase : (fieldNormalizerSetup L B U S).BaseHypothesis) :
    fieldModuleClosure B U ≤ S ⊓ centralizer (U : Set G) ∧
      IsPReduced 2 (fieldModuleClosureQuotient B U) ∧
      ⁅(normalizer (U : Set G)).pCoreIn 2, fieldModuleClosure B U⁆ ≤ U := by
  let D := fieldNormalizerSetup L B U S
  have h := fieldNormalizerSetup_hypothesis S hnatural hfield hn hbase
  refine ⟨le_inf h.U_normal_in_T.1 h.U_le_centralizer_point, ?_, ?_⟩
  · have htop : D.tilde D.H = ⊤ := by
      change ((normalizer (U : Set G)).subgroupOf (normalizer (U : Set G))).map
        (QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G)))) = ⊤
      rw [subgroupOf_self, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    have hr : IsPReduced 2 ((D.tilde D.U).subgroupOf ⊤) := by
      have hr : IsPReduced 2 ((D.tilde D.U).subgroupOf (D.tilde D.H)) := h.tilde_U_reduced
      rwa [htop] at hr
    have hr' := hr.map_equiv (topEquiv : (⊤ : Subgroup D.Tilde) ≃* D.Tilde)
    change IsPReduced 2 (((D.tilde D.U).subgroupOf ⊤).map (⊤ : Subgroup D.Tilde).subtype) at hr'
    rw [map_subgroupOf_eq_of_le le_top] at hr'
    exact hr'
  · rw [commutator_comm]
    exact h.commutator_U_core_le_point

/-- The zeroth weak-closure bound makes the full normalizer closure elementary. -/
theorem field_closure_elementary
    (S : Subgroup G) (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hn : 2 < n)
    (hbase : (fieldNormalizerSetup L B U S).BaseHypothesis)
    (hweak : W B (S ⊓ centralizer (U : Set G)) 0 ≤ centralizer (B : Set G)) :
    IsElementaryAbelian 2 (fieldModuleClosure B U) := by
  let : IsElementaryAbelian 2 B := hbase.elementary
  have hR := (field_closure_reduced_and_core S hnatural hfield hn hbase).1
  have hW : fieldModuleClosure B U ≤ W B (S ⊓ centralizer (U : Set G)) 0 := by
    apply (closure_le _).mpr
    rintro x ⟨g, hg, b, hb, rfl⟩
    apply ChapterE.gamma_le_weakClosure (A := B.map (MulAut.conj g).toMonoidHom) ?_
      (mem_map_of_mem _ hb)
    apply (ChapterE.mem_gamma_zero_iff _ _ _).mpr
    refine ⟨g, rfl, ?_⟩
    rintro y ⟨a, ha, rfl⟩
    exact hR (subset_closure ⟨g, hg, a, ha, rfl⟩)
  let : IsMulCommutative (conjugateSpanBy B (normalizer (U : Set G))) :=
    (conjugateSpanBy_commutative_iff _ _).mpr (le_centralizer_iff.mp (hW.trans hweak))
  exact conjugateSpanBy_elementary_of_commutative B (normalizer (U : Set G))
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {L M B U : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem sylow_in_intermediate {H X S : Subgroup G}
    (hXH : X ≤ H) (hSX : S ≤ X) (R : Sylow 2 H)
    (hR : (R : Subgroup H).map H.subtype = S) :
    ∃ Q : Sylow 2 X, (Q : Subgroup X).map X.subtype = S := by
  let f : X →* H := inclusion hXH
  have hRmem (x : H) : x ∈ R ↔ (x : G) ∈ S := by
    rw [← hR]
    exact (mem_map_iff_mem (f := H.subtype) H.subtype_injective).symm
  have hrange : (R : Subgroup H) ≤ f.range := by
    intro x hx
    exact ⟨⟨x, hSX ((hRmem x).mp hx)⟩, rfl⟩
  refine ⟨R.comapOfInjective f (inclusion_injective _) hrange, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hRmem (f y)).mp hy
  · intro hx
    exact ⟨⟨x, hSX hx⟩, (hRmem (f ⟨x, hSX hx⟩)).mpr hx, rfl⟩

/-- The genuine local hypotheses for G.2.2 from the relative Sylow
statement in 6.1.14(1) and characteristic two in 6.1.14(2). -/
theorem fieldNormalizerSetup_base
    (S : Subgroup G) [IsElementaryAbelian 2 B]
    (hUB : U ≤ B) (hUne : U ≠ ⊥) (hBS : B ≤ S)
    (hSU : S ≤ normalizer (U : Set G))
    (hSB : S ≤ normalizer (B : Set G))
    (hSL : S ≤ normalizer (L : Set G))
    (hSyl : ∃ R : Sylow 2 (normalizer (U : Set G)),
      (R : Subgroup (normalizer (U : Set G))).map (normalizer (U : Set G)).subtype = S)
    (hchar : generalizedFitting (normalizer (U : Set G)) =
      pCore 2 (normalizer (U : Set G))) :
    (fieldNormalizerSetup L B U S).BaseHypothesis := by
  have hKN : fieldLocalResidual L U ≤ normalizer (U : Set G) :=
    (map_subtype_le _).trans inf_le_right
  have hSN : S ≤ normalizer (L ⊓ normalizer (U : Set G) : Set G) :=
    (le_inf hSL (hSU.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hSK : S ≤ normalizer (fieldLocalResidual L U : Set G) :=
    hSN.trans (normalizer_le_normalizer_characteristic_image
      (L ⊓ normalizer (U : Set G)) (pResidual 2 (L ⊓ normalizer (U : Set G) : Subgroup G)))
  refine {
    elementary := (inferInstance : IsElementaryAbelian 2 B)
    point_ne_bot := hUne
    point_le := hUB
    residual := (pResidual_eq_top_iff 2 _).mpr
      (isPPerfect_embedded_pResidual 2 (L ⊓ normalizer (U : Set G)))
    V_le_T := hBS
    T_normalizes_point := hSU
    T_normalizes_V := hSB
    T_normalizes_L := hSK
    sylow_LT := ?_
    H_le := le_rfl
    local_le := ?_
    sylow_H := hSyl
    characteristic_two := hchar }
  · obtain ⟨R, hR⟩ := hSyl
    exact sylow_in_intermediate (sup_le hKN hSU) le_sup_right R hR
  · rw [fieldNormalizerSetup_local_actor]
    exact sup_le hKN hSU
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {L M B U : Subgroup G} {n : ℕ}

/-- All closure conclusions of 6.1.14(4), conditional only on the earlier
relative Sylow, normalization, characteristic-two and weak-closure geometry. -/
theorem field_closure_of_sylow_geometry
    (S : Subgroup G) [IsElementaryAbelian 2 B]
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hn : 2 < n)
    (hUne : U ≠ ⊥) (hBS : B ≤ S)
    (hSU : S ≤ normalizer (U : Set G))
    (hSB : S ≤ normalizer (B : Set G))
    (hSL : S ≤ normalizer (L : Set G))
    (hSyl : ∃ R : Sylow 2 (normalizer (U : Set G)),
      (R : Subgroup (normalizer (U : Set G))).map (normalizer (U : Set G)).subtype = S)
    (hchar : generalizedFitting (normalizer (U : Set G)) =
      pCore 2 (normalizer (U : Set G)))
    (hweak : W B (S ⊓ centralizer (U : Set G)) 0 ≤ centralizer (B : Set G)) :
    fieldModuleClosure B U ≤ S ⊓ centralizer (U : Set G) ∧
      IsElementaryAbelian 2 (fieldModuleClosure B U) ∧
      IsPReduced 2 (fieldModuleClosureQuotient B U) ∧
      ⁅(normalizer (U : Set G)).pCoreIn 2, fieldModuleClosure B U⁆ ≤ U := by
  have hUB : U ≤ B := by
    obtain ⟨_, _, _, hU, _⟩ := hfield
    exact hU.le.trans inf_le_left
  have hb := fieldNormalizerSetup_base S hUB hUne hBS hSU hSB hSL hSyl hchar
  obtain ⟨hR, hred, hcore⟩ := field_closure_reduced_and_core S hnatural hfield hn hb
  exact ⟨hR, field_closure_elementary S hnatural hfield hn hb hweak, hred, hcore⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
