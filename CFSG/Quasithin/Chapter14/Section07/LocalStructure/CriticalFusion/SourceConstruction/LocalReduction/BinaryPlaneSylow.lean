module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCore
public import Theory.GroupAction.KleinFourSylowExtension

/-!
# Sylow subgroups and weak closure on the original reciprocal plane

The full plane action and the proved core identity identify the point
stabilizer Y₀ ∩ H with Q_H Uα. It has index three in Y₀ and is a Sylow
two-subgroup. Every plane-normalizing two-subgroup R between Q_H Uα and T
is therefore Sylow in Y = Y₀R, and C_Y(P) = O₂(Y). This discharges those
two premises in the literal application of 14.7.31(2), retaining the same
critical path, plane and returning conjugates throughout.

The normal span Q_H ∨ ⟨Uα^(L₁T)⟩ lies in T and is normalized by L₁T.
For this concrete candidate the construction of the local normalizing
W₀(R,V) requires only its normalization of P. That geometric premise is
explicit and remains unproved here; the later contradiction and the
classification through 14.7.52 are not asserted. In particular the
unconditional application at Q_H Uα is not claimed to be the source T_Y.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf. The earlier structural interfaces remain universal;
final original assembly still needs their guarded same-G,T successors.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual point stabilizer in Y₀ is Q_H Uα. Every plane-normalizing
two-subgroup between it and T yields the required 14.7.31(2) application. -/
theorem local_nonnormal_component_plane_sylow_extensions
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
      let R₀ := F.H.pCoreIn 2 ⊔ c.Uα
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧ P ≤ F.U ⊓ c.Uα ∧
      Y₀ ≤ normalizer (P : Set G) ∧
      normalizer (P : Set G) ≤ normalizer (Y₀ : Set G) ∧
      R₀ = Y₀ ⊓ F.H ∧ R₀.relIndex Y₀ = 3 ∧
      R₀ ≤ (T : Subgroup G) ∧ F.U ≤ R₀ ∧
      ∀ R : Subgroup G, R₀ ≤ R → R ≤ (T : Subgroup G) →
        R ≤ normalizer (P : Set G) →
        let Y := Y₀ ⊔ R
        Chapter1.IsSylowIn 2 R Y ∧
        Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2 ∧
        Nonempty (Y ⧸ pCore 2 Y ≃* Equiv.Perm (Fin 3)) ∧
        V ≤ ChapterE.indexedWeakClosure V R 0 ∧
        ChapterE.indexedWeakClosure V R 0 ≤ Y ∧
        Y ≤ normalizer (ChapterE.indexedWeakClosure V R 0 : Set G) := by
  obtain ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hkernel,hAcore,
    hcentralCore,hcoreEq,hstar,hquotient,hbound,hreturn,σ,hσ,hconj⟩ :=
    local_nonnormal_component_reciprocal_plane_core_with_action d h hab structural
      previous faithful earlier I K hI hKI hK hnormal
  let P := F.Vi 1 ⊔ c.Zα
  let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
  let R₀ := F.H.pCoreIn 2 ⊔ c.Uα
  let : IsElementaryAbelian 2 P := hE
  have hcardP : Nat.card P = 4 := hfour
  let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr (by intro hz; simp [hz] at hcardP)
  let : IsKleinFour P := ⟨hfour,IsElementaryAbelian.exponent_eq_prime⟩
  let τ := P.normalizerMonoidHom.comp (inclusion hYn)
  have hτ : Function.Surjective τ :=
    full_conjugation_surjective_overgroup Y₀ Y₀ P le_rfl hYn σ hσ hconj
  have hτconj : ∀ (y : Y₀) (v : P), (τ y v : G) = (y : G) * v * (y : G)⁻¹ :=
    fun _ _ => rfl
  have hker : τ.ker = (Y₀.pCoreIn 2).subgroupOf Y₀ := by
    dsimp [τ]
    rw [←MonoidHom.comap_ker,normalizerMonoidHom_ker,hkernel]
    ext y
    exact ⟨fun hc => ⟨y.property,hc⟩,fun hc => hc.2⟩
  have hkp : IsPGroup 2 τ.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 Y₀).comap_subtype
  have htwo : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨v,hv,_⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp htwo
  let z : P := ⟨v,mem_sup_left v.property⟩
  have hz : z ≠ 1 := fun he => hv (Subtype.ext (show (v : G) = 1 from congrArg (fun a : P => (a : G)) he))
  have hpow : (v : G)^2 = 1 := by
    have hh := pow_card_eq_one' (x := v)
    rw [htwo] at hh
    exact congrArg Subtype.val hh
  have hgen : zpowers (v : G) = F.Vi 1 := by
    have hh := congrArg (Subgroup.map (F.Vi 1).subtype) (zpowers_eq_top_of_prime_card htwo hv)
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hCH : centralizer ({(z : G)} : Set G) = F.H := by
    rw [←normalizer_zpowers_eq_centralizer_of_order_two (v : G)
      (orderOf_eq_prime hpow (fun he => hv (Subtype.ext he))),hgen]
    rfl
  obtain ⟨hp,hind⟩ := full_four_action_point_stabilizer Y₀ P τ hτ hkp hτconj z hz
  rw [hCH] at hp hind
  have hpoint : Y₀ ⊓ F.H = R₀ := by
    apply le_antisymm
    · change Y₀ ⊓ F.H ≤ F.H.pCoreIn 2 ⊔ c.Uα
      rw [←hcoreEq]
      exact le_pCoreIn_of_normalizes hp
        (le_inf inf_le_right (inf_le_left.trans hYn))
        ((le_inf (inf_le_right.trans hNY) (inf_le_left.trans F.H.le_normalizer)).trans
          inf_normalizer_le_normalizer_inf)
    · apply sup_le
      · exact le_inf le_sup_left (pCoreIn_le 2 F.H)
      · exact le_inf (hAcore.trans (pCoreIn_le 2 Y₀))
          ((critical_le_Q h structural c).trans (Q_le_H F))
  have hR₀T : R₀ ≤ (T : Subgroup G) := sup_le
    ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1)))
    (hR.trans ((pCoreIn_le_sylow _ (T.subtype
      (le_sup_right : (T : Subgroup G) ≤ F.Li L 1 ⊔ (T : Subgroup G)))).trans_eq
        (map_subgroupOf_eq_of_le le_sup_right)))
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  have hUR₀ : F.U ≤ R₀ := (le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 F.U) F.U_le_H
    (le_normalizer_conjugateSpanBy V F.H)).trans le_sup_left
  have hC := (local_nonnormal_component_plane_centralizer d h hab structural previous
    faithful earlier I K hI hKI hK hnormal).2
  refine ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hpoint.symm,?_,hR₀T,hUR₀,?_⟩
  · change R₀.relIndex Y₀ = 3
    rw [←hpoint,inf_comm,inf_relIndex_right]
    exact hind
  · intro R hR₀R hRT hRN
    let Y := Y₀ ⊔ R
    have hYN : Y ≤ normalizer (P : Set G) := sup_le hYn hRN
    obtain ⟨hSylow,hcore⟩ := full_four_action_sylow_extension Y₀ R P τ hτ hkp hτconj z hz
      hYn (T.isPGroup'.to_le hRT) hRN (hRN.trans hNY)
      (by rw [hCH]; exact hRT.trans (F.invariant 1))
      (by rw [hCH,hpoint]; exact hR₀R)
    let σY := P.normalizerMonoidHom.comp (inclusion hYN)
    have hσY : Function.Surjective σY :=
      full_conjugation_surjective_overgroup Y₀ Y P le_sup_left hYN τ hτ hτconj
    have hσYconj : ∀ (y : Y) (v : P), (σY y v : G) = (y : G)*v*(y : G)⁻¹ :=
      fun _ _ => rfl
    have hPY : P ≤ Y := (hplane.trans inf_le_left).trans
      (hUR₀.trans (hR₀R.trans le_sup_right))
    have hred := full_four_action_reduced Y P hPY hYN σY hσY hσYconj
    obtain ⟨e⟩ := full_four_action_core_quotient Y P σY hσY hσYconj hcore
    have hweak := EarlierWeakClosure.clause_two h structural F hC Y R P hSylow hPY hred e hcore
      (by
        intro g hg
        obtain ⟨y,hy,he,hP,hU⟩ := hreturn g hg
        exact hU.trans (hkernel.le.trans (inf_le_inf_right _ le_sup_left)))
    exact ⟨hSylow,hcore,⟨e⟩,
      ChapterE.self_le_weakClosure_zero
        ((le_conjugateSpanBy V F.H).trans (hUR₀.trans hR₀R)),hweak⟩


omit [Finite G] in
/-- The normal span used for the source Sylow is already a two-subgroup
of the original T, normalized by the actual L₁T. Plane normalization is
the separate orthogonal-module calculation. -/
theorem critical_plane_normal_span (c : CriticalPath (L := L) F)
    (hR : c.Uα ≤ F.Ri L 1) :
    let J := F.Li L 1 ⊔ (T : Subgroup G)
    let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
    F.H.pCoreIn 2 ⊔ c.Uα ≤ R ∧ R ≤ (T : Subgroup G) ∧
      J ≤ normalizer (R : Set G) := by
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  have hJH : J ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have hJR : J ≤ normalizer (F.Ri L 1 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hRiT : F.Ri L 1 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow J (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  have hJQ : J ≤ normalizer (F.H.pCoreIn 2 : Set G) := hJH.trans
    (F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
  exact ⟨sup_le_sup_left (le_conjugateSpanBy c.Uα J) _,
    sup_le hQT ((conjugateSpanBy_le hR hJR).trans hRiT),
    (le_inf hJQ (le_normalizer_conjugateSpanBy c.Uα J)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)⟩

/-- The literal normal span gives the source weak-closure local as soon as
its remaining geometric premise, plane normalization, is established.
All Sylow, plane-kernel, reducedness and returning-point premises are
proved here on the original selected path. -/
theorem local_nonnormal_component_normal_span_weakClosure
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
      let R₀ := F.H.pCoreIn 2 ⊔ c.Uα
      let J := F.Li L 1 ⊔ (T : Subgroup G)
      let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧
      R₀ = Y₀ ⊓ F.H ∧ Chapter1.IsSylowIn 2 R₀ Y₀ ∧
      V ≤ ChapterE.indexedWeakClosure V R₀ 0 ∧
      Y₀ ≤ normalizer (ChapterE.indexedWeakClosure V R₀ 0 : Set G) ∧
      R₀ ≤ R ∧ R ≤ (T : Subgroup G) ∧ J ≤ normalizer (R : Set G) ∧
      (R ≤ normalizer (P : Set G) →
        let Y := Y₀ ⊔ R
        Chapter1.IsSylowIn 2 R Y ∧
        Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2 ∧
        Nonempty (Y ⧸ pCore 2 Y ≃* Equiv.Perm (Fin 3)) ∧
        V ≤ ChapterE.indexedWeakClosure V R 0 ∧
        J ⊔ Y ≤ normalizer (ChapterE.indexedWeakClosure V R 0 : Set G)) := by
  obtain ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hpoint,hind,hR₀T,hUR₀,hext⟩ :=
    local_nonnormal_component_plane_sylow_extensions d h hab structural previous faithful earlier I K hI hKI hK hnormal
  let P := F.Vi 1 ⊔ c.Zα
  let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
  let R₀ := F.H.pCoreIn 2 ⊔ c.Uα
  have hR₀Y : R₀ ≤ Y₀ := hpoint.le.trans inf_le_left
  obtain ⟨hS₀,hcore₀,he₀,hV₀,_,hW₀⟩ := hext R₀ le_rfl hR₀T (hR₀Y.trans hYn)
  have heY : Y₀ ⊔ R₀ = Y₀ := sup_eq_left.mpr hR₀Y
  rw [heY] at hS₀ hW₀
  obtain ⟨hR₀R,hRT,hJR⟩ := critical_plane_normal_span c hR
  refine ⟨c,hs,hR,hE,hfour,hpoint,hS₀,hV₀,hW₀,hR₀R,hRT,hJR,?_⟩
  intro hRN
  obtain ⟨hS,hcore,he,hV,_,hW⟩ := hext _ hR₀R hRT hRN
  exact ⟨hS,hcore,he,hV,
    sup_le (hJR.trans (ChapterE.normalizer_le_weakClosure_normalizer V _ 0)) hW⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
