module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianAction
public import Theory.SpecificGroups.SymmetricEight.PerfectSylow

/-!
# Normal component images and the S₈ exclusion

The normal point component survives in the faithful action on U/Z(U),
and strict containment of the point residual survives whenever the
component quotient is quasisimple. In degree five this excludes even an
embedding in S₈: the perfect point image already has an A₈-sized section.
In degree four, the full Sylow comparison forces that image to equal A₈,
contradicting its two-core quotient of order 168.

These calculations also exclude the exceptional full GL₄(2) natural-plus-
dual actor in the corrected G.11 catalogue. The actual representation
applications are in NonabelianCases. No exhaustion is assumed here.
Source: Aschbacher--Smith 12.9.4, printed pp.859--860; the G.11 correction
is recorded in docs/quasithin-proof-basis.md.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
open Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The original seven-section survives in the faithful central-quotient actor. -/
theorem point_hat_seven_dvd {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    7 ∣ Nat.card (F.terminalDot (F.Li L 1)) := by
  have hc := point_hat_core_card h hn F hne
  have hd : 7 ∣ Nat.card (F.terminalDot (F.Li L 1) ⧸ pCore 2 (F.terminalDot (F.Li L 1))) := by
    rw [hc]
    split <;> decide
  exact hd.trans (card_quotient_dvd_card _)

/-- In particular, the original point residual has nonzero dotted image. -/
theorem point_hat_ne_bot {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    F.terminalDot (F.Li L 1) ≠ ⊥ := by
  intro he
  have hd := point_hat_seven_dvd h hn F hne
  rw [he,card_bot] at hd
  norm_num at hd

/-- The original point normalizer's two-core is killed by the central-quotient action. -/
theorem point_core_le_hat_kernel {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) : pCore 2 F.H ≤ F.terminalHatAction.ker := by
  let := h.chosen.elementary
  have hJ := h.point_mem_Hz F earlier.alternatives
  have hc := F.localKernel_core_le h.source.simpleQTKE L _ F.H
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  have he : F.uhatAction = F.terminalHatAction :=
    F.terminalHatAction_unique F.uhatAction (fun a u => F.uhatAction_apply_mk a u)
  rw [← he]
  exact hc.trans (F.localTildeAction_ker_le_uhatAction_ker (by have := h.rank; omega))

/-- A quasisimple point component remains a nontrivial normal ordinary component
under the literal map to H/C_H(U/Z(U)). -/
theorem point_hat_component {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hq : IsQuasisimple (C.K1 ⧸ pCore 2 C.K1)) :
    IsComponent F.TerminalHdot (F.terminalDot C.K1) ∧ (F.terminalDot C.K1).Normal := by
  let D := C.K1.subgroupOf F.H
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let e := subgroupOfEquivOfLe C.point_le
  let := hq
  have hqD : IsQuasisimple (D ⧸ pCore 2 D) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hc : D.pCoreIn 2 ≤ q.ker := by
    rw [QuotientGroup.ker_mk']
    exact (pCoreIn_le_of_subnormal 2 C.normal.isSubnormal).trans (point_core_le_hat_kernel h earlier F)
  have hnot : F.terminalDot C.K1 ≠ ⊥ := by
    intro he
    exact point_hat_ne_bot h hn F hne
      (le_bot_iff.mp (he ▸ map_mono (comap_mono C.contains)))
  exact ⟨C.component.isComponent_map_of_twoCore_killed hqD q (QuotientGroup.mk'_surjective _) hc hnot,
    C.normal.map q (QuotientGroup.mk'_surjective _)⟩

/-- In degree five the normal point component has a nontrivial ordinary component
image, without an additional quasisimplicity assumption. -/
theorem five_point_hat_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hne : ¬ IsMulCommutative F.U)
    (C : ComponentGeometry F L) :
    IsComponent F.TerminalHdot (F.terminalDot C.K1) ∧ (F.terminalDot C.K1).Normal :=
  point_hat_component h (Or.inr rfl) earlier F hne C
    (five_endpoint_component_quasisimple h earlier F 1 (Or.inl rfl) C.K1
      ⟨C.point_le,C.component⟩ C.contains)

/-- The strict enlargement of the point residual remains strict after taking the
actual faithful action on U/Z(U). Equal images would force equal components. -/
theorem point_hat_residual_lt_component {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hq : IsQuasisimple (C.K1 ⧸ pCore 2 C.K1)) :
    F.terminalDot (F.Li L 1) < F.terminalDot C.K1 := by
  refine lt_of_le_of_ne (map_mono (comap_mono C.contains)) ?_
  intro he
  let D := C.K1.subgroupOf F.H
  let A := (F.Li L 1).subgroupOf F.H
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let e := subgroupOfEquivOfLe C.point_le
  let := hq
  let : IsQuasisimple (D ⧸ pCore 2 D) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hnot : D.map q ≠ ⊥ := fun hb => point_hat_ne_bot h hn F hne (he.trans hb)
  have hnorm : pCore 2 D ≤ normalizer (A.subgroupOf D : Set D) := by
    intro d hd a
    have hc : (d.val : F.H) ∈ pCore 2 F.H :=
      pCoreIn_le_of_subnormal 2 C.normal.isSubnormal (mem_map_of_mem D.subtype hd)
    have ht : (d.val.val : G) ∈ (T : Subgroup G) :=
      pCore_isPGroup.le_sylow_of_normal
        (T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)) hc
    exact sylow_normalizes_Li h earlier F 1 ht (a.val.val : G)
  have heq : A = D := Theory.GroupTheory.IsCComponent.eq_of_image_eq_of_twoCore_normalizes q C.component
    (comap_mono C.contains) he hnot hnorm
  have heq' := congrArg (map F.H.subtype) heq
  dsimp only [A,D] at heq'
  rw [map_subgroupOf_eq_of_le (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right),
    map_subgroupOf_eq_of_le C.point_le] at heq'
  exact hne (point_span_abelian_of_point_residual_normal h hn earlier F (heq'.symm ▸ C.normal))

/-- In degree five even the exceptional S₈ actor cannot occur. Every perfect
image in S₈ lies in A₈; the original point image already has an A₈-sized quotient,
leaving no room for the strict normal point component. -/
theorem five_point_hat_not_embeds_symmetric_eight
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hne : ¬ IsMulCommutative F.U) :
    ¬ ∃ f : F.TerminalHdot →* Equiv.Perm (Fin 8), Function.Injective f := by
  rintro ⟨f,hf⟩
  obtain ⟨C⟩ := five_componentGeometry h earlier F
  have hq := five_endpoint_component_quasisimple h earlier F 1 (Or.inl rfl)
    C.K1 ⟨C.point_le,C.component⟩ C.contains
  have hlt := point_hat_residual_lt_component h (Or.inr rfl) earlier F hne C hq
  let B := (F.terminalDot (F.Li L 1)).map f
  let D := (F.terminalDot C.K1).map f
  let := point_hat_perfect h (Or.inr rfl) F
  let : Group.IsPerfect B := Group.IsPerfect.map _
  let : IsQuasisimple (F.terminalDot C.K1) :=
    (five_point_hat_component h earlier F hne C).1.2
  let : Group.IsPerfect D := Group.IsPerfect.map _
  have hB : B ≤ alternatingGroup (Fin 8) :=
    le_of_isPerfect_of_index_eq_two B _ alternatingGroup.index_eq_two
  have hD : D ≤ alternatingGroup (Fin 8) :=
    le_of_isPerfect_of_index_eq_two D _ alternatingGroup.index_eq_two
  have hc : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hb : 20160 ≤ Nat.card B := by
    have hh := Nat.le_of_dvd (Nat.card_pos (α := F.terminalDot (F.Li L 1)))
      (card_quotient_dvd_card (pCore 2 (F.terminalDot (F.Li L 1))))
    rw [point_hat_core_card h (Or.inr rfl) F hne,
      if_neg (by decide : ¬ 5 = 4)] at hh
    rwa [card_map_of_injective hf]
  have heB : B = alternatingGroup (Fin 8) := eq_of_le_of_card_ge hB (hc ▸ hb)
  have heBD : B = D := le_antisymm (map_mono hlt.le) (heB.symm ▸ hD)
  exact hlt.ne (map_injective hf heBD)

/-- In degree four the perfect point image has quotient order 168. A full
symmetric Sylow would force it to be A₈, whose factor five cannot lie in its
two-core. This uses the actual full quotient Sylow of the original T. -/
theorem four_point_hat_not_symmetric_eight {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V 4) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U) :
    ¬ Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) := by
  rintro ⟨e⟩
  let C := F.terminalDot (F.Li L 1)
  let B := C.map e.toMonoidHom
  let c : C ≃* B := C.equivMapOfInjective e.toMonoidHom e.injective
  have hc : Nat.card (B ⧸ pCore 2 B) = 168 := by
    have he := (Nat.card_congr (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.toEquiv).trans
      (point_hat_core_card h (Or.inl rfl) F hne)
    exact he
  have h7 : 7 ∣ Nat.card B :=
    (show 7 ∣ 168 by decide).trans (hc ▸ card_quotient_dvd_card (pCore 2 B))
  let := point_hat_perfect h (Or.inl rfl) F
  let : Group.IsPerfect B := Group.IsPerfect.map _
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let Sbase : Sylow 2 F.H := T.subtype (F.invariant 1)
  let S₀ := Sbase.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let S := S₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn₀ : (Sbase : Subgroup F.H) ≤
      normalizer ((F.Li L 1).subgroupOf F.H : Set F.H) := by
    intro t ht b
    exact sylow_normalizes_Li h earlier F 1 ht (b : G)
  have hn₁ : (S₀ : Subgroup F.TerminalHdot) ≤ normalizer (C : Set F.TerminalHdot) :=
    (map_mono hn₀).trans (((F.Li L 1).subgroupOf F.H).le_normalizer_map q)
  have hn₂ : (S : Subgroup (Equiv.Perm (Fin 8))) ≤ normalizer (B : Set _) :=
    (map_mono hn₁).trans (C.le_normalizer_map e.toMonoidHom)
  have he := Theory.SpecificGroups.SymmetricEight.PerfectSylow.eq_alternating_of_seven_dvd
    B S hn₂ h7
  have h5 : 5 ∣ Nat.card B := by
    rw [he,nat_card_alternatingGroup,Nat.card_fin]
    decide
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),hc] at h5
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp h5 with hf | hf
  · exact (by decide : ¬ 5 ∣ 168) hf
  · obtain ⟨a,ha⟩ := (pCore_isPGroup : IsPGroup 2 (pCore 2 B)).exists_card_eq
    rw [ha] at hf
    exact (by decide : ¬ 5 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5)) hf)

/-- Neither original degree permits a full S₈ actor on the nonabelian central
quotient. This also excludes the corrected full-linear-four action row. -/
theorem point_hat_not_symmetric_eight
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    ¬ Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) := by
  rcases hn with rfl | rfl
  · exact four_point_hat_not_symmetric_eight h earlier F hne
  · rintro ⟨e⟩
    exact five_point_hat_not_embeds_symmetric_eight h earlier F hne ⟨e.toMonoidHom,e.injective⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
