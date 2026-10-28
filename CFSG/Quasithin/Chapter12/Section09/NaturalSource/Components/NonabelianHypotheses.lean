module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianGeometry
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import CFSG.Quasithin.ChapterG.Section10.TerminalSource
public import Theory.Representation.ConjugateSpanOrbit

/-!
# The original G.10 hypotheses for the nonabelian natural branch

The commutator with the plane is exactly the marked point. This proves
relative normality of both literal dotted actors in the point-plane image,
and hence of the actor in the original full quotient Sylow. The plane's
conjugate span generates the central quotient. Together with the existing
form, fixed-space and transvection calculations, these facts construct all
G.10.1 fields and the actual SQTK cover, using the unchanged quotient maps.

The seed inclusion is then applied to the surviving orthogonal row in
`NonabelianOrthogonalGeometry`. These are source inputs to the remaining
classification argument; no catalogue exhaustion is asserted here.

Source: Aschbacher--Smith 12.8.12(1--2), 12.8.13(1) and 12.9.4,
printed pp.855--856,859--860.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

private theorem binary_scalar (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hh := ZMod.val_lt a
  have hh' : a.val = 0 ∨ a.val = 1 := by omega
  rcases hh' with hh' | hh'
  · left
    apply ZMod.val_injective
    simpa only [ZMod.val_zero] using hh'
  · right
    apply ZMod.val_injective
    simpa only [ZMod.val_one] using hh'

private theorem plane_span {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (_earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) : F.U = conjugateSpanBy (F.Vi 2) F.H := by
  let := h.chosen.elementary
  exact F.U_eq_plane_span L (by have := h.rank; omega) h.chosen.normalizes
    (F.localKernel_irreducible L (by have := h.rank; omega) h.chosen.normalizes
      (fun _ => ⟨h.naturalMarking⟩))

/-- The original nonabelian span moves the marked plane by precisely its point. -/
theorem nonabelian_plane_commutator {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    ⁅F.U,F.Vi 2⁆ = F.Vi 1 := by
  let := h.chosen.elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  have hc := (F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)).1
  have hle : ⁅F.U,F.Vi 2⁆ ≤ F.Vi 1 :=
    (commutator_mono le_rfl ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))).trans hc
  have hnon : ⁅F.U,F.Vi 2⁆ ≠ ⊥ := fun he =>
    F.binary_U_not_centralizes_plane (plane_span h earlier F) hne
      (commutator_eq_bot_iff_le_centralizer.mp he)
  apply eq_of_le_of_card_ge hle
  have hp : 1 < Nat.card (⁅F.U,F.Vi 2⁆ : Subgroup G) := (one_lt_card_iff_ne_bot _).mpr hnon
  rw [F.card 1 (by omega)]
  omega

/-- Both literal actor images are normal in the actual point-plane image. -/
theorem nonabelian_actors_normal {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) :
    F.terminalDot (F.X g) ≤ F.terminalDot (F.H ⊓ F.Gi 2) ∧
      ((F.terminalDot (F.X g)).subgroupOf (F.terminalDot (F.H ⊓ F.Gi 2))).Normal ∧
      F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.H ⊓ F.Gi 2) ∧
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf
        (F.terminalDot (F.H ⊓ F.Gi 2))).Normal := by
  let := h.chosen.elementary
  let := F.binaryPlane_elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by omega)
  let : Nontrivial (F.Vi 1) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z,hz⟩ := exists_ne (1 : F.Vi 1)
  have hg : F.Vi 1 = zpowers (z : G) := by
    have ht := zpowers_eq_top_of_prime_card hc hz
    have he := congrArg (map (F.Vi 1).subtype) ht
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,Subgroup.subtype_apply] using he.symm
  exact actors_normal_in_dot_H2 F hn z hg
    (fun he => hz (Subtype.ext he)) (nonabelian_plane_commutator h earlier F hne)
    g (F.P_le_G₂ hn L h.chosen.normalizes hgP) F.terminalHatAction
    (fun a u => F.terminalHatAction_apply_mk a u)

/-- The original full Sylow gives G.11's relative normality, with the
same point, actor and faithful quotient map. -/
theorem nonabelian_normalSylow {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (hXT : F.X g ≤ (T : Subgroup G)) :
    ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  let Q := (T.subtype (F.invariant 1)).mapSurjective
    (f := QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  have hn := nonabelian_actors_normal h earlier F hne g hgP
  have hX : F.terminalDot (F.X g) ≤ (Q : Subgroup F.TerminalHdot) :=
    map_mono (comap_mono hXT)
  refine ⟨Q,sylow_fixes_plane_hat_point F v hv hline,hX,?_⟩
  apply (normal_subgroupOf_iff_le_normalizer hX).mpr
  exact (map_mono (comap_mono (le_inf (F.invariant 1) (F.invariant 2)))).trans
    ((normal_subgroupOf_iff_le_normalizer hn.1).mp hn.2.1)

/-- The unique nonzero image of the original plane generates the entire
central quotient under its actual faithful actor. -/
theorem nonabelian_hat_orbit_span {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    Submodule.span (ZMod 2) {w | ∃ a : F.TerminalHdot,
      F.terminalRepresentation a v = w} = ⊤ := by
  let := h.chosen.elementary
  have hPU : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  have hs := conjugateSpan_binary_orbit_span (F.Vi 2) F.H F.U hPU
    (plane_span h earlier F) (QuotientGroup.mk' (center F.U))
    (QuotientGroup.mk'_surjective _) F.terminalHatAction
    (fun a u hu => (F.terminalHatAction_apply_mk a u).symm) v.toMul ?_
  · apply top_unique
    rw [←hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact Submodule.subset_span ⟨QuotientGroup.mk' F.terminalHatAction.ker a,rfl⟩
  · intro u
    have hu : hatElement F (inclusion hPU u) ∈ hatSpace F (F.Vi 2) :=
      ⟨inclusion hPU u,u.property,rfl⟩
    rw [hline] at hu
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hu
    rcases binary_scalar a with rfl | rfl
    · left
      have hh : hatElement F (inclusion hPU u) = 0 := by simpa only [zero_smul] using ha.symm
      exact congrArg (@Additive.toMul F.Uhat) hh
    · right
      have hh : hatElement F (inclusion hPU u) = v := by simpa only [one_smul] using ha.symm
      exact congrArg (@Additive.toMul F.Uhat) hh

/-- Construct the literal G.10.1 configuration from the original
nonabelian source geometry. The actor, smaller actor, form and plane line
are retained; no classification or geometric conclusion is assumed. -/
theorem nonabelian_g10_hypothesis {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
      let := hX
      ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
        ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
        hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
        ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  obtain ⟨hX,B,v,hB,hAlt,hInv,hv,hline,hXT,hiso,htrans,_,hfixed,hWX,hperp,hrank⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  let := hX
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  obtain ⟨hc,hs⟩ := F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)
  have hstab := (F.binary_source_parabolic_action_clauses hn L h.chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT earlier.structural)
    hc hs (plane_span h earlier F) hne
    (F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne)
    g hgP hgH).2.2
  have hk : F.U.subgroupOf F.H ≤ F.terminalHatAction.ker :=
    U_le_action_kernel F F.terminalHatAction (fun a u => F.terminalHatAction_apply_mk a u)
  refine ⟨hX,B,v,?_,hline,nonabelian_normalSylow h earlier F hne g hgP v hv hline hXT⟩
  apply F.terminal_g10_hypothesis g (F.P_le_G₂ hn L h.chosen.normalizes hgP)
    B hB hAlt hInv v hv hline v.property (nonabelian_hat_orbit_span h earlier F v hline)
    (sylow_fixes_plane_hat_point F v hv hline) hiso ?_ hfixed hWX hperp hrank ?_ hstab
  · intro x hx e he
    obtain ⟨φ,_,hφ⟩ := htrans ⟨x,hx⟩
    rw [hφ ⟨e,he⟩,add_sub_cancel_left,hline]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro e he _
    exact hk ((inf_le_left.trans inf_le_left : F.E g ≤ F.U) he)

/-- The faithful actor is an actual quotient of the source two-local
SQTK group, using the unchanged point normalizer and action kernel. -/
def nonabelian_sqtkCover {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n) :
    ChapterG.Section09.SQTKCover K F.TerminalHdot where
  Cover := F.H
  sqtk := h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 1 le_rfl)
  projection := QuotientGroup.mk' F.terminalHatAction.ker
  surjective := QuotientGroup.mk'_surjective _

/-- The original seed is contained in the isotropic intersection. -/
theorem seed_hat_le_intersection {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n)
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hgP : g ∈ F.P L) : hatSpace F V ≤ hatSpace F (F.E g) := by
  let := h.chosen.elementary
  have hVE := F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L h.chosen.normalizes hgP)
  intro v hv
  exact (show hatImage F V ≤ hatImage F (F.E g) from map_mono (comap_mono hVE)) hv

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
