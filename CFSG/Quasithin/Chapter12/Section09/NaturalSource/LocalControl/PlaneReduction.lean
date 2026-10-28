module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointControl
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.Movement
public import CFSG.Quasithin.Chapter12.Section08.Terminal.ThreeRank
public import Theory.GroupTheory.Commutator.CentralizerSylowSupplement

/-!
# The original plane-centralizer reduction

Let D be the literal kernel of the G₁-action on K₁/O₂(K₁). The proved
point bound puts D in M₁, hence in N_G(V). Its commutators with L₁ lie
in O₂(L₁). The full natural action on V/V₁ has trivial centralizer,
so D fixes V/V₁. Normality extends this to U/V₁, and the exact local
kernel theorem puts D in O₂(G₁). Thus G₁=K₁T.

The original plane has order two modulo V₁. Consequently its tilded
centralizer is G₁ intersect G₂, and the central elementary commutator
layer gives C_G(V₂)T. Define Y literally as its intersection with K₁T.
Then Y=C_{K₁T}(V₂)T=G₁ intersect G₂, contains the original Sylow and
point/plane intersection, and has three-rank at most one. Perfectness
of K₁ and its proved core movement make Y proper in K₁T.

Failure of the plane-centralizer bound constructs the actual escaping
join YL₁ in Hz. Conversely Y≤L₁T supplies that bound and the unchanged
LocalControl on the same flag. The source overgroup-lattice argument
and four-dimensional module contradiction must still prove this
containment; this reduction does not assert LocalControlInput.

The definition of Y is exposed because its literal intersection formula
is part of the source interface, used by the downstream model comparison.
Source: Aschbacher--Smith 12.9.7, printed p.862 of refs/quasithin.pdf,
using the original 12.8.4(4) kernel and 12.9.5--6 point-control results.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original quotient-action kernel fixes the natural point quotient. -/
theorem point_centralizer_fixes_tilde_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    F.tilde (pointQuotientCentralizer C) ≤ centralizer (F.tilde V : Set F.G₁tilde) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let D := pointQuotientCentralizer C
  have hDH : D ≤ F.H := map_subtype_le _
  have hDM := point_quotient_centralizer_le_normalizer h hn earlier F hab C
  have hDV : D ≤ normalizer (V : Set G) :=
    (le_inf hDM hDH).trans (h.flag_normalizer_le earlier.structural F le_rfl
      (by rcases hn with rfl | rfl <;> decide)) |>.trans inf_le_right
  let J := D ⊔ F.Li L 1
  have hJH : J ≤ F.H := sup_le hDH ((F.Li_le L 1).trans inf_le_right)
  have hJV : J ≤ normalizer (V : Set G) :=
    sup_le hDV ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
  obtain ⟨M⟩ := F.naturalSeedMarking_of_ambient h.rank.1 L h.chosen.normalizes h.naturalMarking
  let a := F.tildeAction J V hJH hJV
  let f : J →* LinearGroup (n-1) :=
    { toFun := fun j => M.coordinates.symm.trans
        ((a j).toAdditive.toLinearEquiv (fun c x => ZMod.map_smul (a j).toAdditive c x))
          |>.trans M.coordinates
      map_one' := by
        apply LinearEquiv.ext
        intro v
        change M.coordinates (Additive.ofMul (a 1 (M.coordinates.symm v).toMul)) = v
        rw [map_one]
        exact M.coordinates.apply_symm_apply v
      map_mul' := by
        intro j k
        apply LinearEquiv.ext
        intro v
        change M.coordinates (Additive.ofMul (a (j*k) (M.coordinates.symm v).toMul)) =
          M.coordinates (Additive.ofMul (a j (M.coordinates.symm
            (M.coordinates (Additive.ofMul (a k (M.coordinates.symm v).toMul)))).toMul))
        rw [M.coordinates.symm_apply_apply,map_mul]
        rfl }
  have hf (k : F.Li L 1) : f (inclusion le_sup_right k) = M.naturalActor k := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨v,rfl⟩ := M.coordinates.surjective v
    change M.coordinates (Additive.ofMul (a (inclusion le_sup_right k)
      (M.coordinates.symm (M.coordinates v)).toMul)) = _
    rw [M.coordinates.symm_apply_apply]
    exact M.equivariant k v
  have hcore (x : J) (hx : (x : G) ∈ (F.Li L 1).pCoreIn 2) : f x = 1 := by
    obtain ⟨k,hk,he⟩ := hx
    have hex : inclusion (show F.Li L 1 ≤ J from le_sup_right) k = x := Subtype.ext he
    rw [←hex,hf]
    change (M.quotientEquiv (QuotientGroup.mk' (pCore 2 (F.Li L 1)) k)).val = 1
    have hkq : QuotientGroup.mk' (pCore 2 (F.Li L 1)) k = 1 :=
      (QuotientGroup.eq_one_iff k).mpr hk
    rw [hkq,map_one]
    rfl
  have hd (d : D) : f (inclusion le_sup_left d) = 1 := by
    have hc : f (inclusion le_sup_left d) ∈ center (LinearGroup (n-1)) := by
      apply Subgroup.mem_center_iff.mpr
      intro b
      obtain ⟨k,rfl⟩ := M.naturalActor_surjective (by rcases hn with rfl | rfl <;> decide) b
      have he := hcore ⁅inclusion (show D ≤ J from le_sup_left) d,
        inclusion (show F.Li L 1 ≤ J from le_sup_right) k⁆
          (point_quotient_centralizer_residual_commutator h earlier F C
            (commutator_mem_commutator d.property k.property))
      rw [map_commutatorElement,hf,commutatorElement_eq_one_iff_mul_comm] at he
      exact he.symm
    let e := (slEquivLinear (n-1)).symm
    have he : e (f (inclusion le_sup_left d)) ∈ center _ :=
      (centerCongr e ⟨_,hc⟩).property
    rw [binary_center_eq_bot (by rcases hn with rfl | rfl <;> decide),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  rintro q ⟨d,hdD,rfl⟩
  let d' : D := ⟨d,hdD⟩
  have ha : a (inclusion le_sup_left d') = 1 := by
    apply MulEquiv.ext
    intro v
    change a (inclusion le_sup_left d') v = v
    apply Additive.ofMul.injective
    apply M.coordinates.injective
    have hh := congrArg (fun g : LinearGroup (n-1) => g (M.coordinates (Additive.ofMul v))) (hd d')
    change M.coordinates (Additive.ofMul (a (inclusion le_sup_left d')
      (M.coordinates.symm (M.coordinates (Additive.ofMul v))).toMul)) =
        M.coordinates (Additive.ofMul v) at hh
    simpa only [M.coordinates.symm_apply_apply, toMul_ofMul] using hh
  have hker : inclusion (show D ≤ J from le_sup_left) d' ∈ a.ker := ha
  rw [F.tildeAction_ker] at hker
  exact hker

/-- Normality extends the same kernel calculation to the entire point span. -/
theorem point_centralizer_fixes_tilde_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    F.tilde (pointQuotientCentralizer C) ≤ centralizer (F.tilde F.U : Set F.G₁tilde) := by
  let := h.chosen.elementary
  change F.tilde (pointQuotientCentralizer C) ≤ centralizer (F.tilde (F.UH F.H) : Set F.G₁tilde)
  rw [F.tilde_UH_eq_span F.H le_rfl]
  apply le_centralizer_conjugateSpanBy_of_normalizes _ _ _ _
    (point_centralizer_fixes_tilde_seed h hn earlier F hab C)
  exact F.tilde_normalizes F.H _ (point_quotient_centralizer_normal F C)

/-- The literal local-kernel theorem puts D in O₂(G₁). -/
theorem point_centralizer_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    pointQuotientCentralizer C ≤ F.H.pCoreIn 2 := by
  let := h.chosen.elementary
  have hj := h.point_mem_Hz F earlier.alternatives
  have hHU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  have hk : (F.tildeAction F.H F.U le_rfl hHU).ker = pCore 2 F.H :=
    F.localKernel_eq_pCore h.source.simpleQTKE L (normalizer (L : Set G)) F.H
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    rfl (h.maximal_unique earlier.structural earlier.uniqueness).2
    (h.seed_centralizer_le earlier.structural earlier.uniqueness) h.centralizer_L hj
  have hc := point_centralizer_fixes_tilde_span h hn earlier F hab C
  intro x hx
  obtain ⟨x,hx,rfl⟩ := hx
  have hxk : x ∈ (F.tildeAction F.H F.U le_rfl hHU).ker := by
    rw [F.tildeAction_ker]
    exact hc (mem_map_of_mem F.tildeProjection (mem_map_of_mem F.H.subtype hx))
  exact mem_map_of_mem F.H.subtype (hk ▸ hxk)

/-- The original point normalizer is the full component-Sylow join. -/
theorem point_normalizer_eq_point_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    F.H = C.K1 ⊔ (T : Subgroup G) := by
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    exact hh.trans_eq (map_subgroupOf_eq_of_le (F.invariant 1))
  have hDT := (point_centralizer_le_point_core h hn earlier F hab C).trans hQT
  rw [←point_normalizer_decomposition F C
    (point_outer_two_of_local_models F C (point_models_of_abelian h hn earlier F hab C)),
    sup_assoc,sup_eq_right.mpr hDT]

/-- The original plane has order two modulo the original point. -/
theorem tilde_plane_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (F : InvariantFlag T V n) : Nat.card (F.tilde (F.Vi 2)) = 2 := by
  let := h.chosen.elementary
  have hPH : F.Vi 2 ≤ F.H := (F.le_seed 2).trans (h.chosen.le_sylow.trans (F.invariant 1))
  let q := F.tildeMap (F.Vi 2) hPH
  have hk : q.ker = (F.Vi 1).subgroupOf (F.Vi 2) := by
    ext x
    change F.tildeMap (F.Vi 2) hPH x = 1 ↔ _
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hcard : Nat.card q.ker = 2 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe (F.monotone (by decide : 1 ≤ 2))).toEquiv]
    simpa using F.card 1 (by have := h.rank; omega)
  have hc := q.ker.card_mul_index
  rw [hcard,index_ker,q.range_eq_top_of_surjective (F.tildeMap_surjective _ hPH),Nat.card_congr (topEquiv).toEquiv] at hc
  have hp := F.card 2 (by have := h.rank; omega)
  rw [hp] at hc
  omega

/-- Centralizing the tilded plane is exactly preserving both original flag terms. -/
theorem point_plane_eq_tilde_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (F : InvariantFlag T V n) :
    F.H ⊓ F.Gi 2 = F.terminalTildePlaneCentralizer := by
  let := h.chosen.elementary
  have hPH : F.Vi 2 ≤ F.H := (F.le_seed 2).trans (h.chosen.le_sylow.trans (F.invariant 1))
  apply le_antisymm ?_ (le_inf F.terminalTildePlaneCentralizer_le_H
    (F.terminalTildePlaneCentralizer_le_G₂ hPH))
  have hnorm := F.tilde_normalizes (F.H ⊓ F.Gi 2) (F.Vi 2) inf_le_right
  have hcent := hnorm.trans
    (normalizer_le_centralizer_of_card_two _ (tilde_plane_card h F))
  intro x hx
  exact ⟨⟨x,hx.1⟩,hcent (mem_map_of_mem F.tildeProjection hx),rfl⟩

/-- The source tilded-plane centralizer is supplemented by the original Sylow. -/
theorem tilde_plane_centralizer_eq_centralizer_sup_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (F : InvariantFlag T V n) :
    F.terminalTildePlaneCentralizer = centralizer (F.Vi 2 : Set G) ⊔ (T : Subgroup G) := by
  let := h.chosen.elementary
  let E := F.terminalTildePlaneCentralizer
  have hTH : (T : Subgroup G) ≤ E := by
    change (T : Subgroup G) ≤ F.terminalTildePlaneCentralizer
    rw [←point_plane_eq_tilde_centralizer h F]
    exact le_inf (F.invariant 1) (F.invariant 2)
  have hPH : F.Vi 2 ≤ F.H := (F.le_seed 2).trans (h.chosen.le_sylow.trans (F.invariant 1))
  have hPE : F.Vi 2 ≤ E := (F.le_seed 2).trans (h.chosen.le_sylow.trans hTH)
  have hZE : F.Vi 1 ≤ E := (F.monotone (by decide : 1 ≤ 2)).trans hPE
  let W := (F.Vi 2).subgroupOf E
  let Z := (F.Vi 1).subgroupOf E
  let : W.Normal := (normal_subgroupOf_iff_le_normalizer hPE).mpr
    (F.terminalTildePlaneCentralizer_le_G₂ hPH)
  let : IsElementaryAbelian 2 (F.Vi 1) :=
    IsElementaryAbelian.of_injective (inclusion (F.le_seed 1)) (inclusion_injective _)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf hZE
  have hfix : (⊤ : Subgroup E) ≤ centralizer (Z : Set E) := by
    intro x _ z hz
    apply Subtype.ext
    exact (normalizer_le_centralizer_of_card_two (F.Vi 1)
      (by simpa using F.card 1 (by have := h.rank; omega))
        (F.terminalTildePlaneCentralizer_le_H x.property)) z hz
  have hcomm : ⁅W,(⊤ : Subgroup E)⁆ ≤ Z := by
    apply commutator_le.mpr
    intro w hw x _
    exact F.tildePlane_commutator_le_point hPH
      (commutator_mem_commutator hw x.property)
  have hgen := centralizer_sup_sylow_eq_top_of_commutator_le W Z
    (T.subtype hTH) hfix hcomm
  have hc : (centralizer (W : Set E)).map E.subtype = centralizer (F.Vi 2 : Set G) := by
    have hCE : centralizer (F.Vi 2 : Set G) ≤ E := by
      change centralizer (F.Vi 2 : Set G) ≤ F.terminalTildePlaneCentralizer
      rw [←point_plane_eq_tilde_centralizer h F]
      exact le_inf ((centralizer_le (F.monotone (by decide : 1 ≤ 2))).trans
        (Subgroup.centralizer_le_normalizer _)) (Subgroup.centralizer_le_normalizer _)
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩ z hz
      exact congrArg Subtype.val (hy (⟨z,hPE hz⟩ : E) hz)
    · intro hx
      refine ⟨⟨x,hCE hx⟩,?_,rfl⟩
      intro z hz
      exact Subtype.ext (hx z hz)
  have he := congrArg (map E.subtype) hgen
  rw [Subgroup.map_sup,hc,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
    ←MonoidHom.range_eq_map,range_subtype] at he
  exact he.symm

/-- The point-action kernel lies in the original tilded-plane centralizer. -/
theorem point_centralizer_le_tilde_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    pointQuotientCentralizer C ≤ F.terminalTildePlaneCentralizer := by
  have hc := (point_centralizer_fixes_tilde_seed h hn earlier F hab C).trans
    (centralizer_le (map_mono (comap_mono (F.le_seed 2))))
  intro d hd
  obtain ⟨d,hd,rfl⟩ := hd
  exact ⟨d,hc (mem_map_of_mem F.tildeProjection
    (mem_map_of_mem F.H.subtype hd)),rfl⟩

/-- The actual remaining source overgroup inside K₁T. -/
@[expose] def planeCentralizerJoin (F : InvariantFlag T V n) (C : ComponentGeometry F L) : Subgroup G :=
  (C.K1 ⊔ (T : Subgroup G)) ⊓ F.terminalTildePlaneCentralizer

/-- The full tilded centralizer is the product of D with the literal overgroup Y. -/
theorem tilde_plane_centralizer_decomposition
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    pointQuotientCentralizer C ⊔ planeCentralizerJoin F C = F.terminalTildePlaneCentralizer := by
  let D := pointQuotientCentralizer C
  let X := C.K1 ⊔ (T : Subgroup G)
  have hDE := point_centralizer_le_tilde_plane h hn earlier F hab C
  have hDX : D ⊔ X = F.H := by
    rw [show D ⊔ X = (C.K1 ⊔ D) ⊔ (T : Subgroup G) by dsimp [X]; ac_rfl]
    exact point_normalizer_decomposition F C
      (point_outer_two_of_local_models F C (point_models_of_abelian h hn earlier F hab C))
  have hXD : X ≤ normalizer (D : Set G) :=
    (sup_le C.point_le (F.invariant 1)).trans (point_quotient_centralizer_normal F C)
  apply le_antisymm (sup_le hDE inf_le_right)
  intro x hx
  have hxH := F.terminalTildePlaneCentralizer_le_H hx
  rw [←hDX] at hxH
  have hxmul : x ∈ (D : Set G) * (X : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left D X hXD]
    exact hxH
  obtain ⟨d,hd,y,hy,rfl⟩ := hxmul
  have hyE : y ∈ F.terminalTildePlaneCentralizer := by
    simpa only [inv_mul_cancel_left] using F.terminalTildePlaneCentralizer.mul_mem
      (F.terminalTildePlaneCentralizer.inv_mem (hDE hd)) hx
  exact mul_mem_sup hd ⟨hy,hyE⟩

/-- The source overgroup contains the same Sylow and lies in the plane normalizer. -/
theorem planeCentralizerJoin_placements
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    (T : Subgroup G) ≤ planeCentralizerJoin F C ∧
      planeCentralizerJoin F C ≤ F.Gi 2 := by
  have hTE : (T : Subgroup G) ≤ F.terminalTildePlaneCentralizer := by
    rw [←point_plane_eq_tilde_centralizer h F]
    exact le_inf (F.invariant 1) (F.invariant 2)
  exact ⟨le_inf le_sup_right hTE,inf_le_right.trans
    (F.terminalTildePlaneCentralizer_le_G₂
      ((F.le_seed 2).trans (h.chosen.le_sylow.trans (F.invariant 1))))⟩

/-- The remaining overgroup Y has three-rank at most one, with no local-control premise. -/
theorem planeCentralizerJoin_three_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    primeRank 3 (planeCentralizerJoin F C) ≤ 1 := by
  let := h.chosen.elementary
  let := F.binaryPlane_elementary
  have hm := point_core_moves_plane_of_controlled_models h hn earlier F C
    (point_quotient_centralizer_le_normalizer h hn earlier F hab C)
    (point_models_of_abelian h hn earlier F hab C)
  have hr := plane_centralizer_three_rank_le_one h earlier F
    (point_core_moves_plane_of_component C hm)
  apply (primeRank_le_iff_elementary_card_le (planeCentralizerJoin F C)).mpr
  intro B hB
  let := hB
  let A := B.map (planeCentralizerJoin F C).subtype
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map_subtype
  have hAE : A ≤ F.terminalTildePlaneCentralizer := (map_subtype_le _).trans inf_le_right
  have hAC := F.odd_elementary_centralizes_plane
    ((F.le_seed 2).trans (h.chosen.le_sylow.trans (F.invariant 1)))
    (by simpa using F.card 1 (by have := h.rank; omega))
    (IsElementaryAbelian.isPGroup 2 (F.Vi 2)) A hAE
  let : IsElementaryAbelian 3 (A.subgroupOf (centralizer (F.Vi 2 : Set G))) :=
    IsElementaryAbelian.subgroupOf hAC
  have hb := (primeRank_le_iff_elementary_card_le (centralizer (F.Vi 2 : Set G))).mp hr
    (A.subgroupOf (centralizer (F.Vi 2 : Set G))) inferInstance
  rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv] at hb
  exact (Nat.card_congr (B.equivMapOfInjective (planeCentralizerJoin F C).subtype
    (planeCentralizerJoin F C).subtype_injective).toEquiv).trans_le hb

/-- Containment of the literal Y in the original point parabolic gives the plane bound. -/
theorem plane_centralizer_le_of_join_le_point_parabolic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hY : planeCentralizerJoin F C ≤ F.Li L 1 ⊔ (T : Subgroup G)) :
    centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) := by
  have hCE : centralizer (F.Vi 2 : Set G) ≤ F.terminalTildePlaneCentralizer := by
    rw [tilde_plane_centralizer_eq_centralizer_sup_sylow h F]
    exact le_sup_left
  apply hCE.trans
  rw [←tilde_plane_centralizer_decomposition h hn earlier F hab C]
  exact sup_le (point_quotient_centralizer_le_normalizer h hn earlier F hab C)
    (hY.trans (sup_le (((F.Li_le L 1).trans inf_le_left).trans L.le_normalizer)
      (h.sylow_normalizes earlier.structural)))

/-- A failure of the plane bound gives the source escaping join H=⟨Y,L₁⟩. -/
theorem plane_centralizer_escape_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hfail : ¬ centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    ¬ planeCentralizerJoin F C ≤ F.Li L 1 ⊔ (T : Subgroup G) ∧
      planeCentralizerJoin F C ⊔ F.Li L 1 ∈ F.Hz L (normalizer (L : Set G)) := by
  let Y := planeCentralizerJoin F C
  have hTY := (planeCentralizerJoin_placements h F C).1
  have hYH : Y ≤ F.H := inf_le_right.trans F.terminalTildePlaneCentralizer_le_H
  have hJH : Y ⊔ F.Li L 1 ≤ F.H := sup_le hYH ((F.Li_le L 1).trans inf_le_right)
  have hout : ¬ Y ≤ normalizer (L : Set G) := by
    intro hYM
    apply hfail
    have hE : F.terminalTildePlaneCentralizer ≤ normalizer (L : Set G) := by
      rw [←tilde_plane_centralizer_decomposition h hn earlier F hab C]
      exact sup_le (point_quotient_centralizer_le_normalizer h hn earlier F hab C) hYM
    rw [tilde_plane_centralizer_eq_centralizer_sup_sylow h F] at hE
    exact le_sup_left.trans hE
  have hz : F.Vi 1 ≤ Y ⊔ F.Li L 1 :=
    (F.le_seed 1).trans (h.chosen.le_sylow.trans (hTY.trans le_sup_left))
  have hcard : Nat.card (F.Vi 1) = 2 := by
    simpa using F.card 1 (by have := h.rank; omega)
  have hcore : (Y ⊔ F.Li L 1).pCoreIn 2 ≠ ⊥ := by
    have hp : IsPGroup 2 (F.Vi 1) := IsPGroup.of_card (n := 1) (by simpa using hcard)
    have he := le_pCoreIn_of_normalizes hp hz hJH
    intro heq
    have hbot := le_bot_iff.mp (heq ▸ he)
    rw [hbot,card_bot] at hcard
    contradiction
  refine ⟨fun hY => hfail (plane_centralizer_le_of_join_le_point_parabolic
    h hn earlier F hab C hY),⟨⟨hcore,?_⟩,hJH,fun hJM => hout (le_sup_left.trans hJM)⟩⟩
  intro x hx
  rcases hx with hx | hx
  · exact mem_sup_right hx
  · exact mem_sup_left (hTY hx)

/-- Apply the original subgroup reduction to the unchanged LocalControl record. -/
theorem localControl_of_abelian_and_plane_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hY : planeCentralizerJoin F C ≤ F.Li L 1 ⊔ (T : Subgroup G)) : LocalControl C :=
  localControl_of_centralizers_and_models h hn earlier F C
    (point_quotient_centralizer_le_normalizer h hn earlier F hab C)
    (point_models_of_abelian h hn earlier F hab C)
    (plane_centralizer_le_of_join_le_point_parabolic h hn earlier F hab C hY)

/-- The same Y is the full original point/plane intersection. -/
theorem planeCentralizerJoin_eq_point_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    planeCentralizerJoin F C = F.H ⊓ F.Gi 2 := by
  rw [planeCentralizerJoin,←point_normalizer_eq_point_join h hn earlier F hab C,
    ←point_plane_eq_tilde_centralizer h F,←inf_assoc,inf_idem]

/-- The source equality Y=C_{K₁T}(V₂)T uses the full original Sylow. -/
theorem planeCentralizerJoin_eq_centralizer_sup_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    planeCentralizerJoin F C =
      ((C.K1 ⊔ (T : Subgroup G)) ⊓ centralizer (F.Vi 2 : Set G)) ⊔ (T : Subgroup G) := by
  let X := C.K1 ⊔ (T : Subgroup G)
  let A := centralizer (F.Vi 2 : Set G)
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (F.invariant 2).trans (normalizer_le_normalizer_centralizer (F.Vi 2))
  rw [planeCentralizerJoin,tilde_plane_centralizer_eq_centralizer_sup_sylow h F]
  apply le_antisymm ?_ (sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
    (le_inf le_sup_right le_sup_right))
  intro x hx
  have hxmul : x ∈ (A : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left A (T : Subgroup G) hTA]
    exact hx.2
  obtain ⟨a,ha,t,ht,rfl⟩ := hxmul
  have haX : a ∈ X := by
    simpa only [mul_inv_cancel_right] using X.mul_mem hx.1
      (X.inv_mem (mem_sup_right ht))
  exact mul_mem_sup ⟨haX,ha⟩ ht

/-- The old point/plane intersection lies in the literal remaining overgroup. -/
theorem point_plane_intersection_le_planeCentralizerJoin
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    (F.Li L 1 ⊓ F.Gi 2) ⊔ (T : Subgroup G) ≤ planeCentralizerJoin F C := by
  apply sup_le ?_ (planeCentralizerJoin_placements h F C).1
  apply le_inf (inf_le_left.trans (C.contains.trans le_sup_left))
  rw [←point_plane_eq_tilde_centralizer h F]
  exact le_inf (inf_le_left.trans ((F.Li_le L 1).trans inf_le_right)) inf_le_right

/-- The literal overgroup Y is proper in K₁T. A perfect K₁ preserving the
plane would centralize it and contradict the proved core movement. -/
theorem planeCentralizerJoin_lt_point_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    planeCentralizerJoin F C < C.K1 ⊔ (T : Subgroup G) := by
  let := h.chosen.elementary
  let := C.component.perfect
  let : Group.IsPerfect C.K1 := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe C.point_le).toMonoidHom)
    (subgroupOfEquivOfLe C.point_le).surjective
  refine lt_of_le_of_ne inf_le_left ?_
  intro he
  have hKG : C.K1 ≤ F.Gi 2 := le_sup_left.trans
    (he ▸ (planeCentralizerJoin_placements h F C).2)
  have hc := Components.plane_perfect_centralizes F (by have := h.rank; omega) C.K1 hKG
  have hm := point_core_moves_plane_of_controlled_models h hn earlier F C
    (point_quotient_centralizer_le_normalizer h hn earlier F hab C)
    (point_models_of_abelian h hn earlier F hab C)
  exact hm (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp ((pCoreIn_le 2 C.K1).trans hc)))

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
