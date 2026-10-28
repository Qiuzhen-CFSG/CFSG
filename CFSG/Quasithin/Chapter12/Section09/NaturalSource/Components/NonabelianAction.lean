module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourThree
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Quotients
public import CFSG.Quasithin.Chapter12.Section08.Terminal.Quotients
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Geometry
public import Theory.SpecificGroups.Alternating.SevenPerfectSylow
public import Theory.GroupTheory.CComponent.QuasisimpleImage

/-!
# The original point residual on the nonabelian central quotient

The seed marking identifies the kernel of L₁ on U/Z(U) as a two-group,
so its intrinsic two-core quotient remains GLₙ₋₁(2). The residual and its
image are perfect. Its full Sylow normalizer excludes the S₇ actor.
The seed image has dimension n−1 and is isotropic in the actual
nondegenerate commutator form, giving dimension at least 2(n−1).

All maps are the literal quotients and conjugation actions of the chosen
flag. These are comparisons for 12.9.4; exhaustion of the action catalogue
and the remaining nonnormal abelianity argument are separate obligations.
Source: Aschbacher--Smith 12.9.4, printed pp.859--860.
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

/-- The kernel of the original point residual on the central quotient is a two-group. -/
theorem point_hat_kernel_le_core {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) :
    (dotMap F F.terminalHatAction (F.Li L 1) ((F.Li_le L 1).trans inf_le_right)).ker ≤
      pCore 2 (F.Li L 1) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient h.rank.1 L h.chosen.normalizes h.naturalMarking
  have hcenter := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne
  have ha : F.uhatAction = F.terminalHatAction :=
    F.terminalHatAction_unique F.uhatAction (fun a u => F.uhatAction_apply_mk a u)
  intro k hk
  rw [dotMap_ker, MonoidHom.mem_ker] at hk
  have hkhat : (⟨k,(F.Li_le L 1 k.property).2⟩ : F.H) ∈ F.uhatAction.ker := by
    rw [ha]
    exact hk
  have hm := (F.mem_uhatAction_ker_iff _).mp hkhat
  rw [← D.seedAction_ker]
  apply (F.mem_tildeAction_ker_iff _ _ _ (h.chosen.le_sylow.trans (F.invariant 1)) _ _).mpr
  intro v hv
  rw [← hcenter]
  refine ⟨?_,hm v (le_conjugateSpanBy V F.H hv)⟩
  exact le_normalizer_iff_commutator_le_right.mp
    ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
    (commutator_mem_commutator k.property hv)

/-- The point-residual image retains its original intrinsic two-core quotient. -/
theorem point_hat_core_equiv {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) :
    Nonempty ((F.Li L 1 ⧸ pCore 2 (F.Li L 1)) ≃*
      (F.terminalDot (F.Li L 1) ⧸ pCore 2 (F.terminalDot (F.Li L 1)))) := by
  let f := dotMap F F.terminalHatAction (F.Li L 1) ((F.Li_le L 1).trans inf_le_right)
  exact ⟨f.pCoreQuotientEquiv (dotMap_surjective _ _ _ _)
    (pCore_isPGroup.of_injective (inclusion (point_hat_kernel_le_core h F hne))
      (inclusion_injective _))⟩

/-- The point image has the same marked binary-linear section as L₁. -/
theorem point_hat_linear {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    Nonempty ((F.terminalDot (F.Li L 1) ⧸ pCore 2 (F.terminalDot (F.Li L 1))) ≃*
      BinaryLinear.OuterCyclic.LinearGroup (n-1)) := by
  let := h.chosen.elementary
  have hi : ComponentIndex n 1 := by
    rcases hn with rfl | rfl
    · exact Or.inr ⟨rfl,Or.inl rfl⟩
    · exact Or.inl ⟨rfl,by decide,by decide⟩
  obtain ⟨d,hd,_,⟨e⟩⟩ := Li_core_linear F h.naturalMarking 1 hi
  have he : d = n-1 := by omega
  rw [he] at e
  exact ⟨(point_hat_core_equiv h F hne).some.symm.trans e⟩

/-- The point residual is perfect at both degrees. -/
theorem point_residual_perfect {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) : Group.IsPerfect (F.Li L 1) := by
  let := h.chosen.elementary
  have hi : ComponentIndex n 1 := by
    rcases hn with rfl | rfl
    · exact Or.inr ⟨rfl,Or.inl rfl⟩
    · exact Or.inl ⟨rfl,by decide,by decide⟩
  let : IsQuasisimple (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) :=
    Li_core_quasisimple F h.naturalMarking 1 hi
  have hh := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 (F.Li L 1)) pCore_isPGroup (Li_twoPerfect F 1)
  let := hh.perfect
  exact Group.IsPerfect.ofSurjective (f := (topEquiv (G := F.Li L 1)).toMonoidHom)
    topEquiv.surjective

/-- The actual dotted point residual remains perfect. -/
theorem point_hat_perfect {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) : Group.IsPerfect (F.terminalDot (F.Li L 1)) := by
  let := point_residual_perfect h hn F
  exact Group.IsPerfect.ofSurjective (f := dotMap F F.terminalHatAction
    (F.Li L 1) ((F.Li_le L 1).trans inf_le_right)) (dotMap_surjective _ _ _ _)

/-- The exact small-degree orders used in the source model comparison. -/
theorem point_hat_core_card {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    Nat.card (F.terminalDot (F.Li L 1) ⧸ pCore 2 (F.terminalDot (F.Li L 1))) =
      if n = 4 then 168 else 20160 := by
  rw [Nat.card_congr (point_hat_linear h hn F hne).some.toEquiv]
  rcases hn with rfl | rfl
  · simp only [Nat.reduceSub]
    rw [← Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 3).toEquiv]
    exact Atlas.Comparisons.Exceptional.sl3Two_card
  · simp only [Nat.reduceSub, if_neg (by decide : ¬ 5 = 4)]
    rw [← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear 4).toEquiv,
      Matrix.card_GL_field]
    decide +kernel

/-- The full faithful actor cannot be S₇: its original perfect point residual
has a seven-section, while the full Sylow normalizes that residual. -/
theorem point_hat_not_symmetric_seven {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) :
    ¬ Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 7)) := by
  rintro ⟨e⟩
  let C := F.terminalDot (F.Li L 1)
  let B := C.map e.toMonoidHom
  let c : C ≃* B := C.equivMapOfInjective e.toMonoidHom e.injective
  have hc : Nat.card (B ⧸ pCore 2 B) = if n = 4 then 168 else 20160 :=
    (Nat.card_congr (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.toEquiv).trans
      (point_hat_core_card h hn F hne)
  have hd : Nat.card (B ⧸ pCore 2 B) ∣ 5040 := by
    have hh := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
    simpa only [Nat.card_perm,Nat.card_fin,Nat.factorial] using hh
  have hn4 : n = 4 := by
    rcases hn with hn4 | hn5
    · exact hn4
    · simp only [hn5,if_neg (by decide : ¬ 5 = 4)] at hc
      rw [hc] at hd
      exact False.elim ((by decide : ¬ 20160 ∣ 5040) hd)
  rw [if_pos hn4] at hc
  have h7 : 7 ∣ Nat.card B :=
    (show 7 ∣ 168 by decide).trans (hc ▸ card_quotient_dvd_card (pCore 2 B))
  have hBne : B ≠ ⊥ := by
    intro he
    rw [he,card_bot] at h7
    norm_num at h7
  have hBproper : B ≠ alternatingGroup (Fin 7) := by
    intro he
    have h5 : 5 ∣ Nat.card B := by
      rw [he,nat_card_alternatingGroup,Nat.card_fin]
      decide
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),hc] at h5
    rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp h5 with hf | hf
    · exact (by decide : ¬ 5 ∣ 168) hf
    · obtain ⟨a,ha⟩ := (pCore_isPGroup : IsPGroup 2 (pCore 2 B)).exists_card_eq
      rw [ha] at hf
      exact (by decide : ¬ 5 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5)) hf)
  let := point_hat_perfect h hn F
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
  have hn₂ : (S : Subgroup (Equiv.Perm (Fin 7))) ≤ normalizer (B : Set _) :=
    (map_mono hn₁).trans (C.le_normalizer_map e.toMonoidHom)
  exact Theory.SpecificGroups.Alternating.SevenPerfectSylow.seven_not_dvd B hBne hBproper S hn₂ h7

/-- The original nonabelian span has an elementary central quotient. -/
theorem nonabelian_hat_elementary {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    IsElementaryAbelian 2 F.Uhat := by
  let := h.chosen.elementary
  have hJ := h.point_mem_Hz F earlier.alternatives
  have ht := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  have hp := F.localKernel_frattini_eq_point h.source.simpleQTKE L _
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F earlier.alternatives) hne
  exact F.uhat_elementary_of_point (by have := h.rank; omega) ht hp

/-- The original seed has dimension n−1 in U/Z(U); the kernel is precisely V₁. -/
theorem nonabelian_seed_hat_finrank {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) [IsElementaryAbelian 2 F.Uhat] :
    Module.finrank (ZMod 2) (hatSpace F V) = n-1 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hc := card_hatImage_mul_card_inf F V (le_conjugateSpanBy V F.H)
  rw [F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne,
    F.card 1 (by have := h.rank; omega), ← card_hatSpace F V,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  have hv : Nat.card V = 2^n := F.last ▸ F.card n le_rfl
  rw [hv] at hc
  simp only [pow_one,←pow_succ] at hc
  have hd := Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  omega

/-- The natural seed is isotropic for the actual nondegenerate commutator form,
so the central quotient has at least twice its dimension. -/
theorem nonabelian_hat_rank {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] :
    2*(n-1) ≤ Module.finrank (ZMod 2) (Additive F.Uhat) := by
  let := h.chosen.elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  have hJ := h.point_mem_Hz F earlier.alternatives
  have ht := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H
    hn h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  have hp := F.localKernel_frattini_eq_point h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives) hne
  have hcomm := (F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)).1
  let B := F.localKernel_markedForm (by omega) ht hp hcomm
  have hiso : hatSpace F V ≤ B.form.orthogonal (hatSpace F V) := by
    intro x hx y hy
    obtain ⟨a,ha,hae⟩ := (show x.toMul ∈ hatImage F V from hx)
    obtain ⟨b,hb,hbe⟩ := (show y.toMul ∈ hatImage F V from hy)
    have hba : ⁅(b : G),(a : G)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (congrArg Subtype.val (mul_comm (⟨b,hb⟩ : V) ⟨a,ha⟩))
    have he := B.evaluation b a
    have hz : (⟨⁅(b : G),(a : G)⁆,hcomm (commutator_mem_commutator b.property a.property)⟩ : F.Vi 1) = 1 :=
      Subtype.ext hba
    rw [hz,map_one] at he
    change B.form (Additive.ofMul (QuotientGroup.mk' (center F.U) b))
      (Additive.ofMul (QuotientGroup.mk' (center F.U) a)) = 0 at he
    simpa only [hae,hbe,ofMul_toMul] using he
  have hi := Submodule.finrank_mono hiso
  have hd := B.form.finrank_add_finrank_orthogonal' (hatSpace F V)
  rw [B.nondegenerate.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at hd
  rw [nonabelian_seed_hat_finrank h F hne] at hi hd
  omega

/-- The small-dimensional G.11 rows cannot arise in either original degree. -/
theorem point_span_abelian_of_hat_rank_le_four {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat]
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 4) :
    IsMulCommutative F.U := by
  by_contra hne
  have hb := nonabelian_hat_rank h earlier F hne
  omega

/-- Any surviving six-dimensional central-quotient action has original degree four. -/
theorem nonabelian_degree_four_of_hat_rank_le_six {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hne : ¬ IsMulCommutative F.U) [IsElementaryAbelian 2 F.Uhat]
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 6) : n = 4 := by
  have hb := nonabelian_hat_rank h earlier F hne
  omega

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
