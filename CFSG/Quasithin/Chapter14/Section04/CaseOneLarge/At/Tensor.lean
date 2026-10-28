module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.At.Constituents
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SymmetricSeven
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedSource
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedResidualSource
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedCore
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedAmalgam
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.Actor
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.Order
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedSize
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.CommonSource
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.NaturalSource
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.Source

/-!
# The original symmetric-seven and tensor exclusions at G,T

Retain the original parabolic, component, central quotient and tensor
coordinates. The natural constituent supplies a marked partner and the
PSL4(2) order contradiction. The deleted constituent supplies precisely
the Chapter 10 mixed-tensor hypotheses consumed by MixedSizeInput.

The earlier inputs are restricted to the original group and Sylow subgroup.
The universal APIs remain unchanged. The `import all` edges intentionally
reuse the private calculations of the corresponding source implementation;
only deductions depending on the earlier inputs are specialized here.
Source: Aschbacher--Smith, 14.4.2(4--5),10--11; printed pp.1006--1007,1010--1011; refs/quasithin.pdf.
-/

public noncomputable section

/- Specialization of CaseOneLarge/SymmetricSeven.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.SymmetricSeven LargerDimension.LocalAction.Components

open Representation.AlternatingSevenConjugatePair

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_partner_of_symmetric_seven_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* Equiv.Perm (Fin 7)) (D : Pair (Additive F.Uhat))
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      D.representation (starProjection e a) w =
        F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w) :
    Partner T L V F g := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨ι,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm ι hcore hindex
  have hXT := F.X_le_T_of_parabolic_core L g hIG
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN) hsplit
  have hqn := F.binary_source_E_normal_in_core L chosen.normalizes g hgP hgen.symm hcomm
  let := hqn
  have hqe := F.binary_source_quotient_elementary L chosen.normalizes g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  have hpair : ∃ hn : ((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal, letI := hn
      IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸ (F.E g).subgroupOf (F.W ⊔ F.X g)) := by
    have hh : ∃ hn : ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)).Normal, letI := hn
        IsElementaryAbelian 2 (((F.I₂ L).pCoreIn 2 : Subgroup G) ⧸
          (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) := ⟨hqn,hqe⟩
    rwa [hsplit] at hh
  obtain ⟨hn,helem⟩ := hpair
  let := hn
  let := helem
  have hWX := F.commutator_W_X_le_E g
  obtain ⟨_,hx,B,v,hyp,hline,hfix⟩ :=
    source_terminal_marked_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  let := hx
  let f : F.TerminalHdot ≃* Equiv.Perm (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).trans e
  have hmap (A : Subgroup G) : (F.terminalDot A).map f.toMonoidHom =
      (A.subgroupOf F.H).map (starProjection e) := by
    rw [terminalDot,map_map]
    rfl
  have hcard : Nat.card ((F.X g).subgroupOf F.H |>.map (starProjection e)) = 8 := by
    have hc : Nat.card ((F.X g).subgroupOf F.H |>.map (starProjection e)) =
        Nat.card (F.terminalDot (F.X g)) := by
      rw [← hmap,card_map_of_injective f.injective]
    have hpow : Nat.card (F.terminalDot (F.X g)) =
        2 ^ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
      rw [Nat.card_congr Additive.ofMul]
      simpa only [Nat.card_zmod] using
        Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive (F.terminalDot (F.X g)))
    have hu : Nat.card ((F.X g).subgroupOf F.H |>.map (starProjection e)) ≤ 8 := by
      rw [← hmap]
      exact ElementaryGeometry.elementary_card_le (IsElementaryAbelian.map _)
    have hr := (Group.rank_le_of_surjective
      (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
      (QuotientGroup.mk'_surjective _)).trans
      (IsElementaryAbelian.rank_le_finrank (p:=2) (F.terminalDot (F.X g)))
    have hd := hyp.dimension_bound.1
    rw [D.finrank_eq_eight] at hd
    have hl : 3 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hl
    rw [hc,hpow] at hu ⊢
    exact le_antisymm hu hp
  let ca : CentralAction (Q:=F.Uhat) F.H F.U (starProjection e) := {
    coordinates := MulEquiv.refl _
    pair := D
    normalizes := le_normalizer_conjugateSpanBy V F.H
    equivariant := fun a w => by
      rw [he]
      exact congrArg Additive.ofMul (F.terminalHatAction_apply_mk a w) }
  have himage (A : Subgroup G) : ca.image A = hatSpace F A := rfl
  have hcent : center F.U ≤ (F.Vi 2).subgroupOf F.U := by
    rw [center_point F hZ]
    exact comap_mono (F.monotone (by omega : 1 ≤ 2))
  have hcentE : center F.U ≤ (F.E g).subgroupOf F.U := by
    rw [center_point F hZ]
    exact comap_mono ((F.le_seed 1).trans (F.seed_le_E_of_normalizes g (chosen.normalizes hg)))
  have hpn := source_actor_normal_in_point_stabilizer_at d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH v hyp.point_ne_zero hline
  have hact (a : F.TerminalHdot) (w : Additive F.Uhat) :
      D.representation (f a) w = F.terminalRepresentation a w := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact he b w
  let geom : EarlierGeometry ca (T:Subgroup G) (F.Vi 2) F.W (F.X g) := {
    U_le_T := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
    V₂_le_U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
    center_le_V₂ := hcent
    W_le_U := inf_le_left
    W_index := hindex
    N_le_T := hXT
    center_le_E := hcentE
    commutator_le_E := hWX
    s := v
    nonzero := hyp.point_ne_zero
    marked := (himage _).trans hline.symm
    fixed := by
      rintro _ ⟨a,ha,rfl⟩
      exact (he a v).trans (hfix _ ⟨a,ha,rfl⟩)
    image_card := hcard
    image_normal := by
      intro t ht
      have hh : f.symm t ∈ ChapterG.Section10.pointCentralizer F.terminalRepresentation v := by
        change F.terminalRepresentation (f.symm t) v = v
        rw [← hact,f.apply_symm_apply]
        exact ht
      rw [← hmap]
      have hh' := le_normalizer_map _ (mem_map_of_mem f.toMonoidHom
        ((normal_subgroupOf_iff_le_normalizer hpn.1).mp hpn.2 hh))
      simpa only [MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] using hh' }
  exact exists_partner F.H (T:Subgroup G) F.U (F.Vi 2) (F.Li L 1) g
    (T.subtype (F.invariant 1)) (map_subgroupOf_eq_of_le (F.invariant 1)) e ca geom
    (source_first_actor_at d earlier hq chosen structural F g hg).1

theorem source_symmetric_seven_contradiction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T:Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* Equiv.Perm (Fin 7)) (D : Pair (Additive F.Uhat))
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      D.representation (starProjection e a) w =
        F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w) : False :=
  contradiction_of_partner_at d earlier hq chosen structural alternatives classification F hne hZ hlarge
    g hg hgP hgH (source_partner_of_symmetric_seven_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH e D he)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Tensor/DeletedSource.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem source_tensor_point_rank_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    finrank (ZMod 2) (c.image (F.Vi 2)) = 1 := by
  let := chosen.elementary
  have hcard : Nat.card (c.image (F.Vi 2)) = 2 :=
    (c.image_card _).trans (card_plane_hat F (by decide)
      ((source_seed_geometry_at d earlier hq chosen F).2.2 hne))
  let : Finite (c.image (F.Vi 2)) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := c.image (F.Vi 2))
  rw [Nat.card_zmod, hcard] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm

theorem source_tensor_deleted_plane_centralizer_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    second F.H (T : Subgroup G) ≤ centralizer (F.Vi 2 : Set G) := by
  let := chosen.elementary
  have hcent : (center F.U).map F.U.subtype = F.Vi 1 := hZ
  have hfix := TensorDeleted.second_fixes_image c hdel (T.subtype (F.invariant 1))
    (map_subgroupOf_eq_of_le (F.invariant 1)) (F.invariant 2)
    (source_tensor_point_rank_at d earlier hq chosen F hne c)
  have hbound := TensorDeleted.commutator_le_center_of_fixed_image c
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) (second_le _ _) hfix
  rw [hcent] at hbound
  have hp : IsPGroup 2 (F.Vi 1) :=
    (IsElementaryAbelian.isPGroup 2 V).of_injective (inclusion (F.le_seed 1))
      (inclusion_injective _)
  have hH : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  exact A5.second_centralizes_of_two_layers hp ((second_le _ _).trans hH) hbound

theorem source_tensor_deleted_reduction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    XFamily F.H (T : Subgroup G) = {first F.H, second F.H (T : Subgroup G)} ∧
      first F.H ≠ second F.H (T : Subgroup G) ∧
      second F.H (T : Subgroup G) ∉ YFamily F.H T (F.Vi 2) (F.E g) ∧
      F.Li L 1 = first F.H ∧
      second F.H (T : Subgroup G) ≤ centralizer (F.Vi 2 : Set G) ∧
      second F.H (T : Subgroup G) ≤ centralizer (V : Set G) ∧
      second F.H (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      second F.H (T : Subgroup G) ≤ normalizer (F.Li L 2 : Set G) ∧
      second F.H (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G) := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hcent : (center F.U).map F.U.subtype = F.Vi 1 := hZ
  have hplane := source_tensor_deleted_plane_centralizer_at d earlier hq chosen F hne hZ c hdel
  obtain ⟨hpair,hneq⟩ := family_eq_pair_of_model (T.subtype (F.invariant 1))
    (map_subgroupOf_eq_of_le (F.invariant 1)) c.actor_models
  have hnot : second F.H (T : Subgroup G) ∉ YFamily F.H T (F.Vi 2) (F.E g) := by
    intro hy
    have he : movedSpace (F.Vi 2) (second F.H (T : Subgroup G)) = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hplane)
    have hc := hy.2.1
    rw [he, Subgroup.card_bot] at hc
    norm_num at hc
  have hfirst := source_first_actor_at d earlier hq chosen structural F g hg
  have hL : first F.H = F.Li L 1 := A5.first_eq_L₁_of_second_not_mem_Y hpair hfirst.1 hnot
  have hmove : movedSpace (F.Vi 2) (first F.H) = V := by rw [hL]; exact hfirst.2.1
  have hfix := TensorDeleted.second_fixes_first_moved_image c hdel
    (T.subtype (F.invariant 1)) (map_subgroupOf_eq_of_le (F.invariant 1)) (F.invariant 2)
    (source_tensor_point_rank_at d earlier hq chosen F hne c)
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))
  rw [hmove] at hfix
  have hbound := TensorDeleted.commutator_le_center_of_fixed_image c
    (le_conjugateSpanBy V F.H) (second_le _ _) hfix
  rw [hcent] at hbound
  have hp : IsPGroup 2 (F.Vi 1) :=
    (IsElementaryAbelian.isPGroup 2 V).of_injective (inclusion (F.le_seed 1))
      (inclusion_injective _)
  have hH : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hV := A5.second_centralizes_of_two_layers hp ((second_le _ _).trans hH) hbound
  have hM := hV.trans (h.seed_centralizer_le_at structural)
  obtain ⟨hcomm,hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  obtain ⟨e,_,_,_,hIG,hIN,_⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural) hcomm hsquare
    (source_seed_geometry_at d earlier hq chosen F).2.1 hne g hgP hgH
  have hI := (hplane.trans (Subgroup.centralizer_le_normalizer _)).trans
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN)
  have hLN : (L.subgroupOf (normalizer (L : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  have hL₂ := A5.second_normalizes_L₂ L.le_normalizer hLN hM hplane
    (LargerDimension.LocalAction.NaturalFlags.Li_eq_residual F 2)
  exact ⟨hpair,hneq,hnot,hL.symm,hplane,hV,hM,hL₂,hI⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Tensor/DeletedResidualSource.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem source_tensor_deleted_component_not_centralizes_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    ¬ component F.H ≤ centralizer (F.Vi 2 : Set G) := by
  intro hc
  have hr := source_tensor_point_rank_at d earlier hq chosen F hne c
  rw [TensorDeleted.image_eq_bot_of_component_centralizes c hdel hc, finrank_bot] at hr
  omega

theorem source_tensor_deleted_not_normalizes_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    ¬ F.I₂ L ≤ normalizer (component F.H : Set G) := by
  let := chosen.elementary
  intro hn
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  obtain ⟨_, _, _, _, _, _, _, _, hfactor, hPH, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare
      (source_seed_geometry_at d earlier hq chosen F).2.1 hne g hgP hgH
  have hPN : F.P L ≤ normalizer (component F.H : Set G) := by
    rw [hfactor]
    exact sup_le (hPH.trans (component_normalized F.H)) hn
  have hHZ : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hKZ : component F.H ≤ centralizer (F.Vi 1 : Set G) :=
    (map_subtype_le _).trans hHZ
  have hspan := le_centralizer_conjugateSpanBy_of_normalizes
    (component F.H) (F.Vi 1) (F.P L) hPN hKZ
  have hplane : F.Vi 2 ≤ conjugateSpanBy (F.Vi 1) (F.P L) := by
    rw [← F.binary_plane_point_span (by decide) L chosen.normalizes g hgP hgH]
    refine sup_le (le_conjugateSpanBy _ _) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.subset_closure ⟨g⁻¹, (F.P L).inv_mem hgP, z, hz, by simp⟩
  exact source_tensor_deleted_component_not_centralizes_at d earlier hq chosen F hne c hdel
    (hspan.trans (centralizer_le hplane))

theorem source_tensor_deleted_no_small_component_orbit_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent)
    {J : Subgroup G} (hIJ : F.I₂ L ≤ J) (hKJ : component F.H ≤ J) :
    ¬ ((component F.H).subgroupOf J).Normal ∧
      (normalizer ((component F.H).subgroupOf J : Set J)).index ≠ 2 := by
  let := chosen.elementary
  have exclude (ho : ((component F.H).subgroupOf J).Normal ∨
      (normalizer ((component F.H).subgroupOf J : Set J)).index = 2) : False := by
    let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
    obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
    obtain ⟨_, hres, _⟩ :=
      F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
        (h.centralizer_LT_at structural) hcomm hsquare
        (source_seed_geometry_at d earlier hq chosen F).2.1 hne g hgP hgH
    have hRJ : twoResidual (F.P L) ≤ J := le_sup_left.trans (hres.ge.trans hIJ)
    have hr := A5.residual_normalizes_of_small_orbit hKJ hRJ ho
    rw [twoResidual_idempotent] at hr
    apply source_tensor_deleted_not_normalizes_component_at d earlier hq chosen structural
      alternatives F hne g hgP hgH c hdel
    rw [hres]
    exact sup_le hr (F.U_le_H.trans (component_normalized F.H))
  exact ⟨fun hn => exclude (.inl hn), fun hi => exclude (.inr hi)⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Tensor/DeletedCore.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction.Components

open ChapterA.Section04

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem source_tensor_deleted_overgroup_core_eq_bot_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent)
    {J : Subgroup G} (hKJ : component F.H ≤ J) (hTJ : (T : Subgroup G) ≤ J)
    (hIJ : F.I₂ L ≤ J) : J.pCoreIn 2 = ⊥ := by
  by_contra hcore
  exact (source_tensor_deleted_no_small_component_orbit_at d earlier hq chosen structural
    alternatives F hne g hgP hgH c hdel hIJ hKJ).1
    (source_tensor_component_normal_in_local_overgroup d chosen classification F c hKJ hTJ hcore)

theorem source_tensor_deleted_sylow_join_core_eq_bot_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    (A5.generated F.H (F.I₂ L) ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥ :=
  source_tensor_deleted_overgroup_core_eq_bot_at d earlier hq chosen structural alternatives
    classification F hne g hgP hgH c hdel (le_sup_right.trans le_sup_left) le_sup_right
    (le_sup_left.trans le_sup_left)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Tensor/DeletedAmalgam.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction.Components

open ChapterA.Section04

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem source_tensor_deleted_amalgam_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    ChapterF.Source.HypothesisF11 ![component F.H, F.I₂ L] (T : Subgroup G) := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  obtain ⟨e, _, hgen, _, hIG, hIN, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare
      (source_seed_geometry_at d earlier hq chosen F).2.1 hne g hgP hgH
  have hTK : (T : Subgroup G) ≤ normalizer (component F.H : Set G) :=
    (F.invariant 1).trans (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.H (solvableResidual F.H)))
  have hTI : (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G) :=
    (F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN)
  have hSylK : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ component F.H) (component F.H) :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype (F.invariant 1), map_subgroupOf_eq_of_le (F.invariant 1)⟩
      (map_subtype_le _) (TensorDeleted.component_isCComponent (starComponentEquiv hAD c.actor)).subnormal
  have hSylI : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ F.I₂ L) (F.I₂ L) :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype (F.invariant 2), map_subgroupOf_eq_of_le (F.invariant 2)⟩ hIG hIN.isSubnormal
  have hBI : ChapterF.Source.borel (F.I₂ L) (T : Subgroup G) = (T : Subgroup G) ⊓ F.I₂ L := by
    convert ChapterF.Source.borel_eq_of_cubic_local_sylow _ _ hSylI e using 1
    simp only [ChapterF.Source.borel, inf_assoc, inf_idem]
  have hsecond : second F.H (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G) :=
    (source_tensor_deleted_reduction_at d earlier hq chosen structural alternatives F hne hZ
      g hg hgP hgH c hdel).2.2.2.2.2.2.2.2
  have hBK : borel F.H (T : Subgroup G) ≤ second F.H (T : Subgroup G) ⊔ (T : Subgroup G) :=
    le_embedded_pResidual_sup_sylow_of_normalizes T _ (borel_T_normalized (F.invariant 1))
  have hcross : borel F.H (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G) :=
    hBK.trans (sup_le hsecond hTI)
  have hcore := source_tensor_deleted_sylow_join_core_eq_bot_at d earlier hq chosen
    structural alternatives classification F hne g hgP hgH c hdel
  let eK := TensorDeleted.componentQuotient (starComponentEquiv hAD c.actor)
  have hmodelK : ChapterF.Source.IsRankOneModel (coreQuotient (component F.H)) := by
    apply ChapterF.Source.IsRankOneModel.linear 2 (by decide)
    refine ⟨GaloisField 2 2, inferInstance, inferInstance, ?_, ?_⟩
    · rw [GaloisField.card 2 2 (by decide)]
    · obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
        (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
      exact ⟨eK.trans a.symm⟩
  have hmodelI : ChapterF.Source.IsRankOneModel (coreQuotient (F.I₂ L)) := by
    obtain ⟨a⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two
      (K := ZMod 2) (by simp)
    exact .linear 1 (by decide) ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨e.trans a.symm⟩⟩
  have hchar (A : Subgroup G) (hTA : (T : Subgroup G) ≤ A) (hQ : A.pCoreIn 2 ≠ ⊥) :
      generalizedFitting A = pCore 2 A :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (d.qtke.evenCharacteristic T) ⟨hQ, hTA⟩))
  refine { finite_S := inferInstance
           S_isP := T.isPGroup'
           S_normalizes := ?_
           sylow := ?_
           quotient := ?_
           cross := ?_
           twoCore_free := ?_
           characteristic_two := ?_ }
  · intro i; fin_cases i
    · exact hTK
    · exact hTI
  · intro i; fin_cases i
    · exact hSylK
    · exact hSylI
  · intro i; fin_cases i
    · exact hmodelK
    · exact hmodelI
  · intro i; fin_cases i
    · change ChapterF.Source.borel (F.I₂ L) (T : Subgroup G) ≤ _
      rw [hBI]
      exact inf_le_left.trans hTK
    · exact hcross
  · change pCore 2 (component F.H ⊔ F.I₂ L ⊔ (T : Subgroup G) : Subgroup G) = ⊥
    rw [sup_comm (component F.H) (F.I₂ L)]
    exact (map_eq_bot_iff_of_injective _
      (A5.generated F.H (F.I₂ L) ⊔ (T : Subgroup G)).subtype_injective).mp hcore
  · intro i; fin_cases i
    · change generalizedFitting (component F.H ⊔ (T : Subgroup G) ⊔
        ChapterF.Source.borel (F.I₂ L) (T : Subgroup G) : Subgroup G) =
        pCore 2 (component F.H ⊔ (T : Subgroup G) ⊔
          ChapterF.Source.borel (F.I₂ L) (T : Subgroup G) : Subgroup G)
      rw [hBI, sup_eq_left.mpr (show (T : Subgroup G) ⊓ F.I₂ L ≤
        component F.H ⊔ (T : Subgroup G) from inf_le_left.trans le_sup_right)]
      exact hchar _ le_sup_right (source_tensor_component_local chosen F c).2.2
    · let A := F.I₂ L ⊔ (T : Subgroup G) ⊔ borel F.H (T : Subgroup G)
      change generalizedFitting A = pCore 2 A
      have hAG : A ≤ F.Gi 2 := sup_le (sup_le hIG (F.invariant 2))
        (hBK.trans (sup_le
          ((source_tensor_deleted_plane_centralizer_at d earlier hq chosen F hne hZ c hdel).trans
            (Subgroup.centralizer_le_normalizer _)) (F.invariant 2)))
      have hPA : F.Vi 2 ≤ A := ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)).trans
        ((le_sup_left.trans hgen.ge).trans (le_sup_left.trans le_sup_left))
      have hp : IsPGroup 2 (F.Vi 2) :=
        (IsElementaryAbelian.isPGroup 2 V).of_injective (inclusion (F.le_seed 2)) (inclusion_injective _)
      have hQ := le_pCoreIn_of_normalizes hp hPA hAG
      have hneQ : A.pCoreIn 2 ≠ ⊥ := by
        intro he
        have heP := bot_unique (he ▸ hQ)
        have hc := F.card 2 (by decide)
        rw [heP, card_bot] at hc
        norm_num at hc
      exact hchar A (le_sup_right.trans le_sup_left) hneQ

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Tensor/Actor.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative TensorProduct

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]


theorem source_tensor_actor_card_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    IsElementaryAbelian 2 (star F.H (F.X g)) ∧
      Nat.card (star F.H (F.X g)) = 8 := by
  obtain ⟨heU, hx, B, v, hyp⟩ :=
    source_terminal_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let := hx
  let f : F.TerminalHdot ≃* coreQuotient F.H :=
    QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)
  have hm : (F.terminalDot (F.X g)).map f.toMonoidHom = star F.H (F.X g) := by
    rw [terminalDot, map_map]
    rfl
  have he : IsElementaryAbelian 2 (star F.H (F.X g)) := by
    rw [← hm]
    exact IsElementaryAbelian.map f.toMonoidHom
  let := he
  let e := TensorGeometry.linearCoordinates c
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 := by
    rw [e.finrank_eq, Module.finrank_tensorProduct, BinaryPermutation.finrank_core,
      Fintype.card_fin, c.constituent_model.finrank_four]
  have hr := (Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (QuotientGroup.mk'_surjective _)).trans
    (IsElementaryAbelian.rank_le_finrank (p:=2) (F.terminalDot (F.X g)))
  have hb := hyp.dimension_bound.1
  rw [hd] at hb
  have hl : 3 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by omega
  have hpow : Nat.card (star F.H (F.X g)) =
      2 ^ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
    rw [← hm, card_map_of_injective f.injective, Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive (F.terminalDot (F.X g)))
  have hD : primeRank 2 D ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 D.subtype D.subtype_injective).trans
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
  have hprod : primeRank 2 (Three × D) ≤ 3 := by
    rw [primeRank_prod_eq_add]
    have h3 := Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricThree_primeRank_le_one
    change primeRank 2 Three ≤ 1 at h3
    omega
  have hu := (primeRank_le_iff_elementary_card_le (Three × D)).mp hprod
    ((star F.H (F.X g)).map c.actor.toMonoidHom) (IsElementaryAbelian.map c.actor.toMonoidHom)
  rw [card_map_of_injective c.actor.injective] at hu
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hl
  exact ⟨he, le_antisymm hu (by simpa only [← hpow] using hp)⟩

theorem source_tensor_actor_normal_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    c.actorImage (F.X g) ≤ c.pointCentralizer (F.Vi 2) ∧
      ((c.actorImage (F.X g)).subgroupOf (c.pointCentralizer (F.Vi 2))).Normal := by
  obtain ⟨heU, hx, B, v, hyp, hline, hfix⟩ :=
    source_terminal_marked_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let e := TensorGeometry.linearCoordinates c
  let f : F.TerminalHdot ≃* Three × D :=
    (QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).trans c.actor
  have hm (A : Subgroup G) : (F.terminalDot A).map f.toMonoidHom = c.actorImage A := by
    rw [terminalDot, map_map]
    change (A.subgroupOf F.H).map _ =
      ((A.subgroupOf F.H).map (QuotientGroup.mk' _)).map c.actor.toMonoidHom
    rw [map_map]
    rfl
  have ha (a : F.TerminalHdot) (w : Additive F.Uhat) :
      e (F.terminalRepresentation a w) = sourceTensorAction c.constituent (f a) (e w) := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact TensorGeometry.coordinates_equivariant c b w
  have hP : c.image (F.Vi 2) = Submodule.span (ZMod 2) {e v} := by
    rw [TensorGeometry.image_eq_map, ← hline, Submodule.map_span, Set.image_singleton]
    rfl
  have hpc : (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).map
      f.toMonoidHom = c.pointCentralizer (F.Vi 2) := by
    ext b
    have hiff : b ∈ c.pointCentralizer (F.Vi 2) ↔
        sourceTensorAction c.constituent b (e v) = e v := by
      change (b ∈ (⊤ : Subgroup (Three × D)) ∧
        ∀ w ∈ c.image (F.Vi 2), sourceTensorAction c.constituent b w = w) ↔ _
      simp only [Subgroup.mem_top, true_and]
      rw [hP]
      constructor
      · intro hb
        exact hb _ (Submodule.mem_span_singleton_self _)
      · intro hb w hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [map_smul, hb]
    rw [hiff]
    constructor
    · rintro ⟨a, ha', rfl⟩
      exact (ha a v).symm.trans (congrArg e ha')
    · intro hb
      obtain ⟨a, rfl⟩ := f.surjective b
      exact ⟨a, e.injective ((ha a v).trans hb), rfl⟩
  obtain ⟨hRC, hRN⟩ := source_actor_normal_in_point_stabilizer_at d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hyp.point_ne_zero hline
  have hle : c.actorImage (F.X g) ≤ c.pointCentralizer (F.Vi 2) := by
    rw [← hm, ← hpc]
    exact map_mono hRC
  refine ⟨hle, (normal_subgroupOf_iff_le_normalizer hle).mpr ?_⟩
  rw [← hpc, ← hm]
  exact (map_mono ((normal_subgroupOf_iff_le_normalizer hRC).mp hRN)).trans
    (le_normalizer_map f.toMonoidHom)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Tensor/Order.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative TensorProduct

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem source_tensor_closure_card_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    Nat.card F.U = 512 := by
  let := chosen.elementary
  let h := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  let : IsElementaryAbelian 2 F.Uhat :=
    F.uhat_elementary_of_point (by decide) h.two h.frattini_point
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 := by
    rw [(TensorGeometry.linearCoordinates c).finrank_eq,
      Module.finrank_tensorProduct, BinaryPermutation.finrank_core,
      Fintype.card_fin, c.constituent_model.finrank_four]
  have hcenter :=
    (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1.center_order_p
  have hquot := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
  rw [Nat.card_zmod, hd] at hquot
  rw [card_eq_card_quotient_mul_card_subgroup (center F.U), hcenter]
  change Nat.card (Additive F.Uhat) * 2 = 512
  norm_num only [hquot]

theorem source_tensor_sylow_card_lower_bound_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    512 ≤ Nat.card T := by
  rw [← source_tensor_closure_card_at d earlier hq chosen structural alternatives F hne hZ c]
  exact Nat.card_le_card_of_injective _
    (inclusion_injective (source_closure_le_sylow_at d earlier hq chosen structural alternatives F))

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Tensor/DeletedSize.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem source_tensor_deleted_mixed_hypotheses_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    ChapterF.Source.HypothesisF11 ![component F.H, F.I₂ L] (T : Subgroup G) ∧
      IsQuasithin (ChapterF.Source.generated ![component F.H, F.I₂ L] (T : Subgroup G)) ∧
      Chapter1.IsSylowIn 2 (T : Subgroup G)
        (ChapterF.Source.generated ![component F.H, F.I₂ L] (T : Subgroup G)) ∧
      Nonempty (coreQuotient (component F.H) ≃* AltFive) ∧
      Nonempty (coreQuotient (F.I₂ L) ≃* Three) ∧
      ChapterF.Source.borel (F.I₂ L) (T : Subgroup G) ≤ normalizer (T : Set G) := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  obtain ⟨e, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare
      (source_seed_geometry_at d earlier hq chosen F).2.1 hne g hgP hgH
  have hF := source_tensor_deleted_amalgam_at d earlier hq chosen structural alternatives
    classification F hne hZ g hg hgP hgH c hdel
  have hT : (T : Subgroup G) ≤
      ChapterF.Source.generated ![component F.H, F.I₂ L] (T : Subgroup G) := le_sup_right
  exact ⟨hF, d.qtke.quasithin.subgroup _,
    ⟨T.subtype hT, map_subgroupOf_eq_of_le hT⟩,
    ⟨TensorDeleted.componentQuotient (starComponentEquiv hAD c.actor)⟩,
    ⟨e⟩, hF.cubic_borel_normalizes_S 1 e⟩

theorem source_tensor_deleted_contradiction_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) : False := by
  obtain ⟨hF, hqt, hT, hK, hI, hB⟩ := source_tensor_deleted_mixed_hypotheses_at
    d earlier hq chosen structural alternatives classification F hne hZ g hg hgP hgH c hdel
  have hl := source_tensor_sylow_card_lower_bound_at d earlier hq chosen structural alternatives
    F hne hZ c
  have hu := size (component F.H) (F.I₂ L) (T : Subgroup G) hF hqt hT hK hI hB
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Tensor/CommonSource.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative TensorProduct

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem source_tensor_conjugate_geometry_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.X g ≤ (T : Subgroup G) ∧ ⁅F.W, F.X g⁆ ≤ F.E g ∧ F.W.relIndex F.U = 2 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨ι,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm ι hcore hindex
  have hXT := F.X_le_T_of_parabolic_core L g hIG
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN) hsplit
  have hqn := F.binary_source_E_normal_in_core L chosen.normalizes g hgP hgen.symm hcomm
  let := hqn
  have hqe := F.binary_source_quotient_elementary L chosen.normalizes g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  have hpair : ∃ hn : ((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal, letI := hn
      IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸ (F.E g).subgroupOf (F.W ⊔ F.X g)) := by
    have hh : ∃ hn : ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)).Normal, letI := hn
        IsElementaryAbelian 2 (((F.I₂ L).pCoreIn 2 : Subgroup G) ⧸
          (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) := ⟨hqn,hqe⟩
    rwa [hsplit] at hh
  obtain ⟨hn,helem⟩ := hpair
  let := hn
  let := helem
  exact ⟨hXT, F.commutator_W_X_le_E g, hindex⟩

theorem source_tensor_common_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    XFamily F.H (T : Subgroup G) = {first F.H, second F.H (T : Subgroup G)} ∧
      first F.H ≠ second F.H (T : Subgroup G) ∧
      first F.H ∈ YFamily F.H T (F.Vi 2) (F.E g) ∧
      Nonempty (c.SelectedConstituent T (F.Vi 2) g) := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1
  obtain ⟨hex, _⟩ := source_extraspecial_data_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH
  have hT : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hSylow : ((T.subtype hT : Sylow 2 F.H) : Subgroup F.H).map F.H.subtype = T :=
    map_subgroupOf_eq_of_le hT
  obtain ⟨S, hS⟩ := exists_star_sylow (T.subtype hT) hSylow
  let S' : Sylow 2 (Three × D) := S.mapSurjective (f := c.actor.toMonoidHom) c.actor.surjective
  have hS' : (S' : Subgroup (Three × D)) = c.actorImage (T : Subgroup G) := by
    change (S : Subgroup (coreQuotient F.H)).map c.actor.toMonoidHom = _
    rw [hS]
  have hpT : IsPGroup 2 (c.actorImage (T : Subgroup G)) := hS' ▸ S'.isPGroup'
  obtain ⟨he, hc⟩ := source_tensor_actor_card_at d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH c
  let := he
  have he' : IsElementaryAbelian 2 (c.actorImage (F.X g)) :=
    IsElementaryAbelian.map c.actor.toMonoidHom
  let := he'
  let : IsElementaryAbelian 2 (c.actorImage (conjugateLayer F.U (F.Vi 2) g)) := he'
  have hc' : Nat.card (c.actorImage (F.X g)) = 8 := by
    change Nat.card ((star F.H (F.X g)).map c.actor.toMonoidHom) = _
    rw [card_map_of_injective c.actor.injective, hc]
  have hr := source_tensor_point_rank_at d earlier hq chosen F hne c
  have hfix := c.point_fixed_of_normalizes hT (F.invariant 2) hr
  obtain ⟨s⟩ := TensorGeometry.selectedConstituent c hpT hex.Wg_le_T hc' hfix
  have hn := (source_tensor_actor_normal_at d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH c).2
  have hZP : center F.U ≤ (F.Vi 2).subgroupOf F.U := by
    intro z hz
    exact F.monotone (by omega : 1 ≤ 2) (hZ ▸ (show (z:G) ∈ F.ZU from ⟨z,hz,rfl⟩))
  have hPE : F.Vi 2 ≤ F.E g :=
    (F.le_seed 2).trans (F.seed_le_E_of_normalizes g (chosen.normalizes hg))
  have hbound : ⁅F.X g, F.W⁆ ≤ F.E g := by
    rw [commutator_comm]
    exact (source_tensor_conjugate_geometry_at d earlier hq chosen structural alternatives
      F hne g hgP hgH).2.1
  have hfirst := TensorGeometry.first_mem_Y c S' hS' s hT hex.U_le_T
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) hZP hr
    hex.Wg_le_T hPE he' hc' hn hbound
  obtain ⟨hpair, hneq⟩ := family_eq_pair_of_model (T.subtype hT) hSylow c.actor_models
  exact ⟨hpair, hneq, hfirst, ⟨s⟩⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Tensor/NaturalSource.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative TensorProduct

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]


theorem source_tensor_natural_second_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hnatural : IsNaturalFour hAD c.constituent) :
    second F.H (T : Subgroup G) ∈ YFamily F.H T (F.Vi 2) (F.E g) := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1
  let h := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  let : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point (by decide) h.two h.frattini_point
  obtain ⟨hpair, _, hfirst, ⟨s⟩⟩ :=
    source_tensor_common_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH c
  obtain ⟨e, f, hf⟩ := hnatural
  let n := TensorGeometry.naturalConstituent c s e f hf
  let A := TensorGeometry.preimage c s.firstSpace
  have hSylow : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map F.H.subtype = T :=
    map_subgroupOf_eq_of_le (F.invariant 1)
  have hPU : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  have hpoint : Nat.card (Natural.tilde F.U (F.Vi 2)) = 2 :=
    card_plane_hat F (by decide) ((source_seed_geometry_at d earlier hq chosen F).2.2 hne)
  have hPA : Natural.tilde F.U (F.Vi 2) ≤ Natural.tilde F.U A := by
    apply c.image_le_iff.mp
    rw [show A = TensorGeometry.preimage c s.firstSpace from rfl, TensorGeometry.image_preimage]
    exact s.point_le_fixed.trans s.fixed_le_first
  obtain ⟨hXT, hbound, hindex⟩ := source_tensor_conjugate_geometry_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hgG := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  have hfix : ∀ a : F.H, (a : G) ∈ (T : Subgroup G) ∨ (a : G) ∈ F.X g →
      ∀ q ∈ Natural.tilde F.U (F.Vi 2),
        Natural.Geometry.representation c.H_normalizes_U a (Additive.ofMul q) = Additive.ofMul q := by
    intro a ha q hqp
    have hnorm : (a : G) ∈ normalizer (F.Vi 2 : Set G) := by
      rcases ha with ha | ha
      · exact F.invariant 2 ha
      · exact (Subgroup.centralizer_le_normalizer _ (F.X_le_plane_centralizer g hgG ha))
    apply (TensorGeometry.linearCoordinates c).injective
    rw [TensorGeometry.natural_coordinates_equivariant]
    have hv : TensorGeometry.linearCoordinates c (Additive.ofMul q) ∈ c.image (F.Vi 2) := by
      rw [TensorGeometry.image_eq_map]
      exact ⟨Additive.ofMul q, hqp, rfl⟩
    have ha' : c.actor (QuotientGroup.mk' (pCore 2 F.H) a) ∈
        c.actorImage (F.H ⊓ F.Gi 2) := ⟨_, ⟨a, ⟨a.property, hnorm⟩, rfl⟩, rfl⟩
    exact c.point_fixed_of_normalizes (show F.H ⊓ F.Gi 2 ≤ F.H from inf_le_left)
      inf_le_right (source_tensor_point_rank_at d earlier hq chosen F hne c) hv ⟨_, ha'⟩
  obtain ⟨coords⟩ := Natural.Geometry.exists_coordinates_of_model c.H_normalizes_U n
    (Natural.geometry_placements_of_sylow (T.subtype (F.invariant 1)) hSylow n.componentEquiv c.actor_models)
    c.actor_models hpoint hPA hfix
    (source_tensor_actor_card_at d earlier hq chosen structural alternatives F hne hZ g hgP hgH c).2
  have hZP : center F.U ≤ (F.Vi 2).subgroupOf F.U := by
    intro z hz
    exact F.monotone (by omega : 1 ≤ 2) (hZ ▸ (show (z:G) ∈ F.ZU from ⟨z,hz,rfl⟩))
  have hPE : F.Vi 2 ≤ F.E g :=
    (F.le_seed 2).trans (F.seed_le_E_of_normalizes g (chosen.normalizes hg))
  have hsecond : second F.H (T : Subgroup G) ∈ XFamily F.H (T : Subgroup G) := by
    rw [hpair]; simp
  exact coords.second_mem_Y hsecond
    (source_closure_le_sylow_at d earlier hq chosen structural alternatives F) hPU hZP
    (hZP.trans (subgroupOf_mono F.U hPE)) (TensorGeometry.preimage_le c _)
    (hXT.trans (F.invariant 1))
    (TensorGeometry.preimage_le_hyperplane c s hindex hbound)
    (by rwa [commutator_comm])

theorem source_tensor_natural_partner_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hnatural : IsNaturalFour hAD c.constituent) : Partner T L V F g := by
  have hsecond := source_tensor_natural_second_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH c hnatural
  obtain ⟨hpair, hneq, hfirst, _⟩ :=
    source_tensor_common_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH c
  let a := source_local_data_at d earlier hq chosen structural alternatives classification
    F hne hZ g hg hgP hgH
  obtain ⟨e⟩ := TensorGeometry.symmetric_actor_of_action (F.invariant 1) c.actor_models
    hsecond (a.action _ hsecond)
  let q := Placements.overlapQuotient (T.subtype (F.invariant 1))
    (map_subgroupOf_eq_of_le (F.invariant 1)) e
  have hquot (A : Subgroup G) (hA : A = overlap F.H T) :
      Nonempty (coreQuotient A ≃* Three × Three) := by
    subst A
    exact ⟨q⟩
  have hL := (source_first_actor_at d earlier hq chosen structural F g hg).1
  have hLX : F.Li L 1 ∈ XFamily F.H T := hL.1
  rw [hpair] at hLX
  rcases Set.mem_insert_iff.mp hLX with heq | heq
  · refine ⟨second F.H T, hsecond, ?_, ?_⟩
    · rw [heq]
      exact hneq.symm
    · apply hquot
      rw [heq]
      rfl
  · have heq := Set.mem_singleton_iff.mp heq
    refine ⟨first F.H, hfirst, ?_, ?_⟩
    · rw [heq]
      exact hneq
    · apply hquot
      rw [heq, sup_comm (second F.H (T : Subgroup G)) (first F.H)]
      rfl

theorem source_tensor_natural_contradiction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hnatural : IsNaturalFour hAD c.constituent) : False :=
  contradiction_of_partner_at d earlier hq chosen structural alternatives classification
    F hne hZ hlarge g hg hgP hgH
    (source_tensor_natural_partner_at d earlier hq chosen structural alternatives classification
      F hne hZ g hg hgP hgH c hnatural)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/Tensor/Source.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem source_tensor_contradiction_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) : False := by
  rcases c.constituent_model with hnat | hdel
  · have hc := source_tensor_closure_card_at d earlier hq chosen structural alternatives F hne hZ c
    exact source_tensor_natural_contradiction_at d earlier hq chosen structural alternatives
      classification F hne hZ (by omega) g hg hgP hgH c hnat
  · exact source_tensor_deleted_contradiction_of_mixed_size_at d earlier hq chosen structural
      alternatives classification size F hne hZ g hg hgP hgH c hdel

theorem source_tensor_exclusion_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) : False := by
  obtain ⟨g, hg, hgP, hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  exact source_tensor_contradiction_of_mixed_size_at d earlier hq chosen structural alternatives
    classification size F hne hZ g hg hgP hgH c

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end
