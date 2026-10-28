module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.PointStabilizer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Recognition
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven.Assembly
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry

/-!
# The original S₇ branch

An actual marked S₇ conjugate-pair action on U/Z(U) supplies the remaining
input to 14.4.11. The original parabolic equations supply its earlier local
geometry. The dimension bound and the elementary rank of S₇ force the actor
to have order eight, and the literal point-stabilizer equality supplies
relative normality. Thus this marked model constructs a distinct Y-member
and the middle quotient, and gives the large-branch contradiction.

The exhaustive production of the marked S₇ action, or one of the other
14.4.2 model alternatives, remains with this source task.
Source: Aschbacher--Smith, 14.4.2(4), 14.4.11, pp.1006,1011.
-/

public noncomputable section
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

/-- Construct the source second actor in the actual S₇ conjugate-pair row.
Only the marked model itself remains explicit; all earlier geometry is proved. -/
theorem source_partner_of_symmetric_seven (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨ι,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
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
    source_terminal_marked_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := hx
  let f : F.TerminalHdot ≃* Equiv.Perm (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).trans e
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
  have hpn := source_actor_normal_in_point_stabilizer d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH v hyp.point_ne_zero hline
  have hact (a : F.TerminalHdot) (w : Additive F.Uhat) :
      D.representation (f a) w = F.terminalRepresentation a w := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact he b w
  let geom : EarlierGeometry ca (T:Subgroup G) (F.Vi 2) F.W (F.X g) := {
    U_le_T := source_closure_le_sylow d earlier hq chosen structural alternatives F
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
    (source_first_actor d earlier hq chosen structural F g hg).1

/-- The literal classification consumer for the marked S₇ row. -/
theorem source_symmetric_seven_contradiction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T:Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* Equiv.Perm (Fin 7)) (D : Pair (Additive F.Uhat))
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      D.representation (starProjection e a) w =
        F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w) : False :=
  contradiction_of_partner d earlier hq chosen structural alternatives classification F hne hZ hlarge
    g hg hgP hgH (source_partner_of_symmetric_seven d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH e D he)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
