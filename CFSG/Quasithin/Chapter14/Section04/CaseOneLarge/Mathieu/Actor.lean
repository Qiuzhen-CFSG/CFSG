module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.PointStabilizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Transport

/-!
# The original Mathieu conjugate actor

The actual terminal action transports the original conjugate actor normally
into a native Sylow-fixed point stabilizer. Its elementary two-core has
order 32. G.10's dimension bound on the twelve-dimensional module forces
the actor to have at least that order, giving equality.

The order argument is carried out over an abstract target action to avoid
reducing the concrete matrix generators during quotient transport. The
public source theorem instantiates the genuine native point-core theorem.
Source: Aschbacher--Smith, G.10.1, 12.8.12(2), 14.4.2(6), 14.4.12,
pp.355,855,1006,1011--1012.
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
open LargerDimension LargerDimension.Mathieu LargerDimension.LocalAction.Components

universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


private theorem actor_card_of_point_core
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    (hdim : finrank (ZMod 2) W = 12)
    (hcore : ∀ (S : Sylow 2 D) (v : W), v ≠ 0 →
      (∀ a : S, σ a.val v = v) →
      Nat.card (pCore 2 (ChapterG.Section10.pointCentralizer σ v)) = 32) (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* D)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] W)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      σ (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    Nat.card (((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection F.H e)) = 32 := by
  obtain ⟨_,hx,B,v,hyp,hline,hfix⟩ :=
    source_terminal_marked_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := hx
  let f : F.TerminalHdot ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).trans e
  have hmap (A : Subgroup G) : (F.terminalDot A).map f.toMonoidHom =
      (A.subgroupOf F.H).map (ActorCatalogue.starProjection F.H e) := by
    rw [terminalDot,map_map]
    rfl
  have hact (a : F.TerminalHdot) (w : Additive F.Uhat) :
      σ (f a) (c w) = c (F.terminalRepresentation a w) := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact he b w
  let R : Subgroup D :=
    (F.terminalDot (F.X g)).map f.toMonoidHom
  let C : Subgroup D := ChapterG.Section10.pointCentralizer σ (c v)
  obtain ⟨hRC,hRN⟩ := source_actor_normal_in_point_stabilizer d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hyp.point_ne_zero hline
  have hpc : (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).map
      f.toMonoidHom = C := by
    ext b
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (hact a v).trans (congrArg c ha)
    · intro hb
      obtain ⟨a,rfl⟩ := f.surjective b
      exact ⟨a,c.injective ((hact a v).symm.trans hb),rfl⟩
  have hRC' : R ≤ C := (map_mono hRC).trans hpc.le
  have hCN : C ≤ normalizer (R : Set D) :=
    hpc.ge.trans ((map_mono ((normal_subgroupOf_iff_le_normalizer hRC).mp hRN)).trans
      (le_normalizer_map f.toMonoidHom))
  have hpR : IsPGroup 2 R := by
    let : IsElementaryAbelian 2 R := IsElementaryAbelian.map f.toMonoidHom
    exact IsElementaryAbelian.isPGroup 2 R
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  let S : Sylow 2 D :=
    P.mapSurjective (f:=f.toMonoidHom) f.surjective
  have hv : c v ≠ 0 := fun hh =>
    hyp.point_ne_zero (c.injective (hh.trans (map_zero c).symm))
  have hS : ∀ a : S, σ a.val (c v) = c v := by
    have hvP : c v ∈ (fixedSpace F.terminalRepresentation P).map c.toLinearMap :=
      ⟨v,(fun a => hfix a.val a.property),rfl⟩
    exact (fixedSpace_map_equivariant F.terminalRepresentation σ
      f.toMonoidHom c (fun a w => (hact a w).symm) P).le hvP
  have hc : Nat.card (pCore 2 C) = 32 :=
    hcore S (c v) hv hS
  have hu : Nat.card R ≤ 32 := by
    have hh := card_le_of_le (le_pCoreIn_of_normalizes hpR hRC' hCN)
    rw [pCoreIn,card_map_of_injective C.subtype_injective,hc] at hh
    exact hh
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 12 :=
    c.finrank_eq.trans hdim
  have hr := (Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (QuotientGroup.mk'_surjective _)).trans
    (IsElementaryAbelian.rank_le_finrank (p:=2) (F.terminalDot (F.X g)))
  have hb := hyp.dimension_bound.1
  rw [hd] at hb
  have hl : 5 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by omega
  have hpow : Nat.card R = 2 ^ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
    change Nat.card ((F.terminalDot (F.X g)).map f.toMonoidHom) = _
    rw [card_map_of_injective f.injective,Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive (F.terminalDot (F.X g)))
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hl
  exact (congrArg (fun P : Subgroup D => Nat.card P) (hmap _)).symm.trans
    (le_antisymm hu (by simpa only [← hpow] using hp))

/-- The original Mathieu actor has order 32, from the dimension bound and point radical. -/
theorem source_mathieu_actor_card (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    Nat.card (((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection F.H e)) = 32 := by
  exact actor_card_of_point_core ActorCatalogue.Native.action
    Sporadic.Mathieu.M22TripleCover.binarySpace_finrank
    ActorCatalogue.Native.pointCentralizer_core_card d earlier hq chosen structural
    alternatives F hne hZ g hgP hgH e c he

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
