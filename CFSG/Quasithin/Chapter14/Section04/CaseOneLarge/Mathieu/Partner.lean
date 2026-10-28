module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.PointStabilizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.SourceAction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Hyperplane
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Geometry
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Contracts
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Actor
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Coordinates
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Recognition
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.SourceAssembly

/-!
# The actual Mathieu partner and large-branch contradiction

An equivariant isomorphism from the original quotient action to the native
Mathieu module suffices. Simultaneous conjugation marks its actual Sylow
subgroup. The original fixed line, hyperplane, normal conjugate actor and
order-32 calculation then construct every earlier-geometry premise of
14.4.12. Its second Y-member retains the original source conjugator and
literal overlap quotient, so the proved A₃ recognition gives the large-case
contradiction.

This completes the Mathieu row conditional only on its genuine group and
module identification. Exhaustiveness of the 14.4.2 rows is a separate
remaining source obligation, not an assumption hidden in this construction.
Source: Aschbacher--Smith 14.4.2(6), 14.4.12--14, printed pp.1006,1011--1012.
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
open LargerDimension.Mathieu.ModuleGeometry.Native hiding Group

universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem source_conjugate_local_geometry (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.X g ≤ (T : Subgroup G) ∧ ⁅F.W, F.X g⁆ ≤ F.E g := by
  let := chosen.elementary
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
  exact ⟨hXT, F.commutator_W_X_le_E g⟩

omit [Finite G] in
private theorem terminal_marked_transport
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hk : F.terminalHatAction.ker = pCore 2 F.H)
    (e : coreQuotient F.H ≃* D) (c : Additive F.Uhat ≃ₗ[ZMod 2] W)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      σ (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    ∃ f : F.TerminalHdot ≃* D,
      (∀ A : Subgroup G, (F.terminalDot A).map f.toMonoidHom =
        (A.subgroupOf F.H).map (ActorCatalogue.starProjection F.H e)) ∧
      ∀ (a : F.TerminalHdot) (w : Additive F.Uhat),
        σ (f a) (c w) = c (F.terminalRepresentation a w) := by
  let f : F.TerminalHdot ≃* D := (QuotientGroup.quotientMulEquivOfEq hk).trans e
  refine ⟨f,?_,?_⟩
  · intro A
    rw [terminalDot,map_map]
    rfl
  · intro a w
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact he b w

omit [Finite G] in
private theorem binary_line_unique_nonzero
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v w : W) (hv : v ≠ 0) (h : v ∈ Submodule.span (ZMod 2) {w}) : v = w := by
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp h
  have ha0 : a ≠ 0 := by intro hz; rw [hz,zero_smul] at ha; exact hv ha.symm
  have ha1 := ((show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) a).resolve_left ha0
  simpa only [ha1,one_smul] using ha.symm

omit [Finite G] in
private theorem point_of_fixed_space_marking
    {A D Y W : Type*} [Group A] [Group D]
    [AddCommGroup Y] [Module (ZMod 2) Y] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A Y) (σ : Representation (ZMod 2) D W)
    (f : A →* D) (c : Y ≃ₗ[ZMod 2] W)
    (he : ∀ a w, c (ρ a w) = σ (f a) (c w))
    (P : Subgroup A) (S : Subgroup D) (hPS : P.map f = S)
    (v : Y) (hv : v ≠ 0) (hfix : ∀ a ∈ P, ρ a v = v)
    (w : W) (hS : fixedSpace σ S = Submodule.span (ZMod 2) {w}) : c v = w := by
  have hnon : c v ≠ 0 := fun hh => hv (c.injective (hh.trans (map_zero c).symm))
  have hmem : c v ∈ (fixedSpace ρ P).map c.toLinearMap :=
    ⟨v,(fun a => hfix a.val a.property),rfl⟩
  have hh : (fixedSpace ρ P).map c.toLinearMap = Submodule.span (ZMod 2) {w} :=
    (fixedSpace_map_equivariant ρ σ f c he P).trans
      ((congrArg (fixedSpace σ) hPS).trans hS)
  exact binary_line_unique_nonzero (c v) w hnon (hh.le hmem)

private theorem source_point_with_normal_actor (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ v : Additive F.Uhat, v ≠ 0 ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      (∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v) ∧
      IsElementaryAbelian 2 (F.terminalDot (F.X g)) ∧
      F.terminalDot (F.X g) ≤ ChapterG.Section10.pointCentralizer F.terminalRepresentation v ∧
      ((F.terminalDot (F.X g)).subgroupOf
        (ChapterG.Section10.pointCentralizer F.terminalRepresentation v)).Normal := by
  obtain ⟨_,hx,B,v,hyp,hline,hfix⟩ :=
    source_terminal_marked_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  exact ⟨v,hyp.point_ne_zero,hline,hfix,hx,
    source_actor_normal_in_point_stabilizer d earlier hq chosen
      structural alternatives F hne hZ g hgP hgH v hyp.point_ne_zero hline⟩

omit [Finite G] in
private theorem normal_point_image
    {A D Y W : Type*} [Group A] [Group D]
    [AddCommGroup Y] [Module (ZMod 2) Y] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A Y) (σ : Representation (ZMod 2) D W)
    (f : A ≃* D) (c : Y ≃ₗ[ZMod 2] W)
    (he : ∀ a w, σ (f a) (c w) = c (ρ a w))
    (v : Y) (N : Subgroup A) [IsElementaryAbelian 2 N]
    (I : Subgroup D) (hI : N.map f.toMonoidHom = I)
    (hN : N ≤ ChapterG.Section10.pointCentralizer ρ v)
    (hn : (N.subgroupOf (ChapterG.Section10.pointCentralizer ρ v)).Normal) :
    ∃ R : Subgroup D, I = R ∧
      R ≤ ChapterG.Section10.pointCentralizer σ (c v) ∧
      ChapterG.Section10.pointCentralizer σ (c v) ≤ normalizer (R : Set D) ∧
      IsPGroup 2 R := by
  have hpc : (ChapterG.Section10.pointCentralizer ρ v).map f.toMonoidHom =
      ChapterG.Section10.pointCentralizer σ (c v) := by
    ext b
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (he a v).trans (congrArg c ha)
    · intro hb
      obtain ⟨a,rfl⟩ := f.surjective b
      exact ⟨a,c.injective ((he a v).symm.trans hb),rfl⟩
  refine ⟨N.map f.toMonoidHom,hI.symm,(map_mono hN).trans hpc.le,?_,?_⟩
  · exact hpc.ge.trans ((map_mono ((normal_subgroupOf_iff_le_normalizer hN).mp hn)).trans
      (le_normalizer_map f.toMonoidHom))
  · let : IsElementaryAbelian 2 (N.map f.toMonoidHom) := IsElementaryAbelian.map _
    exact IsElementaryAbelian.isPGroup 2 _

private theorem source_marked_point_geometry
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* D) (c : Additive F.Uhat ≃ₗ[ZMod 2] W)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      σ (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w))
    (S : Subgroup D) (w : W)
    (hS : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map
      (ActorCatalogue.starProjection F.H e) = S)
    (hfixed : fixedSpace σ S = Submodule.span (ZMod 2) {w}) :
    (hatSpace F (F.Vi 2)).map c.toLinearMap = Submodule.span (ZMod 2) {w} ∧
      ∃ R : Subgroup D,
        ((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection F.H e) = R ∧
        R ≤ ChapterG.Section10.pointCentralizer σ w ∧
        ChapterG.Section10.pointCentralizer σ w ≤ normalizer (R : Set D) ∧
        IsPGroup 2 R := by
  obtain ⟨v,hv,hline,hfix,hx,hRC,hRN⟩ :=
    source_point_with_normal_actor d earlier hq chosen structural alternatives F hne hZ g hgP hgH
  let := hx
  obtain ⟨f,hmap,hact⟩ := terminal_marked_transport σ F
    (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ) e c he
  have hcv : c v = w := point_of_fixed_space_marking F.terminalRepresentation σ
    f.toMonoidHom c (fun a w => (hact a w).symm)
    (F.terminalDot (T : Subgroup G)) S ((hmap (T : Subgroup G)).trans hS)
    v hv hfix w hfixed
  constructor
  · rw [← hline,Submodule.map_span,Set.image_singleton]
    change Submodule.span (ZMod 2) {c v} = _
    rw [hcv]
  · obtain ⟨R,hmapR,hR,hRN,hpR⟩ := normal_point_image F.terminalRepresentation
      σ f c hact v (F.terminalDot (F.X g))
      (((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection F.H e))
      (hmap (F.X g)) hRC hRN
    rw [hcv] at hR hRN
    exact ⟨R,hmapR,hR,hRN,hpR⟩

/-- Assemble the earlier geometry in selected coordinates. The public source
consumer below discharges both the Sylow marking and the actor-order input. -/
private theorem partner_of_marked_geometry (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w))
    (hS : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map
      (ActorCatalogue.starProjection F.H e) = markedSylow)
    (hcard : Nat.card (((F.X g).subgroupOf F.H).map (ActorCatalogue.starProjection F.H e)) = 32) : Partner T L V F g := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1
  obtain ⟨hXT,hWX⟩ := source_conjugate_local_geometry d earlier hq chosen
    structural alternatives F hne g hgP hgH
  let ca := mathieuCentralAction F e c he
  obtain ⟨hpoint,R,hmapR,hR₀,hRN₀,hpR⟩ := source_marked_point_geometry
    ActorCatalogue.Native.action d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH e c he markedSylow markedVector hS markedSylow_fixedSpace
  have hC : ChapterG.Section10.pointCentralizer ActorCatalogue.Native.action markedVector =
      pointCentralizer := RadicalAction.NativePositions.pointCentralizer_eq_reference.symm
  have hR : R ≤ pointCentralizer := hR₀.trans hC.le
  have hRN' : pointCentralizer ≤ normalizer (R : Set ActorCatalogue.Native.Model) :=
    hC.ge.trans hRN₀
  have hT : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map F.H.subtype = T :=
    map_subgroupOf_eq_of_le (F.invariant 1)
  let geom : EarlierGeometry F.H F.U (F.Vi 2) F.W (F.X g) (F.E g)
      (T.subtype (F.invariant 1)) e ca R := {
    core_le_sylow := (source_closure_le_sylow d earlier hq chosen structural alternatives F).trans hT.ge
    point_le_core := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
    center_le_point := by rw [center_point F hZ]; exact comap_mono (F.monotone (by omega : 1 ≤ 2))
    center_le_intersection := by
      rw [center_point F hZ]
      exact comap_mono ((F.le_seed 1).trans (F.seed_le_E_of_normalizes g (chosen.normalizes hg)))
    hyperplane_le_core := inf_le_left
    conjugate_le_local := hXT.trans (F.invariant 1)
    commutator_le_intersection := hWX
    sylow_marking := hS
    point_marking := hpoint
    hyperplane_marking := source_mathieu_hyperplane d earlier hq chosen structural alternatives
      F hne g hgP hgH e c he hS
    conjugate_image := hmapR
    conjugate_image_le := hR
    conjugate_image_normal := hRN'
    conjugate_image_two := hpR
    conjugate_image_card := (congrArg (fun P : Subgroup ActorCatalogue.Native.Model => Nat.card P) hmapR).symm.trans hcard }
  have hfirst := (source_first_actor d earlier hq chosen structural F g hg).1
  rw [← hT] at hfirst
  obtain ⟨X,hneX,hY,hqX⟩ := LargerDimension.Mathieu.exists_partner geom (F.Li L 1) hfirst
  rw [hT] at hY hqX
  refine ⟨X,?_,hneX,hqX⟩
  rw [hY]
  simp

/-- The original Mathieu row supplies the second source actor with no
additional geometric, form, Sylow or radical-identification premises. -/
theorem source_mathieu_partner (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    Partner T L V F g := by
  obtain ⟨e',c',he',hS⟩ := exists_mathieu_sylow_marking F e c he
  exact partner_of_marked_geometry d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH e' c' he' hS
    (source_mathieu_actor_card d earlier hq chosen structural alternatives F hne hZ
      g hgP hgH e' c' he')

/-- Actual 14.4.14 consumer of the completed marked Mathieu branch. -/
theorem source_mathieu_contradiction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    False := by
  exact contradiction_of_partner d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hg hgP hgH
    (source_mathieu_partner d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH e c he)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
