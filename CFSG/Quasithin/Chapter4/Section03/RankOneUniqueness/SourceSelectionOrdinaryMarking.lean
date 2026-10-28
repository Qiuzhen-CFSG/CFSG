module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinarySporadic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Parabolics
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.MarkedParabolicPair
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# Simultaneous symplectic coordinates before full-normalizer identification

The actual ordinary catalogue selects a nonbinary symplectic central quotient.
The trivial multiplier lifts it to the original K. Full-Sylow placement and
internal conjugacy simultaneously mark the original L and T intersection.
The local two-core quotient recovers the original field degree; the fully
moved natural extension identifies the full source module with O₂(L).

Every marking is constructed from OutsideChoice, without H = N_G(K).
The original chosen V remains distinct from the full module. The next modules
use these coordinates in the literal root normalizer and source selection.
This extends OrdinaryRecognitionSymplectic/Field to the earlier boundary and
preserves their public interfaces.
Source: Aschbacher–Smith C.3.1, pp.149–151, I.1.3/6, and 4.3.6, p.614.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
private theorem naturalExtension_moved_eq {F X : Type*} [Field F] [Group X]
    {Q : Subgroup X} [Q.Normal] (d : NaturalExtension (F := F) Q)
    (N : Subgroup X) (hne : N ≠ ⊥) (hmove : ⁅N,⊤⁆ = N) (hle : N ≤ Q) : N = Q := by
  have hn : (⊤ : Subgroup X) ≤ normalizer (N : Set X) := by
    rw [←hmove]
    exact normalizer_commutator_ge_right _ _
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  have hnc : ¬ N ≤ center X := by
    intro hc
    exact hne (hmove.symm.trans (commutator_top_right_eq_bot_iff_le_center.mpr hc))
  have he : N ⊔ (Q ⊓ center X) = Q := by
    rcases d.invariant_interval (N ⊔ (Q ⊓ center X)) le_sup_right
      (sup_le hle inf_le_left) with hc | hc
    · exact (hnc (le_sup_left.trans (hc.le.trans inf_le_right))).elim
    · exact hc
  let q := QuotientGroup.mk' N
  have hqc : Q.map q ≤ center (X ⧸ N) := by
    rw [←he,Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq]
    rintro _ ⟨z,hz,rfl⟩
    apply mem_center_iff.mpr
    intro x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N x
    simpa only [map_mul] using congrArg q (mem_center_iff.mp hz.2 x)
  have hzero : Q.map q = ⊥ := by
    rw [←d.commutator_eq,map_commutator,map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
    exact commutator_top_right_eq_bot_iff_le_center.mpr hqc
  exact le_antisymm hle (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff Q).mp hzero)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- A literal plane-local marking determines the entire original full module. -/
theorem ordinary_fullModule_of_plane_marking (c : OutsideChoice T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (K : Subgroup c.H) (hLK : L ≤ K.map c.H.subtype)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : K ≃* Sp F) (hl : (c.ordinaryLocal K).map e.toMonoidHom = planeLocal) :
    c.ordinaryModule = L.pCoreIn 2 := by
  let eL : L ≃* planeLocal (F := F) := (c.ordinaryLocalEquiv hLK).symm.trans
    ((e.subgroupMap (c.ordinaryLocal K)).trans (MulEquiv.subgroupCongr hl))
  let A := c.ordinaryModule.subgroupOf L
  let N := A.map eL.toMonoidHom
  obtain ⟨hne,hmove,hcore⟩ := c.ordinaryModule_local_data D h
  have hNne : N ≠ ⊥ := fun hz => hne ((map_eq_bot_iff_of_injective A eL.injective).mp hz)
  have hNmove : ⁅N,(⊤ : Subgroup (planeLocal (F := F)))⁆ = N := by
    rw [show (⊤ : Subgroup (planeLocal (F := F))) = (⊤ : Subgroup L).map eL.toMonoidHom from
      (map_top_of_surjective _ eL.surjective).symm,←map_commutator,hmove]
  have hNcore : N ≤ Plane.radical := by
    rw [←planeLocal_core_eq hF hn,←pCore_map_iso 2 eL]
    exact map_mono (hcore.trans (map_subtype_le _))
  have hN := naturalExtension_moved_eq (planeNaturalExtension hF hn) N hNne hNmove hNcore
  have hA : A = pCore 2 L := by
    apply map_injective (f := eL.toMonoidHom) eL.injective
    rw [pCore_map_iso 2 eL,planeLocal_core_eq hF hn]
    exact hN
  have hWL : c.ordinaryModule ≤ L := by
    simpa only [c.ordinary_span_eq] using (c.c28 D h).module_le
  change c.ordinaryModule.subgroupOf L = pCore 2 L at hA
  rw [←map_subgroupOf_eq_of_le hWL,hA]
  rfl

private theorem graph_pointLocal {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    pointLocal.map (DiagramAutomorphisms.ExceptionalGraph.graphAut (F := F)).toMonoidHom =
      planeLocal := by
  let a := DiagramAutomorphisms.ExceptionalGraph.graphAut (F := F)
  let ep := pointParabolic.equivMapOfInjective a.toMonoidHom a.injective
  have hh := congrArg (map (pointParabolic.map a.toMonoidHom).subtype)
    (map_solvableResidual_eq ep.toMonoidHom ep.surjective)
  have hm : ((solvableResidual (pointParabolic (F := F))).map pointParabolic.subtype).map
      a.toMonoidHom = (solvableResidual (pointParabolic.map a.toMonoidHom)).map
      (pointParabolic.map a.toMonoidHom).subtype := by
    rw [map_map] at hh
    rw [map_map]
    convert hh using 1
    congr 1
  rw [pointParabolic_solvableResidual_eq hF hn,
    DiagramAutomorphisms.ExceptionalGraph.graphAut_map_point,
    planeParabolic_solvableResidual_eq hF hn] at hm
  exact hm

/-- The actual Sp₄ central-quotient row gives a whole-component equivalence
marking the original L as the plane local. -/
theorem ordinary_symplectic_plane_model (c : OutsideChoice T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {r : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ r))
    (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : (K ⧸ center K) ≃* Sp F) :
    ∃ b : K ≃* Sp F, (c.ordinaryLocal K).map b.toMonoidHom = planeLocal := by
  let := ho.2
  obtain ⟨b,hb⟩ := CentralCovers.Even.exists_whole_model hF hn e
  have he : b.toMonoidHom = e.toMonoidHom.comp (QuotientGroup.mk' (center K)) := by
    ext x : 1
    exact hb x
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  obtain ⟨P,_,hlocal,hproper⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center K)))
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.symplectic_local_placement
    hF hn S ((c.ordinaryLocal K).map f) hlocal hproper
  let b' := b.trans (MulAut.conj g)
  have hb' : b'.toMonoidHom = (MulAut.conj g).toMonoidHom.comp b.toMonoidHom := by ext; rfl
  have hm : (c.ordinaryLocal K).map b'.toMonoidHom = pointLocal ∨
      (c.ordinaryLocal K).map b'.toMonoidHom = planeLocal := by
    simpa only [hb',he,f,map_map] using hg
  rcases hm with hm | hm
  · refine ⟨b'.trans DiagramAutomorphisms.ExceptionalGraph.graphAut,?_⟩
    have hb'' : (b'.trans DiagramAutomorphisms.ExceptionalGraph.graphAut).toMonoidHom =
        DiagramAutomorphisms.ExceptionalGraph.graphAut.toMonoidHom.comp b'.toMonoidHom := by ext; rfl
    rw [hb'',←map_map,hm,graph_pointLocal hF hn]
  · exact ⟨b',hm⟩

/-- Internal Sylow conjugacy preserves the plane-local mark and aligns the
literal S ∩ K with the standard unipotent subgroup. -/
theorem ordinary_symplectic_simultaneous_model (c : OutsideChoice T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {r : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ r))
    (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : (K ⧸ center K) ≃* Sp F) :
    ∃ b : K ≃* Sp F, (c.ordinaryLocal K).map b.toMonoidHom = planeLocal ∧
      ((((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K).map b.toMonoidHom = unipotent := by
  obtain ⟨b,hb⟩ := c.ordinary_symplectic_plane_model D h hpsl K ho hLK hout hKN hF hn e
  obtain ⟨P,hP,_,_⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  let S := P.mapSurjective (f := b.toMonoidHom) b.surjective
  let U := unipotentSylow hF (by omega : 1 ≤ n)
  have hSP : (S : Subgroup (Sp F)) ≤ normalizer (planeLocal (F := F) : Set (Sp F)) := by
    change (P : Subgroup K).map b.toMonoidHom ≤ _
    rw [hP,←hb,←map_equiv_normalizer_eq]
    exact map_mono (c.ordinary_component_sylow_normalizes_local D K)
  have hUP : (U : Subgroup (Sp F)) ≤ normalizer (planeLocal (F := F) : Set (Sp F)) := by
    change unipotent ≤ normalizer (planeLocal (F := F) : Set (Sp F))
    exact inf_le_right.trans planeLocal.le_normalizer
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (normalizer (planeLocal (F := F) : Set (Sp F)))
    (S.subtype hSP) (U.subtype hUP)
  rw [Sylow.smul_subtype] at hg
  have hSU := congrArg Sylow.toSubgroup (Sylow.subtype_injective hg)
  change (S : Subgroup (Sp F)).map (MulAut.conj (g : Sp F)).toMonoidHom = unipotent at hSU
  let b' := b.trans (MulAut.conj (g : Sp F))
  have hb' : b'.toMonoidHom = (MulAut.conj (g : Sp F)).toMonoidHom.comp b.toMonoidHom := by ext; rfl
  refine ⟨b',?_,?_⟩
  · rw [hb',←map_map,hb]
    exact mem_normalizer_iff_map_conj_eq.mp g.property
  · rw [hb',←map_map,←hP]
    exact hSU


end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Simultaneous coordinates on the raw ordinary source choice, before the
full ambient normalizer has been identified. -/
structure OutsideSymplecticMarking (c : OutsideChoice T L) (K : Subgroup c.H) (n : ℕ) where
  Field : Type
  [field : _root_.Field Field]
  [finite : Finite Field]
  [charTwo : CharP Field 2]
  card : Nat.card Field = 2 ^ n
  componentEquiv : K ≃* Sp Field
  original_local : (c.ordinaryLocal K).map componentEquiv.toMonoidHom = planeLocal
  sylow : ((((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K).map
    componentEquiv.toMonoidHom = unipotent
  full_module : c.ordinaryModule = L.pCoreIn 2
  contains : L ≤ K.map c.H.subtype

attribute [instance] OutsideSymplecticMarking.field OutsideSymplecticMarking.finite
  OutsideSymplecticMarking.charTwo

/-- The original local quotient recovers the same field cardinality before
any ambient normalizer equality is available. -/
theorem OutsideChoice.ordinary_symplectic_field_card (c : OutsideChoice T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 1 < r)
    (e : (K ⧸ center K) ≃* Sp F) : Nat.card F = 2 ^ n := by
  obtain ⟨b,hb⟩ := c.ordinary_symplectic_plane_model D h hpsl K ho hLK hout hKN hF hr e
  let a : L ≃* planeLocal (F := F) := (c.ordinaryLocalEquiv hLK).symm.trans
    ((b.subgroupMap (c.ordinaryLocal K)).trans (MulEquiv.subgroupCongr hb))
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let q : (L ⧸ pCore 2 L) ≃* SL(2,F) := aq.trans (planeLocalCoreQuotientEquiv hF hr)
  obtain ⟨E,_,_,hE,⟨b⟩⟩ := hpsl
  let : CharP E 2 := EvenProjective.charTwo_of_card hE
  exact (Matrix.SL2.field_card_eq_of_equiv
    (q.symm.trans (b.trans (Theory.PSL2.sl2QuotientEquiv E).symm))).trans hE

/-- The original ordinary source choice supplies every simultaneous marking,
including its unchanged field, original L, full Sylow and full module.
There is no normalizer, model-selection or marking callback. -/
theorem OutsideChoice.ordinarySymplecticMarking (c : OutsideChoice T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal) :
    Nonempty (OutsideSymplecticMarking c K n) := by
  obtain ⟨r,hr,F,_,_,hF,⟨e⟩⟩ := c.ordinary_symplectic_quotient D h K ho hLK hout hKN hn hpsl
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let a : (K ⧸ center K) ≃* Sp F := e.trans (EvenProjective.equiv (F := F)).symm
  have hFn := c.ordinary_symplectic_field_card D h hpsl K ho hLK hout hKN hF hr a
  obtain ⟨b,hl,hs⟩ := c.ordinary_symplectic_simultaneous_model D h hpsl K ho hLK hout hKN hFn hn a
  exact ⟨{ Field := F
           contains := hLK
           card := hFn
           componentEquiv := b
           original_local := hl
           sylow := hs
           full_module := c.ordinary_fullModule_of_plane_marking D h K hLK hFn hn b hl }⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
