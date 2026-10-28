module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionExceptional
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Parabolics
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.MarkedParabolicPair

/-!
# Constructing the ordinary marking from the genuine symplectic quotient row

The trivial multiplier of Sp₄(2ⁿ), n > 1, lifts the specified quotient
isomorphism to K itself. Full-Sylow local placement identifies the original
L with a parabolic residual. The exceptional graph automorphism chooses
the plane orientation. Conjugacy inside its normalizer then aligns the
original S ∩ K with the standard unipotent group without changing L.

The full module W is nonzero, fully moved and contained in Z(O₂(L)).
The natural quotient of the plane radical is irreducible over the binary
field. Consequently W together with the central fixed space is the whole
radical; full commutator generation removes that central error. Thus
W = O₂(L), retaining the full source module rather than the chosen module.

The final theorem constructs every field of OrdinarySymplecticMarking
from an actual same-field Sp₄ quotient equivalence. Selection of that row
from the original rank-one hypotheses is still required and remains with
qt-d-1222-rankone-ordinary-symplectic-marking; no unconditional recognition
claim is made here. Source: Aschbacher--Smith C.3.1 and 4.3.6, printed
pp.149--151 and 614, with the multiplier calculation of I.1.3.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

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
namespace SourceConfiguration

/-- A literal plane-local marking determines the entire original full module. -/
theorem ordinary_fullModule_of_plane_marking (c : SourceConfiguration T L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : c.K ≃* Sp F) (hl : c.ordinaryLocal.map e.toMonoidHom = planeLocal) :
    c.ordinaryModule = L.pCoreIn 2 := by
  let eL : L ≃* planeLocal (F := F) := c.ordinaryLocalEquiv.symm.trans
    ((e.subgroupMap c.ordinaryLocal).trans (MulEquiv.subgroupCongr hl))
  let A := c.ordinaryModule.subgroupOf L
  let N := A.map eL.toMonoidHom
  obtain ⟨hne,hmove,hcore⟩ := c.ordinaryModule_local_data
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
    simpa only [c.ordinary_span_eq] using c.c28.module_le
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
theorem ordinary_symplectic_plane_model (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : (c.K ⧸ center c.K) ≃* Sp F) :
    ∃ b : c.K ≃* Sp F, c.ordinaryLocal.map b.toMonoidHom = planeLocal := by
  let := ho.2
  obtain ⟨b,hb⟩ := CentralCovers.Even.exists_whole_model hF hn e
  have he : b.toMonoidHom = e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)) := by
    ext x : 1
    exact hb x
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  obtain ⟨P,_,hlocal,hproper⟩ := c.ordinary_model_local_data D ho e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center c.K)))
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.symplectic_local_placement
    hF hn S (c.ordinaryLocal.map f) hlocal hproper
  let b' := b.trans (MulAut.conj g)
  have hb' : b'.toMonoidHom = (MulAut.conj g).toMonoidHom.comp b.toMonoidHom := by ext; rfl
  have hm : c.ordinaryLocal.map b'.toMonoidHom = pointLocal ∨
      c.ordinaryLocal.map b'.toMonoidHom = planeLocal := by
    simpa only [hb',he,f,map_map] using hg
  rcases hm with hm | hm
  · refine ⟨b'.trans DiagramAutomorphisms.ExceptionalGraph.graphAut,?_⟩
    have hb'' : (b'.trans DiagramAutomorphisms.ExceptionalGraph.graphAut).toMonoidHom =
        DiagramAutomorphisms.ExceptionalGraph.graphAut.toMonoidHom.comp b'.toMonoidHom := by ext; rfl
    rw [hb'',←map_map,hm,graph_pointLocal hF hn]
  · exact ⟨b',hm⟩

omit [Finite G] in
/-- The original component Sylow normalizes the original local subgroup. -/
theorem ordinary_component_sylow_normalizes_local (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) :
    c.ordinarySylowInH.subgroupOf c.K ≤ normalizer (c.ordinaryLocal : Set c.K) := by
  intro s hs l
  exact D.sylow_normalizes_component hs.1 ((l : c.H) : G)

/-- Internal Sylow conjugacy preserves the plane-local mark and aligns the
literal S ∩ K with the standard unipotent subgroup. -/
theorem ordinary_symplectic_simultaneous_model (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : (c.K ⧸ center c.K) ≃* Sp F) :
    ∃ b : c.K ≃* Sp F, c.ordinaryLocal.map b.toMonoidHom = planeLocal ∧
      (c.ordinarySylowInH.subgroupOf c.K).map b.toMonoidHom = unipotent := by
  obtain ⟨b,hb⟩ := c.ordinary_symplectic_plane_model D ho hF hn e
  obtain ⟨P,hP⟩ := c.ordinary_component_sylow
  let S := P.mapSurjective (f := b.toMonoidHom) b.surjective
  let U := unipotentSylow hF (by omega : 1 ≤ n)
  have hSP : (S : Subgroup (Sp F)) ≤ normalizer (planeLocal (F := F) : Set (Sp F)) := by
    change (P : Subgroup c.K).map b.toMonoidHom ≤ _
    rw [hP,←hb,←map_equiv_normalizer_eq]
    exact map_mono (c.ordinary_component_sylow_normalizes_local D)
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

/-- Once the genuine same-field Sp₄ quotient row is selected, there are no
remaining center, local, Sylow or full-module premises for the requested marking. -/
theorem ordinarySymplecticMarking_of_quotient_model (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : (c.K ⧸ center c.K) ≃* Sp F) : Nonempty (OrdinarySymplecticMarking c n) := by
  obtain ⟨b,hl,hS⟩ := c.ordinary_symplectic_simultaneous_model D ho hF hn e
  exact ⟨{ Field := F
           card := hF
           componentEquiv := b
           original_local := hl
           sylow := hS
           full_module := c.ordinary_fullModule_of_plane_marking hF hn b hl }⟩

end SourceConfiguration
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
