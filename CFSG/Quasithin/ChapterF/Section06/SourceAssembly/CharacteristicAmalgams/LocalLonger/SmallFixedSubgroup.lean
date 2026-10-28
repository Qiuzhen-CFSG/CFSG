module
public import Stellmacher.SectionNine.NineThreeOrbitQuadraticFixedSubgroup
public import Stellmacher.SectionNine.NineThreeGeometricExtraction
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer
public import Stellmacher.SectionNine.NineThreeInitialExtractionInputs
public import Stellmacher.SectionFiveToSeven.Result7_8.PrescribedActorConfiguration
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalContext
/-!
# Local fixed subgroups in the longer commuting critical-path argument

The two-subgroup W selected in Stellmacher (9.3) already lies in the initial
vertex and centralizes its center. The local orbit centralizer theorem from
(7.4) therefore places W in that vertex's two-core. The full ambient
centralizer of the neighbor module is unnecessary. This proves the geometric
fixed-subgroup extraction with only the Section Seven local hypotheses,
and constructs the actual first extraction from a Goldschmidt triple.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.3), p.49, first
application of (1.2) before relation (2), using (7.4), (7.5), and (7.8).
-/

namespace Stellmacher.SectionNine.LocalLonger
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem geometric_small_fixed_subgroup
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (u0 d l : ctx.Γ.Vertex)
    (hu : IsConjugateVertex ctx.Γ ctx.criticalPath.a u0)
    (V E A0 : Subgroup G) (actor : G)
    (haZu : actor ∈ ZAt ctx.Γ u0)
    (hZuV : ZAt ctx.Γ u0 ≤ V)
    (data : NineThreeGeometricData ctx.Γ d l V E A0 actor)
    (hquad : ⁅⁅ZAt ctx.Γ u0,
      ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ GAt ctx.Γ u0⁆,
      ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ GAt ctx.Γ u0⁆ = ⊥) :
    let m := ctx.Γ.act data.x⁻¹ l
    ∃ W : Subgroup G, W ≤ ZAt ctx.Γ m ∧ W ≤ QAt ctx.Γ u0 ∧
      W ≤ ZAt ctx.Γ l ∧
      Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ u0 : Subgroup G) ≤ 2 * Nat.card W ∧
      E ≤ Subgroup.centralizer (W : Set G) ∧
      ¬ ZAt ctx.Γ u0 ⊓ Subgroup.centralizer (W : Set G) ≤ GAt ctx.Γ m := by
  let Γ := ctx.Γ
  let m := Γ.act data.x⁻¹ l
  let Y := ZAt Γ m ⊓ GAt Γ u0
  have hback : d ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hZmp : IsPGroup 2 (ZAt Γ m) := by
    let _ := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hback
    exact IsElementaryAbelian.isPGroup 2 (ZAt Γ m)
  have hYp : IsPGroup 2 Y := hZmp.to_le inf_le_left
  have hZaNot : ¬ ZAt Γ u0 ≤ GAt Γ m := fun hle => data.actor_outside (hle haZu)
  obtain ⟨W,hWY,hWcard,hWnot⟩ := nine_three_quadratic_fixed_subgroup_at_vertex ctx
    u0 hu Y inf_le_right hYp hquad (GAt Γ m) hZaNot
  obtain ⟨a,ha,haNot⟩ := Set.not_subset.mp hWnot
  have hWm : W ≤ ZAt Γ m := hWY.trans inf_le_left
  have hZmQm : ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core m d hback).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hAxC : (V).conjBy data.x ≤ Subgroup.centralizer (W : Set G) :=
    data.conjugate_core_le.trans (Subgroup.le_centralizer_iff.mp (hWm.trans hZmQm))
  have hEC : E ≤ Subgroup.centralizer (W : Set G) := by
    rw [data.actor_generated a (hZuV ha.1) haNot]
    exact sup_le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr ha.2)) hAxC
  have hxE : data.x ∈ E := (Subgroup.map_subtype_le _) data.residual_mem
  have hWl : W ≤ ZAt Γ l := by
    intro z hz
    have hzmap : z ∈ (ZAt Γ l).map (MulAut.conj data.x).toMonoidHom := by
      have hzm := hWm hz
      change z ∈ CosetGraphContext.z Γ (Γ.act data.x⁻¹ l) at hzm
      rw [z_act,inv_inv] at hzm
      exact hzm
    have hzback := (Subgroup.mem_map_equiv).mp hzmap
    change data.x⁻¹ * z * data.x ∈ ZAt Γ l at hzback
    have hcomm : z * data.x = data.x * z :=
      Subgroup.mem_centralizer_iff.mp (hEC hxE) z hz
    have he : data.x⁻¹ * z * data.x = z := by
      rw [mul_assoc,hcomm,inv_mul_cancel_left]
    exact he ▸ hzback
  have hVfirstE : V ≤ E := by rw [data.generated]; exact le_sup_left
  have hWC : W ≤ Subgroup.centralizer (V : Set G) :=
    (Subgroup.le_centralizer_iff.mp hEC).trans (Subgroup.centralizer_le hVfirstE)
  have hWQu : W ≤ QAt Γ u0 := nine_three_orbit_pgroup_centralizer ctx u0 hu
    W (hYp.to_le hWY) (hWY.trans inf_le_right)
    (hWC.trans (Subgroup.centralizer_le hZuV))
  exact ⟨W,hWm,hWQu,hWl,hWcard,hEC,hWnot⟩



/-- The actual first geometric extraction, retaining its small fixed subgroup. -/
public structure InitialExtractionData
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) where
  l : ctx.Γ.Vertex
  penultimate : l = ctx.criticalPath.path ⟨ctx.criticalPath.length-1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  actor : G
  actor_initial : actor ∈ ZAt ctx.Γ ctx.criticalPath.a
  E : Subgroup G
  A0 : Subgroup G
  extraction : NineThreeGeometricData ctx.Γ ctx.criticalPath.a' l
    (VAt ctx.Γ ctx.criticalPath.firstStep) E A0 actor
  W : Subgroup G
  W_new_center : W ≤ ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l)
  W_initial_core : W ≤ QAt ctx.Γ ctx.criticalPath.a
  W_old_center : W ≤ ZAt ctx.Γ l
  W_index : Nat.card
      (ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ⊓ GAt ctx.Γ ctx.criticalPath.a : Subgroup G) ≤
    2 * Nat.card W
  E_centralizes : E ≤ Subgroup.centralizer (W : Set G)
  fixed_escapes : ¬ ZAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (W : Set G) ≤
    GAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l)

/-- The first extraction and its fixed subgroup need only local Section Seven. -/
public theorem exists_initial_extraction
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (hb : 1 < ctx.criticalPath.length) :
    Nonempty (InitialExtractionData ctx) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let l := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let V := VAt Γ cp.firstStep
  obtain ⟨hl,hV,hElem,hPhi,hquad1,hquad2,actor,haZ,haV,haNot⟩ :=
    nine_three_initial_extraction_inputs ctx hb
  have hPhiLe : frattiniAmbient V ≤ QAt Γ cp.a' := by
    have hh : frattiniAmbient V = ⊥ := hPhi
    rw [hh]
    exact bot_le
  have hVnot : ¬ V ≤ QAt Γ cp.a' := fun hle => haNot (hle haV)
  obtain ⟨y,A0,E,hEP,hyP,h0A,hgen,hcard,hyE,hySq,h0core,hedge,hmodel,horbit,hby,hres,ha0⟩ :=
    sevenEight_quotient_configuration_with_actor ctx.sectionSeven Γ cp.a' l hl V hV hVnot
      hPhiLe actor haV haNot
  obtain ⟨data⟩ := nine_three_geometric_extraction ctx.sectionSeven Γ cp.a' l hl
    V E A0 hV hPhiLe actor haV ha0 y hyE hEP hgen h0A hcard h0core hedge hmodel hby
  have hZaV : ZAt Γ cp.a ≤ V :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hZmVend : ZAt Γ (Γ.act data.x⁻¹ l) ≤ VAt Γ cp.a' := by
    change z Γ (Γ.act data.x⁻¹ l) ≤ v Γ cp.a'
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨_,data.neighbor,rfl⟩
  have hquad : ⁅⁅ZAt Γ cp.a,ZAt Γ (Γ.act data.x⁻¹ l) ⊓ GAt Γ cp.a⁆,
      ZAt Γ (Γ.act data.x⁻¹ l) ⊓ GAt Γ cp.a⁆ = ⊥ := by
    have hq := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb
    exact bot_unique ((Subgroup.commutator_mono
      (Subgroup.commutator_mono hZaV (inf_le_left.trans hZmVend))
        (inf_le_left.trans hZmVend)).trans_eq hq.2.2)
  obtain ⟨W,hWm,hWa,hWl,hWcard,hEC,hCW⟩ := geometric_small_fixed_subgroup ctx
    cp.a cp.a' l ⟨1,Γ.act_one cp.a⟩ V E A0 actor haZ hZaV data hquad
  exact ⟨{
    l := l
    penultimate := rfl
    actor := actor
    actor_initial := haZ
    E := E
    A0 := A0
    extraction := data
    W := W
    W_new_center := hWm
    W_initial_core := hWa
    W_old_center := hWl
    W_index := hWcard
    E_centralizes := hEC
    fixed_escapes := hCW }⟩

end Stellmacher.SectionNine.LocalLonger

namespace CFSG.Quasithin.ChapterF
open Theory.GroupTheory Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- First longer-path extraction for the literal Goldschmidt graph. -/
public theorem IsGoldschmidtTriple.exists_initial_extraction_of_commuting
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅Γ.z cp.a, Γ.z cp.a'⁆ = ⊥) (hb : 1 < cp.length) :
    Nonempty (Stellmacher.SectionNine.LocalLonger.InitialExtractionData
      (⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩ :
        SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂)) :=
  Stellmacher.SectionNine.LocalLonger.exists_initial_extraction _ hb

end CFSG.Quasithin.ChapterF
