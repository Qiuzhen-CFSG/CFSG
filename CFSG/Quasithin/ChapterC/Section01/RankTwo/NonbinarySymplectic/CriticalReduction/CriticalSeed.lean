module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CriticalActors
public import Theory.Representation.SymplecticFourOrthogonalCover.QuadraticSeed

/-!
# Fixed Sylow seeds inside the replacement's critical radius

Critical images are inner at every nonbinary degree, since their order is
at least q whereas an outer quadratic image has order at most n < q.
A critical image preserving a full Sylow seed fixes it pointwise. Exact
vertex centralizers and critical reversal then place the seed inside the
core of every vertex in the source radius with a common normalizing edge.

Source: MS93 (3.4), first radius argument, p.868.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open Representation.SymplecticFourOrthogonalCover
section Abstract
variable {M J V F : Type*} [Group M] [Finite M] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {T : Subgroup M} {geometry : Geometry T} {a z : Vertex T}
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]

omit [B.Normal] in
private theorem critical_seed_central_of_ambient_cover
    (path : CriticalPath T geometry a z) (hb : 0 < geometry.b T)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam T)
    (hj : Function.Injective j) (hjr : j.range = U T z)
    (κ : stabilizer T z →* J)
    (hκQ : κ.ker.map (stabilizer T z).subtype = Q T z)
    (hκL : ((Ltilde T z).subgroupOf (stabilizer T z)).map κ = B)
    (hconj : ∀ (g : stabilizer T z) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam T) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam T)⁻¹)
    (hinner : Z T a ≤ Ltilde T z ⊔ Q T z)
    (P : Sylow 2 (Ltilde T z))
    (hn : Z T a ≤ normalizer ((U T z ⊓ centralizer
      ((P : Subgroup (Ltilde T z)).map (Ltilde T z).subtype : Set (FreeAmalgam T)) :
        Subgroup (FreeAmalgam T)) : Set _)) :
    Z T a ≤ centralizer (U T z ⊓ centralizer
      ((P : Subgroup (Ltilde T z)).map (Ltilde T z).subtype : Set (FreeAmalgam T)) :
        Set (FreeAmalgam T)) := by
  have hAZ : Z T a ≤ stabilizer T z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ : Z T a →* J := κ.comp (inclusion hAZ)
  have hsource : (Z T a).subgroupOf (stabilizer T z) ≤
      (Ltilde T z).subgroupOf (stabilizer T z) ⊔ κ.ker := by
    apply (map_le_map_iff_of_injective (stabilizer T z).subtype_injective).mp
    rwa [Subgroup.map_sup,hκQ,map_subgroupOf_eq_of_le hAZ,
      map_subgroupOf_eq_of_le (Ltilde_le_stabilizer z)]
  have hmap : ((Z T a).subgroupOf (stabilizer T z)).map κ ≤ B := by
    rw [←hκL]
    exact map_le_map_iff.mpr hsource
  have hδB (x : Z T a) : δ x ∈ B := hmap ⟨inclusion hAZ x,x.property,rfl⟩
  let β := e.groupEquiv.toMonoidHom.comp (δ.codRestrict B hδB)
  have hβmark (x : Z T a) : (e.groupEquiv.symm (β x) : J) = δ x := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨δ x,_⟩) : J) = δ x
    rw [e.groupEquiv.symm_apply_apply]
  have hβ (x : Z T a) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) v)) =
        (x : FreeAmalgam T) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam T)⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (β x)) v)) = _
    rw [hβmark]
    exact hconj (inclusion hAZ x) v
  let f₀ : Ltilde T z →* J := κ.comp (inclusion (Ltilde_le_stabilizer z))
  have hf₀ : f₀.range=B := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hκL
  let f := e.groupEquiv.toMonoidHom.comp
    (f₀.codRestrict (B) (fun x => hf₀ ▸ ⟨x,rfl⟩))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y,hy⟩ := (show (e.groupEquiv.symm x : J) ∈ f₀.range from hf₀.symm ▸ (e.groupEquiv.symm x).property)
    refine ⟨y,?_⟩
    change e.groupEquiv ⟨f₀ y,_⟩=x
    rw [show (⟨f₀ y,_⟩ : B)=e.groupEquiv.symm x from Subtype.ext hy,
      e.groupEquiv.apply_symm_apply]
  have hfmark (x : Ltilde T z) : (e.groupEquiv.symm (f x) : J)=f₀ x := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨f₀ x,_⟩) : J)=f₀ x
    rw [e.groupEquiv.symm_apply_apply]
  have hfact (x : Ltilde T z) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (f x) v)) =
        (x : FreeAmalgam T)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam T)⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (f x)) v))=_
    rw [hfmark]
    exact hconj (inclusion (Ltilde_le_stabilizer z) x) v
  let actor := (P : Subgroup (Ltilde T z)).map (Ltilde T z).subtype
  let eP : (P : Subgroup (Ltilde T z)) ≃* actor :=
    (P : Subgroup (Ltilde T z)).equivMapOfInjective (Ltilde T z).subtype (Ltilde T z).subtype_injective
  let π : actor →* L (K := F) :=
    (f.comp (P : Subgroup (Ltilde T z)).subtype).comp eP.symm.toMonoidHom
  let := finite_stabilizer T z
  let : Finite (Ltilde T z) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer z)) (inclusion_injective _)
  let S := P.mapSurjective (f := f) hf
  have hπ : π.range=(S : Subgroup (L (K := F))) := by
    change π.range = (P.mapSurjective (f := f) hf : Subgroup _)
    rw [Sylow.coe_mapSurjective,MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective eP.symm.toMonoidHom eP.symm.surjective,
      ←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
  have hT (t : actor) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (π t) v)) =
        (t : FreeAmalgam T)*j (Multiplicative.ofAdd v)*(t : FreeAmalgam T)⁻¹ := by
    have hh := hfact (eP.symm t) v
    have hval : ((eP.symm t : P) : FreeAmalgam T)=(t : FreeAmalgam T) :=
      congrArg Subtype.val (eP.apply_symm_apply t)
    exact hval ▸ hh
  exact quadratic_centralizes_normalized_embedded_sylow_seed (U T z) (Z T a) actor
    j hj hjr π S hπ β (MovedSection.coverAction s e) hT hβ
    (MovedSection.coverProjection s e) hp
    (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_embedded_natural_actor_quadratic
      path hb (MovedSection.coverAction s e) (MovedSection.coverProjection s e) hp j hj hjr β hβ) hn
end Abstract

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

theorem Input.replacement_critical_centralizes_normalized_sylow_seed
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (P : Sylow 2 (Ltilde d.radical z))
    (hn : Z d.radical a ≤ normalizer ((U d.radical z ⊓ centralizer
      ((P : Subgroup (Ltilde d.radical z)).map (Ltilde d.radical z).subtype : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    Z d.radical a ≤ centralizer (U d.radical z ⊓ centralizer
      ((P : Subgroup (Ltilde d.radical z)).map (Ltilde d.radical z).subtype : Set (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  exact critical_seed_central_of_ambient_cover path hb s e he j hj hjr κ hκQ hκL hconj
    (h.replacement_critical_image_inner d path hb) P hn

theorem Input.replacement_sylow_seed_le_core_of_distance
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    {u c t : Vertex d.radical} (hd : color d.radical u = false) (hcc : color d.radical c = false)
    (hdc : (cosetGraph d.radical).dist u c ≤ geometry.b d.radical)
    (hct : (cosetGraph d.radical).dist c t < geometry.b d.radical)
    (P : Sylow 2 (Ltilde d.radical u))
    (hn : Q d.radical t ≤ normalizer ((U d.radical u ⊓ centralizer
      ((P : Subgroup (Ltilde d.radical u)).map (Ltilde d.radical u).subtype : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    U d.radical u ⊓ centralizer
      ((P : Subgroup (Ltilde d.radical u)).map (Ltilde d.radical u).subtype : Set (FreeAmalgam d.radical)) ≤ Q d.radical c := by
  by_cases hz : Z d.radical u ≤ Q d.radical c
  · exact (inf_le_left.trans (U_le_Z u)).trans hz
  have hcrit : CriticalPair d.radical u c (geometry.exists_critical u hd) := by
    refine ⟨le_antisymm ?_ (criticalDistance_le d.radical u _ hz),hz⟩
    rwa [geometry.distance_constant u hd]
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hrev := critical_reverse d.radical geometry hedge u hd
    (by rwa [geometry.distance_constant u hd]) c hcc hcrit
  obtain ⟨walk,hwalk⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c u
  let path : CriticalPath d.radical geometry c u := ⟨hcc,walk,hwalk,hrev⟩
  have hZt : Z d.radical c ≤ Q d.radical t := Z_le_Q_of_dist_lt d.radical c (geometry.exists_critical c hcc)
    (by rwa [geometry.distance_constant c hcc])
  have hcentral := h.replacement_critical_centralizes_normalized_sylow_seed d path hb P (hZt.trans hn)
  rw [←MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) c hcc]
  exact le_inf
    ((inf_le_left.trans (U_le_Z u)).trans
      (Z_le_stabilizer_of_dist_le u (geometry.exists_critical u hd) hcrit.1.le))
    (le_centralizer_iff.mp hcentral)

theorem Input.replacement_two_edge_sylow_seed_le_distant_core
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    {a u c t : Vertex d.radical} (hd : color d.radical u = false) (hcc : color d.radical c = false)
    (hat : Adjacent d.radical a t) (hdt : Adjacent d.radical u t)
    (hac : (cosetGraph d.radical).dist a c + 2 ≤ geometry.b d.radical)
    (P : Sylow 2 (Ltilde d.radical u))
    (hn : Q d.radical t ≤ normalizer ((U d.radical u ⊓ centralizer
      ((P : Subgroup (Ltilde d.radical u)).map (Ltilde d.radical u).subtype : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    U d.radical u ⊓ centralizer
      ((P : Subgroup (Ltilde d.radical u)).map (Ltilde d.radical u).subtype : Set (FreeAmalgam d.radical)) ≤ Q d.radical c := by
  have hdt1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hdt)
  have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hat)
  have htac := (cosetGraph_connected d.radical).dist_triangle (u := t) (v := a) (w := c)
  have hdtc := (cosetGraph_connected d.radical).dist_triangle (u := u) (v := t) (w := c)
  have hta1 : (cosetGraph d.radical).dist t a = 1 := by rwa [SimpleGraph.dist_comm]
  rw [hta1] at htac
  have hdc : (cosetGraph d.radical).dist u c ≤ geometry.b d.radical := by omega
  have hct : (cosetGraph d.radical).dist c t < geometry.b d.radical := by
    rw [SimpleGraph.dist_comm]
    omega
  exact h.replacement_sylow_seed_le_core_of_distance d geometry hb hd hcc hdc hct P hn


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
