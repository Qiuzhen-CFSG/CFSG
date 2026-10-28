module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NoncentralSeedChoice
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.BackwardEscape

/-!
# Shifted critical endpoint and simultaneous line choice

Reverse the original critical pair and apply universal radius escape at its
second predecessor. The actual radius generators supply a new endpoint at
distance exactly two from the old endpoint, critical with the original
second vertex. For a nonzero moving line there, its unique nonidentity
element supplies the noncentral seed generator. Conjugation covariance
transports that choice from the base vertex to the actual second vertex.

Both the generating local centralizer and the noncentral movement use the
same endpoint and the same conjugator, on the literal subgroup image. The
SourceData application retains its original characteristic replacement.
Source: MS93 (5.9), the second starred choice, printed pp.920--922, toward
Aschbacher--Smith C.1.37 and 13.7.4(1).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

/-- Shift the endpoint while retaining the original second vertex. -/
theorem exists_shifted_critical_endpoint (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ∃ d, color R d=false ∧ (cosetGraph R).dist e d=2 ∧
      CriticalPair R (p.walk.getVert 2) d
        (s.geometry.exists_critical _ ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide))) := by
  have hlen : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  have hc : color R (p.walk.getVert 2)=false := (p.vertex_color hlen).mpr (by decide)
  have hrev := critical_reverse R s.geometry s.edgeCentralizerCondition
    (alpha R) rfl s.criticalDistance_pos e p.end_color p.critical
  have hca : (cosetGraph R).dist (p.walk.getVert 2) (alpha R)=2 := by
    rw [SimpleGraph.dist_comm,p.dist_start hlen]
  have hec : (cosetGraph R).dist e (p.walk.getVert 2)+2=s.geometry.b R := by
    rw [SimpleGraph.dist_comm,p.dist_end,p.length_eq_b]
    omega
  have hpath : (cosetGraph R).dist e (p.walk.getVert 2)+2=(cosetGraph R).dist e (alpha R) := by
    rw [hec,SimpleGraph.dist_comm,←p.shortest,p.length_eq_b]
  have hescape := s.criticalEscape h u hfull (by omega) e p.end_color
    (alpha R) hrev (p.walk.getVert 2) hca hpath
  obtain ⟨d,hd,hde,hcrit⟩ := exists_critical_shift R p.end_color hec hescape
  refine ⟨d,hd,by simpa only [SimpleGraph.dist_comm] using hde,?_⟩
  apply critical_reverse R s.geometry s.edgeCentralizerCondition d hd _ _ hc hcrit
  rw [s.geometry.distance_constant d hd]
  change 0<s.geometry.b R
  omega

private theorem exists_moving_line_generator_base (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {e : Vertex R} (p : CriticalPath R s.geometry (alpha R) e)
    (H : Subgroup (FreeAmalgam R)) (hHU : H ≤ U R (alpha R))
    (hH : H ≠ ⊥) (hcard : Nat.card H ≤ 2) :
    ∃ y ∈ Ltilde R (alpha R),
      (stabilizer R (alpha R) ⊓ centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam R))) ⊔
        Z R e = stabilizer R (alpha R) ∧
      ¬ H.map (MulAut.conj y).toMonoidHom ≤ centralizer (Z R e : Set (FreeAmalgam R)) := by
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R _
  let : Finite H := Finite.of_injective
    (inclusion (hHU.trans ((U_le_Z _).trans (Z_le_stabilizer R _)))) (inclusion_injective _)
  let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  have hc : Nat.card H=2 := by have hh := Finite.one_lt_card (α:=H); omega
  obtain ⟨z,hzn,hunique⟩ := (Nat.card_eq_two_iff' (1:H)).mp hc
  have hzU : (z:FreeAmalgam R)∈U R (alpha R) := hHU z.property
  have hzD : (z:FreeAmalgam R)∉fixedCore R (alpha R) := by
    intro hz
    have he : (z:FreeAmalgam R)∈(⊥:Subgroup (FreeAmalgam R)) := by
      rw [←s.movingLayer_inf_fixedCore_eq_bot h]
      exact ⟨hzU,hz⟩
    exact hzn (Subtype.ext (mem_bot.mp he))
  obtain ⟨y,hy,hgen,hmove⟩ := s.exists_noncentral_seed_generator h u hfull p ((U_le_Z _) hzU) hzD
  have hcentral : centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam R)) =
      centralizer ({y*(z:FreeAmalgam R)*y⁻¹}:Set (FreeAmalgam R)) := by
    apply le_antisymm
    · apply centralizer_le
      exact Set.singleton_subset_iff.mpr (mem_map_of_mem _ z.property)
    · intro q hq x hx
      obtain ⟨x,hx,rfl⟩ := hx
      by_cases hx1 : x=1
      · simp only [hx1,map_one,one_mul,mul_one]
      · have he : (⟨x,hx⟩:H)=z := hunique _ (fun he => hx1 (congrArg Subtype.val he))
        have he' : x=(z:FreeAmalgam R) := congrArg Subtype.val he
        rw [he']
        exact hq _ (Set.mem_singleton _)
  refine ⟨y,hy,?_,?_⟩
  · simpa only [hcentral] using hgen
  · intro hh
    exact hmove (hh (mem_map_of_mem _ z.property))

/-- A moving line at any critical starting vertex has one simultaneous choice. -/
theorem exists_moving_line_generator_at (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {c d : Vertex R} (hc : color R c=false)
    (hcrit : CriticalPair R c d (s.geometry.exists_critical c hc))
    (H : Subgroup (FreeAmalgam R)) (hHU : H ≤ U R c)
    (hH : H ≠ ⊥) (hcard : Nat.card H ≤ 2) :
    ∃ y ∈ stabilizer R c,
      (stabilizer R c ⊓ centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam R))) ⊔
        Z R d = stabilizer R c ∧
      ¬ H.map (MulAut.conj y).toMonoidHom ≤ centralizer (Z R d : Set (FreeAmalgam R)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R hc
  have hbase : act R g⁻¹ (mVertex R g)=alpha R := by
    simp only [act_mVertex,mul_inv_cancel]; rfl
  have hbasecol : color R (act R g⁻¹ (mVertex R g))=false := by rw [hbase]; rfl
  have hcrit' := (criticalPair_act_iff R g⁻¹ (mVertex R g) d
    (s.geometry.exists_critical _ hc) (s.geometry.exists_critical _ hbasecol)).mpr hcrit
  have hcrit0 : CriticalPair R (alpha R) (act R g⁻¹ d) (s.geometry.exists_critical _ rfl) := by
    simpa only [hbase] using hcrit'
  let H0 := H.map (MulAut.conj g).toMonoidHom
  have hU : (U R (mVertex R g)).map (MulAut.conj g).toMonoidHom = U R (alpha R) := by
    have he := U_act R g⁻¹ (mVertex R g)
    simpa only [inv_inv,hbase] using he.symm
  have hH0 : H0 ≠ ⊥ := by
    intro hz
    apply hH
    apply map_injective (f:=(MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    simpa only [H0,Subgroup.map_bot] using hz
  have hc0 : Nat.card H0 ≤ 2 := by
    dsimp only [H0]
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  obtain ⟨y0,hy0,hgen0,hmove0⟩ := s.exists_moving_line_generator_base h u hfull
    (CriticalPath.ofPair rfl hcrit0) H0 ((map_mono hHU).trans_eq hU) hH0 hc0
  let y := g⁻¹*y0*g
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have hG : (stabilizer R (alpha R)).map f=stabilizer R (mVertex R g) := by
    simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act R g (alpha R)).symm
  have hZ : (Z R (act R g⁻¹ d)).map f=Z R d := by
    rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
  have hHmap : (H0.map (MulAut.conj y0).toMonoidHom).map f = H.map (MulAut.conj y).toMonoidHom := by
    dsimp only [H0]
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change g⁻¹*(y0*(g*x*g⁻¹)*y0⁻¹)*(g⁻¹)⁻¹=(g⁻¹*y0*g)*x*(g⁻¹*y0*g)⁻¹
    group
  have hy : y ∈ stabilizer R (mVertex R g) := by
    rw [←hG]
    have he : f y0=y := by
      change g⁻¹*y0*(g⁻¹)⁻¹=g⁻¹*y0*g
      rw [inv_inv]
    rw [←he]
    exact mem_map_of_mem f (Ltilde_le_stabilizer _ hy0)
  refine ⟨y,hy,?_,?_⟩
  · have hh := congrArg (Subgroup.map f) hgen0
    rw [Subgroup.map_sup,←map_inf_centralizer_of_injective f (MulAut.conj g⁻¹).injective,
      hG,hZ,hHmap] at hh
    exact hh
  · intro hh
    apply hmove0
    intro x hx z hz
    have hfx : f x ∈ H.map (MulAut.conj y).toMonoidHom := hHmap ▸ mem_map_of_mem f hx
    have hfz : f z ∈ Z R d := hZ ▸ mem_map_of_mem f hz
    apply (show Function.Injective f from (MulAut.conj g⁻¹).injective)
    simpa only [map_mul] using hh hfx (f z) hfz

/-- The exact shifted endpoint and line choice used in source (5.9). -/
theorem exists_shifted_seed_choice (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (H : Subgroup (FreeAmalgam R)) (hHU : H ≤ U R (p.walk.getVert 2))
    (hH : H ≠ ⊥) (hcard : Nat.card H ≤ 2) :
    ∃ d, color R d=false ∧ (cosetGraph R).dist e d=2 ∧
      CriticalPair R (p.walk.getVert 2) d
        (s.geometry.exists_critical _ ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide))) ∧
      ∃ y ∈ stabilizer R (p.walk.getVert 2),
        (stabilizer R (p.walk.getVert 2) ⊓
          centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam R))) ⊔ Z R d =
            stabilizer R (p.walk.getVert 2) ∧
        ¬ H.map (MulAut.conj y).toMonoidHom ≤ centralizer (Z R d : Set (FreeAmalgam R)) := by
  obtain ⟨d,hd,hed,hcrit⟩ := s.exists_shifted_critical_endpoint h u hfull hb p
  refine ⟨d,hd,hed,hcrit,?_⟩
  exact s.exists_moving_line_generator_at h u hfull
    ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide)) hcrit H hHU hH hcard

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (h : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The original characteristic replacement supplies the shifted choice or
its literal alternating-block alternative. -/
theorem reducedSource_block_or_shifted_seed_choice
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d h).reduce r).geometry (alpha r.radical) e)
    (hb : 4 < ((originalSource d h).reduce r).geometry.b r.radical)
    (H : Subgroup (FreeAmalgam r.radical)) (hHU : H ≤ U r.radical (p.walk.getVert 2))
    (hH : H ≠ ⊥) (hcard : Nat.card H ≤ 2) :
    IsAlternatingBlock L 6 ∨
      ∃ f, color r.radical f=false ∧ (cosetGraph r.radical).dist e f=2 ∧
        CriticalPair r.radical (p.walk.getVert 2) f
          (((originalSource d h).reduce r).geometry.exists_critical _
            ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide))) ∧
        ∃ y ∈ stabilizer r.radical (p.walk.getVert 2),
          (stabilizer r.radical (p.walk.getVert 2) ⊓
            centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam r.radical))) ⊔
              Z r.radical f = stabilizer r.radical (p.walk.getVert 2) ∧
          ¬ H.map (MulAut.conj y).toMonoidHom ≤ centralizer (Z r.radical f : Set (FreeAmalgam r.radical)) := by
  rcases reducedSource_block_or_full_point_image d h r with hblock | hf
  · exact Or.inl hblock
  · let s := (originalSource d h).reduce r
    have hn := reduced_nativeCentralLayer d h r
    have he : r.radical.map s.projection = Model.E.map
        (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hf
    exact Or.inr (s.exists_shifted_seed_choice hn _ he hb p H hHU hH hcard)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
