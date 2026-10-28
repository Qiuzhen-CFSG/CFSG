module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MaximalFamily
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalGeneration
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Maximal offenders on every original symplectic edge

The literal small-mover inequalities and maximum-order family transport
through the faithful coordinates at each edge. In the full point-core branch
their join is the entire edge kernel. There is only one quotient line moving
the natural module with index two. Two distinct transvection preimages thus
cannot generate a critical image, excluding the exceptional tilde-Z case.

These facts retain the actual graph kernels, centralizer indices and original
natural module. They supply the coordinated choices in MS93 (5.5).
Source: Meierfrankenfeld--Stellmacher (1993), Section 5.0 and (5.4), pp.912,915.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal]

def edgeSmallMover (c t : Vertex R) (E : Subgroup (FreeAmalgam R)) : Prop :=
  E ≤ Q R t ∧ (centralizer (E : Set (FreeAmalgam R))).relIndex (U R c) ≤
    (Q R c).relIndex E ∧
    (centralizer (E : Set (FreeAmalgam R))).relIndex (U R c) ≤ 4

def edgeMaximalOffenders (c t : Vertex R) : Set (Subgroup (FreeAmalgam R)) :=
  {E | edgeSmallMover c t E ∧ ∀ F, edgeSmallMover c t F → Nat.card F ≤ Nat.card E}

noncomputable def edgeOffenderJoin (c t : Vertex R) : Subgroup (FreeAmalgam R) :=
  sSup (edgeMaximalOffenders c t)

namespace Source
variable (s : Source L R W)

omit [Finite M] [W.Normal] in
private theorem centralizer_index_map {G : Type*} [Group G]
    (i : M →* G) (hi : Function.Injective i) (E : Subgroup M) :
    (centralizer (E.map i : Set G)).relIndex (W.map i) =
      (centralizer (E : Set M)).relIndex W := by
  rw [← inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective i hi,
    relIndex_map_map_of_injective _ _ hi,inf_relIndex_left]

private theorem edge_coordinates (h : NativeCentralLayer s) {c t : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t) :
    ∃ i : M →* FreeAmalgam R, Function.Injective i ∧
      i.range = stabilizer R c ∧ R.map i = Q R t ∧
      (pCore 2 M).map i = Q R c ∧ W.map i = U R c := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c t).mp hct
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective R),?_,?_,?_,?_⟩
    · have h := stabilizer_act R g (alpha R)
      dsimp only [i]
      rw [MonoidHom.range_comp]
      change (Mbar R).map (MulAut.conj g⁻¹).toMonoidHom = _
      simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using h.symm
    · have h := Q_act R g (beta R)
      rw [Q_beta] at h
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using h.symm
    · have h := Q_act R g (alpha R)
      rw [Q_alpha R s.two_group s.core_le] at h
      simpa only [alpha,act_mVertex,one_mul,Q_alpha R s.two_group s.core_le,map_map] using h.symm
    · have he := U_act R g (alpha R)
      rw [h.U_eq_module] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc

omit [Finite M] in
private theorem edgeSmallMover_map_iff
    (i : M →* FreeAmalgam R) (hi : Function.Injective i) {c t : Vertex R}
    (hiR : R.map i = Q R t) (hiQ : (pCore 2 M).map i = Q R c)
    (hiW : W.map i = U R c) (E : Subgroup M) :
    edgeSmallMover c t (E.map i) ↔ s.smallMover E := by
  unfold edgeSmallMover smallMover
  rw [←hiR,←hiQ,←hiW,map_le_map_iff_of_injective hi,
    centralizer_index_map i hi,relIndex_map_map_of_injective _ _ hi,
    ←s.projection_kernel,relIndex_ker]

omit [Finite M] in
private theorem edgeMaximal_map_iff
    (i : M →* FreeAmalgam R) (hi : Function.Injective i) {c t : Vertex R}
    (hiR : R.map i = Q R t) (hiQ : (pCore 2 M).map i = Q R c)
    (hiW : W.map i = U R c) (E : Subgroup M) :
    E.map i ∈ edgeMaximalOffenders c t ↔ E ∈ s.maximalOffenders := by
  constructor
  · rintro ⟨he,hm⟩
    refine ⟨(s.edgeSmallMover_map_iff i hi hiR hiQ hiW E).mp he,?_⟩
    intro F hF
    have hh := hm (F.map i) ((s.edgeSmallMover_map_iff i hi hiR hiQ hiW F).mpr hF)
    simpa only [card_map_of_injective hi] using hh
  · rintro ⟨he,hm⟩
    refine ⟨(s.edgeSmallMover_map_iff i hi hiR hiQ hiW E).mpr he,?_⟩
    intro F hF
    have hFi : F ≤ i.range := hF.1.trans (hiR ▸ map_le_range i R)
    have hFmap : (F.comap i).map i = F := map_comap_eq_self hFi
    have hsm := (s.edgeSmallMover_map_iff i hi hiR hiQ hiW (F.comap i)).mp
      (hFmap.symm ▸ hF)
    have hh := hm (F.comap i) hsm
    calc
      Nat.card F = Nat.card ((F.comap i).map i) := congrArg (fun H : Subgroup (FreeAmalgam R) => Nat.card H) hFmap.symm
      _ = Nat.card (F.comap i) := card_map_of_injective hi
      _ ≤ Nat.card E := hh
      _ = Nat.card (E.map i) := (card_map_of_injective hi).symm

theorem edgeOffenderJoin_eq (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t) :
    edgeOffenderJoin c t = Q R t := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiW⟩ := s.edge_coordinates h hc hct
  apply le_antisymm
  · apply sSup_le
    intro E hE
    exact hE.1.1
  · have he := congrArg (Subgroup.map i) (s.offenderJoin_eq u hfull)
    rw [hiR] at he
    rw [←he,offenderJoin,sSup_eq_iSup,Subgroup.map_iSup]
    apply iSup_le
    intro F
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hF
    exact le_sSup ((s.edgeMaximal_map_iff i hi hiR hiQ hiW F).mpr hF)

omit [Finite M] in
private theorem small_image_line (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {A : Subgroup M} (hA : A ≤ R) (hc : Nat.card (A.map s.projection) = 2)
    (hi : (centralizer (A : Set M)).relIndex W ≤ 2) :
    A.map s.projection =
      CFSG.Quasithin.ChapterB.Offenders.Six.last.map (MulAut.conj u).toMonoidHom := by
  have hs := (SmallImages.admissible_iff_conjugate u ((map_mono hA).trans_eq hfull)).mp
    (show 2 ^ Representation.BinaryOffender.fixedCodim Model.rho (A.map s.projection) ≤
      Nat.card (A.map s.projection) ∧
      2 ^ Representation.BinaryOffender.fixedCodim Model.rho (A.map s.projection) ≤ 4 from by
        rw [←s.fixed_index,hc]
        exact ⟨hi,hi.trans (by decide)⟩)
  rcases hs with hz | he | ⟨j,he⟩
  · rw [hz,card_bot] at hc
    omega
  · exact he
  · rw [he,SmallImages.plane_card_conjugate] at hc
    omega

theorem edge_transvection_preimage_unique (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    {A B : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R t) (hB : B ≤ Q R t)
    (hqA : Q R c ≤ A) (hqB : Q R c ≤ B)
    (ha : (Q R c).relIndex A = 2) (hb : (Q R c).relIndex B = 2)
    (hfixA : (centralizer (A : Set (FreeAmalgam R))).relIndex (U R c) ≤ 2)
    (hfixB : (centralizer (B : Set (FreeAmalgam R))).relIndex (U R c) ≤ 2) : A = B := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiW⟩ := s.edge_coordinates h hc hct
  have hs (E : Subgroup (FreeAmalgam R)) (hE : E ≤ Q R t) :
      (E.comap i).map i = E := map_comap_eq_self
        (hE.trans (hiR ▸ map_le_range i R))
  have hle (E : Subgroup (FreeAmalgam R)) (hE : E ≤ Q R t) : E.comap i ≤ R := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hs E hE,hiR]
    exact hE
  have hcard (E : Subgroup (FreeAmalgam R)) (hE : E ≤ Q R t)
      (hcE : (Q R c).relIndex E = 2) : Nat.card ((E.comap i).map s.projection) = 2 := by
    rw [←relIndex_ker, s.projection_kernel,←relIndex_map_map_of_injective _ _ hi,hiQ,hs E hE]
    exact hcE
  have hfix (E : Subgroup (FreeAmalgam R)) (hE : E ≤ Q R t)
      (hf : (centralizer (E : Set (FreeAmalgam R))).relIndex (U R c) ≤ 2) :
      (centralizer (E.comap i : Set M)).relIndex W ≤ 2 := by
    rw [←centralizer_index_map i hi,hs E hE,hiW]
    exact hf
  have hk (E : Subgroup (FreeAmalgam R)) (hE : Q R c ≤ E) :
      s.projection.ker ≤ E.comap i := by
    rw [s.projection_kernel]
    intro q hq
    exact hE (hiQ ▸ mem_map_of_mem i hq)
  have hAB : (A.comap i).map s.projection = (B.comap i).map s.projection :=
    (s.small_image_line u hfull (hle A hA) (hcard A hA ha) (hfix A hA hfixA)).trans
      (s.small_image_line u hfull (hle B hB) (hcard B hB hb) (hfix B hB hfixB)).symm
  have he := map_injective_of_ker_le s.projection (hk A hqA) (hk B hqB) hAB
  have hm := congrArg (Subgroup.map i) he
  simpa only [hs A hA,hs B hB] using hm

/-- Two distinct transvection lines generating the forward critical image,
written as their full preimages above the actual endpoint kernel. This is the
exception in the definition of tilde Z in MS93 Section 5.0, p.912. -/
def SplitCriticalImage (a e : Vertex R) : Prop :=
  ∃ A B : Subgroup (FreeAmalgam R), Q R e ≤ A ∧ Q R e ≤ B ∧
    A ⊔ B = Q R e ⊔ Z R a ∧ A ≠ B ∧
    (Q R e).relIndex A = 2 ∧ (Q R e).relIndex B = 2 ∧
    (centralizer (A : Set (FreeAmalgam R))).relIndex (Z R e) = 2 ∧
    (centralizer (B : Set (FreeAmalgam R))).relIndex (Z R e) = 2

theorem critical_image_not_split (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {a e : Vertex R} (p : DistanceEight.PathCentrality.CriticalPath R s.geometry a e) :
    ¬ SplitCriticalImage a e := by
  rintro ⟨A,B,hqA,hqB,hgen,hne,hA,hB,hfixA,hfixB⟩
  have hpos : 0 < p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
  let t := p.walk.getVert (p.walk.length - 1)
  have hct : Adjacent R e t := by
    apply adjacent_symm R
    apply (cosetGraph_adj R _ _).mp
    have ht := p.walk.adj_getVert_succ (i := p.walk.length - 1) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.walk.length),
      SimpleGraph.Walk.getVert_length] using ht
  have htcol : color R t = true := by
    have hn := adjacent_color_ne R hct
    rw [p.end_color] at hn
    cases he : color R t <;> simp_all
  have hz : Z R a ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R a (s.geometry.exists_critical a p.start_color)
    rw [s.geometry.distance_constant a p.start_color]
    change (cosetGraph R).dist a (p.walk.getVert (p.walk.length - 1)) < s.geometry.b R
    rw [p.dist_start (by omega),←p.length_eq_b]
    omega
  have hqt : Q R e ⊔ Z R a ≤ Q R t := sup_le (Q_le_adjacent_h R htcol hct) hz
  have hAE : A ≤ Q R t := le_sup_left.trans (hgen.le.trans hqt)
  have hBE : B ≤ Q R t := le_sup_right.trans (hgen.le.trans hqt)
  let : Finite (stabilizer R e) := finite_stabilizer R e
  let : Finite (Z R e) := Finite.of_injective (inclusion (Z_le_stabilizer R e))
    (inclusion_injective _)
  have hfix (E : Subgroup (FreeAmalgam R))
      (he : (centralizer (E : Set (FreeAmalgam R))).relIndex (Z R e) = 2) :
      (centralizer (E : Set (FreeAmalgam R))).relIndex (U R e) ≤ 2 := by
    rw [←he]
    exact relIndex_le_of_le_right (DistanceEight.U_le_Z R e) index_ne_zero_of_finite
  exact hne (s.edge_transvection_preimage_unique h u hfull p.end_color hct
    hAE hBE hqA hqB hA hB (hfix A hfixA) (hfix B hfixB))


end Source
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
