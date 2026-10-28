module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NaturalSectionTransfer
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardMovedSpanNatural
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallCriticalLine

public import Theory.GroupTheory.PResidual.SubnormalCoreAction

public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.SpecificGroups.SymmetricSix.ResidualSmallIndex

/-!
# Natural quotients of the selected critical orbit span

For a critical path starting at the original replacement vertex, let P be
its second seed's normal span in that vertex stabilizer. Radius centrality
makes P/Z(P) elementary abelian and makes the original two-core act trivially
on it. If P is nonabelian, the resulting action of the same marked S₆ is
faithful. An odd transvection with fixed index two identifies the moved
section. The explicit quotient maps then identify [P,L̃]/Z([P,L̃]) with the
natural module, without replacing either original central cover by a split
subgroup.

When P' is fixed by the alternating component, the central-section
calculation gives its actual derived line and transfers that line through
every subgroup of index at most two. Nonabelianness also constructs a
critical conjugate path through the original first edge and base vertex.
The selected natural quotient also detects endpoint movement modulo the
starting seed. With the source core index and endpoint-action estimates,
residual contraction places the full core commutator in that seed and the
moved span; their derived subgroups coincide, and index-two transfer holds
for the full core as well. The terminal implication uses the conjugate path
and the opposite core bounds on the same literal ambient subgroups.

The displayed selected-path estimates and opposite core bounds are still
source obligations of qt-e-ms-small-a6-exhaustion-large-distance. Neither
this implication nor its known-simple application establishes (5.12) until
those premises are discharged. The same owner retains (5.11) and final
large-distance assembly; qt-e-ms-small-a6-reconstruction owns the final
unconditional reconstruction.

Source: Meierfrankenfeld--Stellmacher (1993), (3.10), printed pp.879--881,
and the terminal argument of (5.12), pp.924--927. The quotient and terminal
proofs adapt SymplecticSetup.ForwardMovedSpanNatural and
SymplecticSetup.DistanceFourImpossible to the original central cover and
arbitrary radical image.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SelectedSpan
variable {M₀ : Type*} [Group M₀] (R₀ : Subgroup M₀)
private theorem core_le_action_kernel (K : Subgroup M₀) (c : Vertex R₀)
    (hK : K.map (embedM R₀) ≤ Q R₀ (alpha R₀))
    (hcentral : ⁅localZSpan R₀ c (alpha R₀),Q R₀ (alpha R₀)⁆ ≤
      centralizer (localZSpan R₀ c (alpha R₀) : Set (FreeAmalgam R₀))) :
    K ≤ (forwardSpanCentralAction R₀ c).ker := by
  let P := localZSpan R₀ c (alpha R₀)
  intro m hm
  have hmQ : embedM R₀ m ∈ Q R₀ (alpha R₀) := hK (mem_map_of_mem (embedM R₀) hm)
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) v
  rw [forwardSpanCentralAction_apply]
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have hmem : ⁅embedM R₀ m,(x:FreeAmalgam R₀)⁆ ∈ ⁅P,Q R₀ (alpha R₀)⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hmQ x.property
  change (y:FreeAmalgam R₀) * (embedM R₀ m*(x:FreeAmalgam R₀)*(embedM R₀ m)⁻¹/(x:FreeAmalgam R₀)) =
    (embedM R₀ m*(x:FreeAmalgam R₀)*(embedM R₀ m)⁻¹/(x:FreeAmalgam R₀))*(y:FreeAmalgam R₀)
  simpa only [div_eq_mul_inv,commutatorElement_def] using hcentral hmem y y.property

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SelectedSpan

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
theorem selected_span_central_quotient_elementary (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (c : Vertex d.radical)
    (hd : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2) :
    IsElementaryAbelian 2 ((localZSpan d.radical c (alpha d.radical)) ⧸
      center (localZSpan d.radical c (alpha d.radical))) := by
  let P := localZSpan d.radical c (alpha d.radical)
  have hPV : P ≤ V d.radical (alpha d.radical) := localZSpan_le_V d.radical hd
  have hs (x : P) : x^2 ∈ center P := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact radius_derived_central s hc hb (alpha d.radical) rfl
      (radius_sq_mem_derived (replacementGeometry h d) (replacementDistance_pos h d)
        (alpha d.radical) rfl ⟨x,hPV x.property⟩) y (hPV y.property)
  have hp (x : P ⧸ center P) : x^2 = 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hs x)
  let : IsMulCommutative (P ⧸ center P) :=
    ⟨⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hp z)) x y).eq⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp⟩

include s in
theorem selected_span_central_action_kills_core (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (c : Vertex d.radical)
    (hd : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2) :
    pCore 2 d.overgroup ≤ (forwardSpanCentralAction d.radical c).ker := by
  apply SelectedSpan.core_le_action_kernel
  · rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
  · have hPV := localZSpan_le_V d.radical hd
    exact ((commutator_mono hPV le_rfl).trans (radius_commutator_central_general s hc hb)).trans
      (centralizer_le hPV)

/-- Descent on the actual orbit span, without a natural-subgroup assumption. -/
def selectedSpanSymmetricAction (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (c : Vertex d.radical)
    (hd : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2) :
    Equiv.Perm (Fin 6) →* MulAut ((localZSpan d.radical c (alpha d.radical)) ⧸
      center (localZSpan d.radical c (alpha d.radical))) :=
  s.projection.liftOfSurjective s.surjective ⟨forwardSpanCentralAction d.radical c,by
    rw [s.projection_kernel]
    exact selected_span_central_action_kills_core s hc hb c hd⟩

theorem selectedSpanSymmetricAction_projection (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (c : Vertex d.radical)
    (hd : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2) (m : d.overgroup) :
    selectedSpanSymmetricAction s hc hb c hd (s.projection m) =
      forwardSpanCentralAction d.radical c m := by
  simp [selectedSpanSymmetricAction,MonoidHom.liftOfSurjective]

include h in
private theorem selected_residual_edge_generation {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Ltilde d.radical a ⊔ Q d.radical t = stabilizer d.radical a := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

include s in
/-- Faithfulness follows from nonabelianness of this selected span. -/
theorem selected_span_symmetric_action_injective
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (ρ : Equiv.Perm (Fin 6) →* MulAut ((localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ⧸
      center (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical))))
    (hρ : ∀ m : d.overgroup, ρ (s.projection m)=forwardSpanCentralAction d.radical (p.walk.getVert 2) m) :
    Function.Injective ρ := by
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  by_contra hne
  have hAlt : alternatingGroup (Fin 6)≤ρ.ker :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot _).mpr hne)
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan d.radical c (alpha d.radical)
  let C := (center P).map P.subtype
  let B := Z d.radical c⊔C
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color d.radical c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent d.radical c t :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hZP : Z d.radical c≤P := Z_le_localZSpan d.radical _ _
  have hCP : C≤P := map_subtype_le _
  have hCC : C≤centralizer (P:Set (FreeAmalgam d.radical)) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
  have hBP : B≤P := sup_le hZP hCP
  have hPL : ⁅P,Ltilde d.radical (alpha d.radical)⁆≤C := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl z hz
    rw [Ltilde_alpha,replacement_residual h d] at hl
    obtain ⟨m,hm,rfl⟩ := hl
    have hmAlt : s.projection m∈alternatingGroup (Fin 6) :=
      s.component_image ▸ mem_map_of_mem s.projection hm
    have he := hρ m
    rw [MonoidHom.mem_ker.mp (hAlt hmAlt)] at he
    have hh := DFunLike.congr_fun he (QuotientGroup.mk' (center P) ⟨z,hz⟩)
    have hq : QuotientGroup.mk' (center P)
        (forwardSpanAction d.radical c m ⟨z,hz⟩) = QuotientGroup.mk' (center P) ⟨z,hz⟩ := by
      exact (forwardSpanCentralAction_apply d.radical c m ⟨z,hz⟩).symm.trans
        (by simpa only [MulAut.one_apply] using hh.symm)
    have hmem := QuotientGroup.eq_iff_div_mem.mp hq
    refine ⟨forwardSpanAction d.radical c m ⟨z,hz⟩/⟨z,hz⟩,hmem,?_⟩
    change embedM d.radical m*z*(embedM d.radical m)⁻¹/z=⁅embedM d.radical m,z⁆
    rw [div_eq_mul_inv,commutatorElement_def]
  have hLB : Ltilde d.radical (alpha d.radical)≤normalizer (B:Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hBP le_rfl).trans (hPL.trans le_sup_right))
  have hQtG : Q d.radical t≤stabilizer d.radical (alpha d.radical) := fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hQtGc : Q d.radical t≤stabilizer d.radical c := fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hGC : stabilizer d.radical (alpha d.radical)≤normalizer (C:Set (FreeAmalgam d.radical)) :=
    (localZSpan_normalized d.radical _ _).trans
      (normalizer_le_normalizer_characteristic_image P (center P))
  have hQtB : Q d.radical t≤normalizer (B:Set (FreeAmalgam d.radical)) :=
    (le_inf (hQtGc.trans (Z_normalized d.radical c)) (hQtG.trans hGC)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hGB : stabilizer d.radical (alpha d.radical)≤normalizer (B:Set (FreeAmalgam d.radical)) := by
    rw [←selected_residual_edge_generation (h := h) rfl hat]
    exact sup_le hLB hQtB
  have hPB : P≤B := by
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    apply iSup_le
    intro g
    rintro _ ⟨z,hz,rfl⟩
    exact (mem_normalizer_iff.mp (hGB ((stabilizer d.radical (alpha d.radical)).inv_mem g.property)) z).mp
      ((show Z d.radical c≤B from le_sup_left) hz)
  have hBC : B≤centralizer (B:Set (FreeAmalgam d.radical)) := by
    apply sup_le
    · apply le_centralizer_iff.mpr
      let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hc
      exact sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance)
        (hCC.trans (centralizer_le hZP))
    · exact hCC.trans (centralizer_le hBP)
  have hab : ⁅P,P⁆=⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((hPB.trans hBC).trans (centralizer_le hPB))
  exact hnonabelian hab

include s in
/-- On a nonabelian selected span, the original action has exactly the
original two-core as kernel, on the literal central quotient. -/
theorem selected_span_central_action_kernel
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    (forwardSpanCentralAction d.radical (p.walk.getVert 2)).ker =
      pCore 2 d.overgroup := by
  have hd : (cosetGraph d.radical).dist (p.walk.getVert 2) (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)]
  let ρ := selectedSpanSymmetricAction s hc hb (p.walk.getVert 2) hd
  have hρ := selectedSpanSymmetricAction_projection s hc hb (p.walk.getVert 2) hd
  have hf := selected_span_symmetric_action_injective s hb p hnonabelian ρ hρ
  have heq : ρ.comp s.projection = forwardSpanCentralAction d.radical (p.walk.getVert 2) :=
    MonoidHom.ext hρ
  exact (congrArg MonoidHom.ker heq).symm.trans
    ((MonoidHom.ker_comp_of_injective s.projection ρ hf).trans s.projection_kernel)

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace SelectedSpan
variable {M₀ : Type*} [Group M₀] [Finite M₀] (R₀ : Subgroup M₀)
  (π : M₀ →* Equiv.Perm (Fin 6)) (K₀ : Subgroup M₀)
  (hres : pResidual 2 M₀ = K₀) (hcomp : K₀.map π = alternatingGroup (Fin 6))
include hres hcomp in
private theorem selected_moved_span_image (c : Vertex R₀)
    [IsElementaryAbelian 2 ((localZSpan R₀ c (alpha R₀))⧸center (localZSpan R₀ c (alpha R₀)))]
    (ρ : Equiv.Perm (Fin 6)→*MulAut ((localZSpan R₀ c (alpha R₀))⧸center (localZSpan R₀ c (alpha R₀))))
    (hρ : ∀m:M₀,ρ (π m)=forwardSpanCentralAction R₀ c m) :
    AddSubgroup.toZModSubmodule 2 (forwardMovedSpanProjection R₀ c).range.toAddSubgroup =
      subspaceCommutator (Offenders.linearize ρ) ⊤ (alternatingGroup (Fin 6)) := by
  let P := localZSpan R₀ c (alpha R₀)
  let q := QuotientGroup.mk' (center P)
  let S := subspaceCommutator (Offenders.linearize ρ) ⊤ (alternatingGroup (Fin 6))
  have hd (m:M₀) (z:P) : q (forwardSpanAction R₀ c m z/z)=ρ (π m) (q z)/q z := by
    rw [map_div,hρ,forwardSpanCentralAction_apply]
  have hbound : forwardMovedSpan R₀ c≤(S.toAddSubgroup.toSubgroup'.comap q).map P.subtype := by
    rw [forwardMovedSpan,commutator_comm]
    apply commutator_le.mpr
    intro l hl z hz
    rw [Ltilde_alpha,hres] at hl
    obtain ⟨m,hm,rfl⟩ := hl
    refine ⟨forwardSpanAction R₀ c m ⟨z,hz⟩/⟨z,hz⟩,?_,?_⟩
    · change Additive.ofMul (q (forwardSpanAction R₀ c m ⟨z,hz⟩/⟨z,hz⟩))∈S
      rw [hd]
      exact Submodule.subset_span ⟨π m,hcomp ▸ mem_map_of_mem π hm,
        Additive.ofMul (q ⟨z,hz⟩),Submodule.mem_top,rfl⟩
    · change embedM R₀ m*z*(embedM R₀ m)⁻¹/z=⁅embedM R₀ m,z⁆
      rw [div_eq_mul_inv,commutatorElement_def]
  apply le_antisymm
  · intro v hv
    change v.toMul∈(forwardMovedSpanProjection R₀ c).range at hv
    obtain ⟨x,hx⟩ := hv
    obtain ⟨z,hz,he⟩ := hbound x.property
    have he' : z=inclusion (forwardMovedSpan_le R₀ c) x := Subtype.ext he
    change Additive.ofMul (q z)∈S at hz
    rw [he'] at hz
    change Additive.ofMul ((forwardMovedSpanProjection R₀ c) x)∈S at hz
    rw [hx] at hz
    exact hz
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    rw [←hcomp] at ha
    obtain ⟨m,hm,rfl⟩ := ha
    obtain ⟨z,hz⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
    change ρ (π m) v.toMul/v.toMul∈(forwardMovedSpanProjection R₀ c).range
    rw [←hz]
    refine ⟨⟨⁅embedM R₀ m,(z:FreeAmalgam R₀)⁆,?_⟩,?_⟩
    · rw [forwardMovedSpan,commutator_comm]
      exact commutator_mem_commutator (by rw [Ltilde_alpha,hres];exact mem_map_of_mem (embedM R₀) hm) z.property
    · change q (⟨⁅embedM R₀ m,(z:FreeAmalgam R₀)⁆,_⟩:P)=_
      rw [←hd]
      apply congrArg q
      apply Subtype.ext
      change ⁅embedM R₀ m,(z:FreeAmalgam R₀)⁆=
        embedM R₀ m*(z:FreeAmalgam R₀)*(embedM R₀ m)⁻¹/(z:FreeAmalgam R₀)
      rw [div_eq_mul_inv,commutatorElement_def]

include hres hcomp in
private theorem selected_moved_span_fixed_kernel (c : Vertex R₀)
    [IsElementaryAbelian 2 ((localZSpan R₀ c (alpha R₀))⧸center (localZSpan R₀ c (alpha R₀)))]
    (ρ : Equiv.Perm (Fin 6)→*MulAut ((localZSpan R₀ c (alpha R₀))⧸center (localZSpan R₀ c (alpha R₀))))
    (hρ : ∀m:M₀,ρ (π m)=forwardSpanCentralAction R₀ c m)
    (hfixed : ⁅localZSpan R₀ c (alpha R₀),localZSpan R₀ c (alpha R₀)⁆≤
      centralizer (Ltilde R₀ (alpha R₀):Set (FreeAmalgam R₀))) :
    (fixedSpace (Offenders.linearize ρ) (alternatingGroup (Fin 6))).toAddSubgroup.toSubgroup'.comap
      (forwardMovedSpanProjection R₀ c)=center (forwardMovedSpan R₀ c) := by
  let P := localZSpan R₀ c (alpha R₀)
  let P₀ := forwardMovedSpan R₀ c
  let q := forwardMovedSpanProjection R₀ c
  let F := (fixedSpace (Offenders.linearize ρ) (alternatingGroup (Fin 6))).toAddSubgroup.toSubgroup'
  let K := F.comap q
  have hpoint (x:P₀) : q x∈F ↔
      ∀l∈Ltilde R₀ (alpha R₀),⁅l,(x:FreeAmalgam R₀)⁆∈centralizer (P:Set (FreeAmalgam R₀)) := by
    constructor
    · intro hx l hl
      rw [Ltilde_alpha,hres] at hl
      obtain ⟨m,hm,rfl⟩ := hl
      have hmA : π m∈alternatingGroup (Fin 6) :=
        hcomp ▸ mem_map_of_mem π hm
      have he := congrArg Additive.toMul (hx ⟨π m,hmA⟩)
      change ρ (π m) (q x)=q x at he
      rw [hρ] at he
      have he' : QuotientGroup.mk' (center P)
          (forwardSpanAction R₀ c m (inclusion (forwardMovedSpan_le R₀ c) x))=
          QuotientGroup.mk' (center P) (inclusion (forwardMovedSpan_le R₀ c) x) :=
        (forwardSpanCentralAction_apply R₀ c m _).symm.trans he
      have hz := QuotientGroup.eq_iff_div_mem.mp he'
      intro y hy
      have hh := congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
      change y*(embedM R₀ m*(x:FreeAmalgam R₀)*(embedM R₀ m)⁻¹/(x:FreeAmalgam R₀))=
        (embedM R₀ m*(x:FreeAmalgam R₀)*(embedM R₀ m)⁻¹/(x:FreeAmalgam R₀))*y at hh
      simpa only [div_eq_mul_inv,commutatorElement_def] using hh
    · intro hx a
      have ha : (a:Equiv.Perm (Fin 6))∈K₀.map π := hcomp.symm ▸ a.property
      obtain ⟨m,hm,he⟩ := ha
      apply Additive.toMul.injective
      change ρ a (q x)=q x
      rw [←he,hρ]
      change forwardSpanCentralAction R₀ c m
        (QuotientGroup.mk' (center P) (inclusion (forwardMovedSpan_le R₀ c) x))=_
      rw [forwardSpanCentralAction_apply]
      apply QuotientGroup.eq_iff_div_mem.mpr
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      have hh := hx (embedM R₀ m) (by
        rw [Ltilde_alpha,hres]
        exact mem_map_of_mem (embedM R₀) hm) y y.property
      change (y:FreeAmalgam R₀)*(embedM R₀ m*(x:FreeAmalgam R₀)*(embedM R₀ m)⁻¹/(x:FreeAmalgam R₀))=
        (embedM R₀ m*(x:FreeAmalgam R₀)*(embedM R₀ m)⁻¹/(x:FreeAmalgam R₀))*(y:FreeAmalgam R₀)
      simpa only [div_eq_mul_inv,commutatorElement_def] using hh
  have hKP : K.map P₀.subtype≤P := (map_subtype_le _).trans (forwardMovedSpan_le R₀ c)
  have hKL : ⁅K.map P₀.subtype,Ltilde R₀ (alpha R₀)⁆≤centralizer (P:Set (FreeAmalgam R₀)) := by
    rw [commutator_comm]
    apply commutator_le.mpr
    rintro l hl _ ⟨x,hx,rfl⟩
    exact (hpoint x).mp hx l hl
  have hKC : K.map P₀.subtype≤centralizer (P₀:Set (FreeAmalgam R₀)) :=
    (commutator_centralizes_iff_centralizes_moved P _ _ hKP hfixed).mp hKL
  have hAC : (center P₀).map P₀.subtype≤centralizer (P₀:Set (FreeAmalgam R₀)) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hAL : ⁅(center P₀).map P₀.subtype,Ltilde R₀ (alpha R₀)⁆≤centralizer (P:Set (FreeAmalgam R₀)) :=
    (commutator_centralizes_iff_centralizes_moved P _ _
      ((map_subtype_le _).trans (forwardMovedSpan_le R₀ c)) hfixed).mpr hAC
  ext x
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hKC (mem_map_of_mem P₀.subtype hx) y y.property)
  · intro hx
    apply (hpoint x).mpr
    intro l hl
    rw [commutator_comm] at hAL
    exact hAL (commutator_mem_commutator hl (mem_map_of_mem P₀.subtype hx))

include hres hcomp in
private theorem selected_moved_span_natural_coordinates_of_section (c : Vertex R₀)
    [IsElementaryAbelian 2 ((localZSpan R₀ c (alpha R₀))⧸center (localZSpan R₀ c (alpha R₀)))]
    (ρ : Equiv.Perm (Fin 6)→*MulAut ((localZSpan R₀ c (alpha R₀))⧸center (localZSpan R₀ c (alpha R₀))))
    (hρ : ∀m:M₀,ρ (π m)=forwardSpanCentralAction R₀ c m)
    (hfixed : ⁅localZSpan R₀ c (alpha R₀),localZSpan R₀ c (alpha R₀)⁆≤
      centralizer (Ltilde R₀ (alpha R₀):Set (FreeAmalgam R₀)))
    (sec : MovedSection (Offenders.linearize ρ) (alternatingGroup (Fin 6)))
    (hn : IsSymmetricNatural sec.action 6) :
    ∃ (e : ((forwardMovedSpan R₀ c)⧸center (forwardMovedSpan R₀ c))≃*
        Multiplicative (BinaryPermutation.natural (Fin 6))) (τ : Equiv.Perm (Fin 6)≃*Equiv.Perm (Fin 6)),
      ∀(m:M₀)(x:forwardMovedSpan R₀ c),
        (e (QuotientGroup.mk' (center (forwardMovedSpan R₀ c)) (forwardMovedSpanAction R₀ c m x))).toAdd=
          BinaryPermutation.naturalRepresentation (Fin 6) (τ (π m))
            (e (QuotientGroup.mk' (center (forwardMovedSpan R₀ c)) x)).toAdd := by
  obtain ⟨E⟩ := hn
  let P₀ := forwardMovedSpan R₀ c
  let q := forwardMovedSpanProjection R₀ c
  have himage : AddSubgroup.toZModSubmodule 2 q.range.toAddSubgroup=sec.space.toSubmodule :=
    (selected_moved_span_image R₀ π K₀ hres hcomp c ρ hρ).trans sec.space_eq.symm
  let r : Additive P₀→+sec.space.toSubmodule := {
    toFun := fun x => ⟨Additive.ofMul (q x.toMul),by
      rw [←himage]
      exact ⟨x.toMul,rfl⟩⟩
    map_zero' := by
      apply Subtype.ext
      exact congrArg Additive.ofMul (map_one q)
    map_add' := by
      intro x y
      apply Subtype.ext
      exact congrArg Additive.ofMul (map_mul q x.toMul y.toMul) }
  have hr : Function.Surjective r := by
    intro v
    have hv : v.val.toMul∈q.range := by
      change v.val∈AddSubgroup.toZModSubmodule 2 q.range.toAddSubgroup
      rw [himage]
      exact v.property
    obtain ⟨x,hx⟩ := hv
    exact ⟨Additive.ofMul x,Subtype.ext (congrArg Additive.ofMul hx)⟩
  let f : P₀→*Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    ((E.linearEquiv.toLinearMap.comp sec.central.toSubmodule.mkQ).toAddMonoidHom.comp r).toMultiplicativeRight
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨x,hx⟩ := E.linearEquiv.surjective.comp
      (sec.central.toSubmodule.mkQ_surjective.comp hr) v.toAdd
    exact ⟨x.toMul,congrArg Multiplicative.ofAdd hx⟩
  have hk : f.ker=center P₀ := by
    ext x
    change E.linearEquiv (sec.central.toSubmodule.mkQ (r (Additive.ofMul x)))=0 ↔ x∈center P₀
    rw [E.linearEquiv.map_eq_zero_iff,←LinearMap.mem_ker,Submodule.ker_mkQ,sec.central_eq]
    rw [←selected_moved_span_fixed_kernel R₀ π K₀ hres hcomp c ρ hρ hfixed]
    change (∀a:alternatingGroup (Fin 6),sec.space.toRepresentation a (r (Additive.ofMul x))=
      r (Additive.ofMul x)) ↔
        ∀a:alternatingGroup (Fin 6),Offenders.linearize ρ a (Additive.ofMul (q x))=Additive.ofMul (q x)
    constructor
    · intro hx a
      exact congrArg Subtype.val (hx a)
    · intro hx a
      exact Subtype.ext (hx a)
  let e : (P₀⧸center P₀)≃*Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (x:P₀) : e (QuotientGroup.mk' (center P₀) x)=f x := rfl
  have hract (m:M₀) (x:P₀) : r (Additive.ofMul (forwardMovedSpanAction R₀ c m x))=
      sec.space.toRepresentation (π m) (r (Additive.ofMul x)) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    change q (forwardMovedSpanAction R₀ c m x)=ρ (π m) (q x)
    rw [hρ]
    change QuotientGroup.mk' (center (localZSpan R₀ c (alpha R₀)))
        (inclusion (forwardMovedSpan_le R₀ c) (forwardMovedSpanAction R₀ c m x))=
      forwardSpanCentralAction R₀ c m
        (QuotientGroup.mk' (center (localZSpan R₀ c (alpha R₀))) (inclusion (forwardMovedSpan_le R₀ c) x))
    rw [forwardSpanCentralAction_apply]
    rfl
  refine ⟨e,E.groupEquiv,?_⟩
  intro m x
  rw [he,he]
  change E.linearEquiv (sec.central.toSubmodule.mkQ (r (Additive.ofMul (forwardMovedSpanAction R₀ c m x))))=_
  rw [hract,←sec.central.quotientRepresentation_mk]
  exact E.intertwines (π m) _

end SelectedSpan

private theorem linearized_cyclic_codim_eq_one
    {Y : Type*} [Group Y] [Finite Y] [IsElementaryAbelian 2 Y]
    {D : Type*} [Group D] (ρ : D→*MulAut Y) (hf : Function.Injective ρ)
    (a : D) (ha : a≠1) (hi : (ρ a).fixedSubgroup.index≤2) :
    fixedCodim (Offenders.linearize ρ) (zpowers a)=1 := by
  let σ := Offenders.linearize ρ
  change fixedCodim σ (zpowers a)=1
  let e : fixedSpace σ (zpowers a) ≃ (ρ a).fixedSubgroup := {
    toFun := fun v => ⟨v.val.toMul, (MulAut.mem_fixedSubgroup _ _).mpr
      (congrArg Additive.toMul ((mem_fixedSpace_zpowers_iff σ a v.val).mp v.property))⟩
    invFun := fun v => ⟨Additive.ofMul v.val,(mem_fixedSpace_zpowers_iff σ a _).mpr
      (congrArg Additive.ofMul ((MulAut.mem_fixedSubgroup _ _).mp v.property))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Nat.card Y≤Nat.card ((ρ a).fixedSubgroup)*2 := by
    rw [←(ρ a).fixedSubgroup.card_mul_index]
    exact Nat.mul_le_mul_left _ hi
  rw [←Nat.card_congr e] at hcard
  change Nat.card (Additive Y)≤_ at hcard
  have hV := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive Y)
  have hF := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=fixedSpace σ (zpowers a))
  rw [Nat.card_zmod] at hV hF
  rw [hV,hF] at hcard
  have hd : Module.finrank (ZMod 2) (Additive Y)≤
      Module.finrank (ZMod 2) (fixedSpace σ (zpowers a))+1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    simpa only [pow_succ] using hcard
  have hne : zpowers a≠⊥ := fun he => ha (mem_bot.mp (he ▸ mem_zpowers a))
  have hp := fixedCodim_pos_of_faithful σ (Offenders.linearize_injective ρ hf) hne
  have hs := fixedCodim_add_finrank σ (zpowers a)
  omega


/-- Odd-transvection recognition on the literal selected central quotient.
The nonabelian selected span and the fixed-index bound must still come from
one coordinated source path. -/
theorem selected_span_moved_section_natural
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6)))
    (a : Equiv.Perm (Fin 6)) (ha : a.IsSwap)
    (hd : (cosetGraph d.radical).dist (p.walk.getVert 2) (alpha d.radical) ≤ 2)
    (hi : (selectedSpanSymmetricAction s hc hb (p.walk.getVert 2) hd a).fixedSubgroup.index ≤ 2) :
    let hEA := selected_span_central_quotient_elementary s hc hb (p.walk.getVert 2) hd
    let ρ := selectedSpanSymmetricAction s hc hb (p.walk.getVert 2) hd
    let := hEA
    ∃ sectionData : MovedSection (Offenders.linearize ρ) (alternatingGroup (Fin 6)),
      IsSymmetricNatural sectionData.action 6 := by
  let hEA := selected_span_central_quotient_elementary s hc hb (p.walk.getVert 2) hd
  let := hEA
  let ρ := selectedSpanSymmetricAction s hc hb (p.walk.getVert 2) hd
  have hf : Function.Injective ρ := selected_span_symmetric_action_injective s hb p hnonabelian ρ
    (selectedSpanSymmetricAction_projection s hc hb (p.walk.getVert 2) hd)
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical hd).trans ((replacementGeometry h d).V_local _ rfl hb)
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hcard : Nat.card (zpowers a) = 2 := by rw [Nat.card_zpowers,ha.orderOf]
  let : IsElementaryAbelian 2 (zpowers a) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      simpa only [hcard] using pow_card_eq_one' (x:=x)) }
  apply SourceCompletion.symmetricSix_moved_section_natural_of_odd_transvection
    (Offenders.linearize ρ) (Offenders.linearize_injective ρ hf) hsq
    (zpowers a) hcard
    (linearized_cyclic_codim_eq_one ρ hf a (by intro he; have ho := ha.orderOf; rw [he,orderOf_one] at ho; omega) hi)
  intro hle
  have hsign := (Equiv.Perm.mem_alternatingGroup.mp (hle (mem_zpowers a)))
  rw [ha.sign_eq] at hsign
  exact (by decide : (-1 : Units ℤ) ≠ 1) hsign


/-- Combining recognition with the literal fixed-kernel calculation produces
an actual quotient of the component-moved selected span. -/
theorem selected_moved_span_natural_coordinates
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6)))
    (a : Equiv.Perm (Fin 6)) (ha : a.IsSwap)
    (hd : (cosetGraph d.radical).dist (p.walk.getVert 2) (alpha d.radical) ≤ 2)
    (hi : (selectedSpanSymmetricAction s hc hb (p.walk.getVert 2) hd a).fixedSubgroup.index ≤ 2) :
    ∃ (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
          center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
        Multiplicative (BinaryPermutation.natural (Fin 6)))
      (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6)),
      ∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
        (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))
            (E (QuotientGroup.mk' _ x)).toAdd := by
  let hEA := selected_span_central_quotient_elementary s hc hb (p.walk.getVert 2) hd
  let := hEA
  let ρ := selectedSpanSymmetricAction s hc hb (p.walk.getVert 2) hd
  obtain ⟨sec,hnat⟩ := selected_span_moved_section_natural s hc hb p hnonabelian hsq a ha hd hi
  exact SelectedSpan.selected_moved_span_natural_coordinates_of_section d.radical s.projection
    (replacementComponent d) (replacement_residual h d) s.component_image (p.walk.getVert 2) ρ
    (selectedSpanSymmetricAction_projection s hc hb (p.walk.getVert 2) hd) hfixed sec hnat

include s in
/-- A critical conjugate of the selected seed lies in the same normal span,
so its genuine critical commutator proves that span nonabelian. -/
theorem selected_span_nonabelian_of_conjugate_critical
    (hc : DistanceTwo.CentralLayer d) (c : Vertex d.radical)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical (alpha d.radical))
    (q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical x c)) :
    ⁅localZSpan d.radical c (alpha d.radical),localZSpan d.radical c (alpha d.radical)⁆ ≠ ⊥ := by
  let P := localZSpan d.radical c (alpha d.radical)
  have hcP : Z d.radical c ≤ P := Z_le_localZSpan d.radical _ _
  have hxP : Z d.radical (act d.radical x c) ≤ P := by
    rw [Z_act]
    exact (map_mono hcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized d.radical c (alpha d.radical)
        ((stabilizer d.radical (alpha d.radical)).inv_mem hx)))
  intro hz
  have hcrit := critical_noncommutation d.radical (replacementGeometry h d)
    (edgeCentralizerCondition s hc) c q.start_color
    (by rw [(replacementGeometry h d).distance_constant c q.start_color];
        exact replacementDistance_pos h d) q.critical
  exact hcrit (le_bot_iff.mp ((commutator_mono hcP hxP).trans_eq hz))

include s in
/-- A central commutator on the index-two predecessor intersection gives
fixed index at most two on the actual selected central quotient. -/
theorem selected_span_endpoint_fixed_index
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hd : (cosetGraph d.radical).dist (p.walk.getVert 2) (alpha d.radical) ≤ 2)
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2), Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical))
    (m : d.overgroup) (hm : embedM d.radical m ∈ Z d.radical a') :
    (selectedSpanSymmetricAction s hc hb (p.walk.getVert 2) hd (s.projection m)).fixedSubgroup.index ≤ 2 := by
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  let C := Q d.radical (p.walk.getVert 2)
  let q : P →* P ⧸ center P := QuotientGroup.mk' (center P)
  have hPQ : P ≤ Q d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical hd).trans
      (V_le_Q d.radical (geometry := replacementGeometry h d) rfl hb)
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) := hPQ.trans (by intro x hx; exact hx.1)
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hZaC : Z d.radical (alpha d.radical) ≤ centralizer (P : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical _ rfl)).trans
      (centralizer_le hPQ)
  have hfix : (C.subgroupOf P).map q ≤
      (selectedSpanSymmetricAction s hc hb (p.walk.getVert 2) hd (s.projection m)).fixedSubgroup := by
    rintro _ ⟨x,hx,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [selectedSpanSymmetricAction_projection,forwardSpanCentralAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hz : ⁅embedM d.radical m,(x:FreeAmalgam d.radical)⁆ ∈ Z d.radical (alpha d.radical) := by
      apply hcomm
      rw [commutator_comm]
      exact commutator_mem_commutator hm ⟨x.property,hx⟩
    change (y:FreeAmalgam d.radical)*(embedM d.radical m*(x:FreeAmalgam d.radical)*(embedM d.radical m)⁻¹/(x:FreeAmalgam d.radical)) =
      (embedM d.radical m*(x:FreeAmalgam d.radical)*(embedM d.radical m)⁻¹/(x:FreeAmalgam d.radical))*(y:FreeAmalgam d.radical)
    simpa only [div_eq_mul_inv,commutatorElement_def] using hZaC hz y y.property
  have hi : ((C.subgroupOf P).map q).index ≤ C.relIndex P := Nat.le_of_dvd
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    ((C.subgroupOf P).index_map_dvd (QuotientGroup.mk'_surjective (center P)))
  exact (index_antitone hfix).trans (hi.trans hindex)

include s in
private theorem selected_alternating_sqtk
    (hsq : IsSQTK KnownSimple.IsKnownSimple d.overgroup) :
    IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6)) := by
  have hquot : IsSQTK KnownSimple.IsKnownSimple (d.overgroup ⧸ pCore 2 d.overgroup) := by
    refine ⟨?_,hsq.isKGroup.quotient (pCore 2 d.overgroup)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 d.overgroup) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  let E : (d.overgroup ⧸ pCore 2 d.overgroup) ≃* Equiv.Perm (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq s.projection_kernel.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective s.projection s.surjective)
  exact (IsSQTK.knownSimple_of_equiv E hquot).subgroup (alternatingGroup (Fin 6))

include s in
/-- Recognition and quotient transport on a single critical path. The
remaining premises are the selected-span estimates of source (5.12). -/
theorem selected_natural_quotient_of_path_estimates
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (hsq : IsSQTK KnownSimple.IsKnownSimple d.overgroup)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2), Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ∃ (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
          center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
        Multiplicative (BinaryPermutation.natural (Fin 6)))
      (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6)),
      ∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
        (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))
            (E (QuotientGroup.mk' _ x)).toAdd := by
  have hd : (cosetGraph d.radical).dist (p.walk.getVert 2) (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)]
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  obtain ⟨m,hm,rfl⟩ := ha
  exact selected_moved_span_natural_coordinates s hc hb p hnonabelian hfixed
    (selected_alternating_sqtk s hsq) _ hswap hd
    (selected_span_endpoint_fixed_index s hc hb p hd hindex hcomm m hm)

include h in
private theorem selected_span_le_core
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤ Q d.radical (alpha d.radical) := by
  apply (localZSpan_le_V d.radical _).trans
    (V_le_Q d.radical (geometry := replacementGeometry h d) rfl hb)
  rw [SimpleGraph.dist_comm,p.dist_start (by have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)]

include s in
/-- The actual critical endpoint moves the selected natural central quotient.
Its commutator cannot be absorbed by the original starting seed, including
when that seed retains the central line of the order-thirty-two cover. -/
theorem selected_moved_span_endpoint_commutator_not_le_seed
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
        center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6))
    (hE : ∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
      (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))
          (E (QuotientGroup.mk' _ x)).toAdd) :
    ¬ ⁅forwardMovedSpan d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤
      Z d.radical (alpha d.radical) := by
  let c := p.walk.getVert 2
  let P₀ := forwardMovedSpan d.radical c
  have hPQ : P₀≤Q d.radical (alpha d.radical) := (forwardMovedSpan_le d.radical c).trans
    (selected_span_le_core hb p)
  have hUC : Z d.radical (alpha d.radical)≤centralizer (P₀:Set (FreeAmalgam d.radical)) :=
    ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical (alpha d.radical) rfl)).trans
        (centralizer_le hPQ))
  have hr := critical_reverse_pair s hc p
  have hnot : ¬ ((Z d.radical a').comap (embedM d.radical)).map s.projection = ⊥ := by
    intro he
    have hh := (Subgroup.map_eq_bot_iff _).mp he
    rw [s.projection_kernel] at hh
    have hm := map_mono (f := embedM d.radical) hh
    have hZe : ((Z d.radical a').comap (embedM d.radical)).map (embedM d.radical) = Z d.radical a' :=
      map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
        (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
    rw [hZe,←Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hm
    exact hr.2 hm
  obtain ⟨a,ha,hne⟩ := (((Z d.radical a').comap (embedM d.radical)).map s.projection).bot_or_exists_ne_one.resolve_left hnot
  obtain ⟨m,hm,rfl⟩ := ha
  have hn : s.projection m ≠ 1 := hne
  intro hcomm
  have hfixed (x:P₀) : QuotientGroup.mk' (center P₀) (forwardMovedSpanAction d.radical c m x)=
      QuotientGroup.mk' (center P₀) x := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hh := hUC (hcomm (by
      rw [commutator_comm]
      exact commutator_mem_commutator hm x.property)) y y.property
    change (y:FreeAmalgam d.radical)*(embedM d.radical m*(x:FreeAmalgam d.radical)*(embedM d.radical m)⁻¹/(x:FreeAmalgam d.radical))=
      (embedM d.radical m*(x:FreeAmalgam d.radical)*(embedM d.radical m)⁻¹/(x:FreeAmalgam d.radical))*(y:FreeAmalgam d.radical)
    simpa only [div_eq_mul_inv,commutatorElement_def] using hh
  have hrep : BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))=1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨z,hz⟩ := E.surjective (Multiplicative.ofAdd v)
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (center P₀) z
    have hv : (E (QuotientGroup.mk' (center P₀) x)).toAdd=v := by rw [hx,hz]; rfl
    have he := hE m x
    rw [hfixed] at he
    change BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m)) v=v
    rw [←hv]
    exact he.symm
  have ht : τ (s.projection m)=1 :=
    (BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide))
      (hrep.trans (map_one (BinaryPermutation.naturalRepresentation (Fin 6))).symm)
  exact hn (τ.injective (ht.trans τ.map_one.symm))

omit [Finite G] in
private theorem selected_normalized_comap_normal (J : Subgroup (FreeAmalgam d.radical))
    (hJ : stabilizer d.radical (alpha d.radical)≤normalizer (J:Set (FreeAmalgam d.radical))) :
    (J.comap (embedM d.radical)).Normal := by
  constructor
  intro n hn g
  change embedM d.radical (g*n*g⁻¹)∈J
  rw [map_mul,map_mul,map_inv]
  exact (le_normalizer_iff.mp hJ (embedM d.radical g)
    (by change embedM d.radical g∈stabilizer d.radical (mVertex d.radical 1); rw [stabilizer_m_base]; exact ⟨g,rfl⟩)) _ hn


include s in
/-- The source index-two action contracts the actual core commutator into
the starting seed and the selected moved span. The natural quotient is
constructed earlier; it supplies the escape needed by the residual argument. -/
theorem selected_core_commutator_le_seed_sup_moved_span
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
        center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6))
    (hE : ∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
      (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))
          (E (QuotientGroup.mk' _ x)).toAdd)
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2)
    (hactor : ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤
      Z d.radical (alpha d.radical) ⊔ forwardMovedSpan d.radical (p.walk.getVert 2) := by
  let c := p.walk.getVert 2
  let Q₀ := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
  let P₀ := forwardMovedSpan d.radical c
  let D := Q₀⊓Q d.radical c
  let f := embedM d.radical
  let Qm := ⁅pCore 2 d.overgroup,pResidual 2 d.overgroup⁆
  let Um := (Z d.radical (alpha d.radical)).comap f
  let Wm := P₀.comap f
  let Dm := D.comap f
  let Am := (Z d.radical a').comap f
  have hQf : Qm.map f=Q₀ := by
    dsimp only [Qm,Q₀,f]
    rw [map_commutator,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←Ltilde_alpha]
  have hGa : stabilizer d.radical (alpha d.radical)=f.range := stabilizer_m_base d.radical
  have hQGa : Q d.radical (alpha d.radical)≤stabilizer d.radical (alpha d.radical) := fun _ hx => hx.1
  have hPQ : P₀≤Q d.radical (alpha d.radical) := (forwardMovedSpan_le d.radical c).trans
    (selected_span_le_core hb p)
  have hP₀Q₀ : P₀≤Q₀ := commutator_mono
    (selected_span_le_core hb p) le_rfl
  have hPf : Wm.map f=P₀ := map_comap_eq_self (hPQ.trans (hQGa.trans_eq hGa))
  have hUf : Um.map f=Z d.radical (alpha d.radical) := map_comap_eq_self
    ((Z_le_stabilizer d.radical _).trans_eq hGa)
  have hQ₀Ga : Q₀≤stabilizer d.radical (alpha d.radical) :=
    (le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (Q_normalized d.radical _))).trans hQGa
  have hDf : Dm.map f=D := map_comap_eq_self (inf_le_left.trans (hQ₀Ga.trans_eq hGa))
  have hAf : Am.map f=Z d.radical a' := map_comap_eq_self
    ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq hGa)
  have hQm : Q₀.comap f=Qm := by
    rw [←hQf,comap_map_eq_self_of_injective (embedM_injective d.radical)]
  let : Um.Normal := selected_normalized_comap_normal _ (Z_normalized d.radical _)
  let : Wm.Normal := selected_normalized_comap_normal _ (forwardMovedSpan_normalized d.radical _)
  have hWQ : Wm≤Qm := by rw [←hQm]; exact comap_mono hP₀Q₀
  have hDQ : Dm≤Qm := by rw [←hQm]; exact comap_mono inf_le_left
  have hi : Dm.relIndex Qm≤2 := by
    rw [relIndex_comap,hQf]
    simpa only [D,inf_relIndex_left] using hindex
  have hmove : ⁅Qm,pResidual 2 d.overgroup⁆=Qm :=
    commutator_isPPerfect_idempotent _ _ (isPPerfect_pResidual 2) pCore_isPGroup le_normalizer_of_normal
  have hDA : ⁅Dm,Am⁆≤Um := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hDf,hAf]
    exact hactor
  have hnot : ¬Wm≤Dm := by
    intro he
    have hPD : P₀≤D := by rw [←hPf,←hDf]; exact map_mono he
    exact selected_moved_span_endpoint_commutator_not_le_seed s hc hb p E τ hE
      ((commutator_mono hPD le_rfl).trans hactor)
  obtain ⟨t,ht,hswap⟩ := small_critical_image_swap s hc p hsmall
  have hodd : ¬ Am.map s.projection ≤ alternatingGroup (Fin 6) := by
    intro hh
    have hs := Equiv.Perm.mem_alternatingGroup.mp (hh ht)
    rw [hswap.sign_eq] at hs
    exact (by decide : (-1 : Units ℤ) ≠ 1) hs
  have hresult := residual_moved_le_of_symmetricSix_odd_small_index s.projection
    s.surjective
    (by rw [s.projection_kernel]; exact pCore_isPGroup)
    Qm Um Wm Dm Am hWQ hDQ hi hmove hDA hnot
    hodd
  have hh := map_mono (f:=f) hresult
  rwa [hQf,Subgroup.map_sup,hUf,hPf] at hh

include h in
/-- A central starting seed contributes no derived subgroup to the core
supplement. Thus the core and the selected moved span have the same literal
ambient derived subgroup. -/
theorem selected_core_derived_eq_of_supplement
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsupp : ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤
      Z d.radical (alpha d.radical) ⊔ forwardMovedSpan d.radical (p.walk.getVert 2)) :
    ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆,
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆⁆ =
      ⁅forwardMovedSpan d.radical (p.walk.getVert 2),
        forwardMovedSpan d.radical (p.walk.getVert 2)⁆ := by
  let A := Z d.radical (alpha d.radical)
  let W := forwardMovedSpan d.radical (p.walk.getVert 2)
  let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
  let J := stabilizer d.radical (alpha d.radical)
  have hCQ : C ≤ Q d.radical (alpha d.radical) :=
    le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (Q_normalized d.radical _))
  have hWQ : W ≤ Q d.radical (alpha d.radical) :=
    (forwardMovedSpan_le d.radical _).trans (selected_span_le_core hb p)
  have hWC : W ≤ C := commutator_mono (selected_span_le_core hb p) le_rfl
  have hAC : A ≤ centralizer (C : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical _ rfl)).trans
      (centralizer_le hCQ)
  have hAW : A ≤ centralizer (W : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical _ rfl)).trans
      (centralizer_le hWQ)
  have hJN : J ≤ normalizer ((⁅W,W⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (forwardMovedSpan_normalized d.radical _ hg)]
  have hAJ : A ≤ J := Z_le_stabilizer d.radical _
  have hWJ : W ≤ J := hWQ.trans (fun _ hx => hx.1)
  have hWCW : ⁅W,C⁆ ≤ ⁅W,W⁆ := by
    rw [commutator_comm]
    apply (commutator_mono hsupp le_rfl).trans
    exact commutator_sup_le_of_relative_normal J A W W ⁅W,W⁆ hJN hAJ hWJ
      ((commutator_eq_bot_iff_le_centralizer.mpr hAW).le.trans bot_le) le_rfl
  apply le_antisymm _ (commutator_mono hWC hWC)
  apply (commutator_mono hsupp le_rfl).trans
  exact commutator_sup_le_of_relative_normal J A W C ⁅W,W⁆ hJN hAJ hWJ
    ((commutator_eq_bot_iff_le_centralizer.mpr hAC).le.trans bot_le) hWCW


include s in
/-- The natural quotient of the selected moved span determines its central
index and derived line, and every index-two subgroup retains that same line. -/
theorem selected_moved_span_derived_transfer
    (hb : 2 < replacementDistance h d) (c : Vertex d.radical)
    (hd : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2)
    (hfixed : ⁅localZSpan d.radical c (alpha d.radical),localZSpan d.radical c (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (E : ((forwardMovedSpan d.radical c) ⧸ center (forwardMovedSpan d.radical c)) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6))
    (hequiv : ∀ (m : d.overgroup) (x : forwardMovedSpan d.radical c),
      (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical c m x))).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))
          (E (QuotientGroup.mk' _ x)).toAdd) :
    (center (forwardMovedSpan d.radical c)).index = 16 ∧
    Nat.card (⁅forwardMovedSpan d.radical c,forwardMovedSpan d.radical c⁆ :
      Subgroup (FreeAmalgam d.radical)) = 2 ∧
    ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ forwardMovedSpan d.radical c →
      A.relIndex (forwardMovedSpan d.radical c) ≤ 2 →
      ⁅A,A⁆ = ⁅forwardMovedSpan d.radical c,forwardMovedSpan d.radical c⁆ := by
  let P := forwardMovedSpan d.radical c
  let q : P →* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    E.toMonoidHom.comp (QuotientGroup.mk' (center P))
  have hq : Function.Surjective q := E.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center P := by
    ext x
    change E (QuotientGroup.mk' (center P) x) = 1 ↔ x ∈ center P
    rw [E.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hci : (center P).index = 16 := by
    rw [index_eq_card,Nat.card_congr E.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    rfl
  have hcent : _root_.commutator P ≤ center P := by
    rw [←hk]
    apply commutator_le.mpr
    intro x _ y _
    rw [MonoidHom.mem_ker,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hne : _root_.commutator P ≠ ⊥ := by
    intro hz
    have he := (_root_.commutator_eq_bot_iff_center_eq_top P).mp hz
    rw [he,index_top] at hci
    omega
  let π := (τ.toMonoidHom.comp s.projection).comp (replacementComponent d).subtype
  have hπ : alternatingGroup (Fin 6) ≤ π.range := by
    dsimp only [π]
    rw [MonoidHom.range_comp,(replacementComponent d).range_subtype,
      ←Subgroup.map_map,s.component_image,characteristic_iff_map_eq.mp inferInstance τ]
  let ρ := (forwardMovedSpanAction d.radical c).comp (replacementComponent d).subtype
  have hc : Nat.card (_root_.commutator P) ≤ 2 :=
    BinaryPermutation.SixCentralDerived.card_derived_le_two q hq hk.le ρ π hπ
      (fun m x => hequiv m x) (by
        intro m _ z hz
        apply Subtype.ext
        have hzP : (z : FreeAmalgam d.radical) ∈ ⁅P,P⁆ := by
          rw [←P.map_subtype_commutator]
          exact mem_map_of_mem P.subtype hz
        have hzm := hfixed ((commutator_mono (forwardMovedSpan_le d.radical c)
          (forwardMovedSpan_le d.radical c)) hzP)
        have hm : embedM d.radical (m : d.overgroup) ∈ Ltilde d.radical (alpha d.radical) := by
          rw [Ltilde_alpha,replacement_residual h d]
          exact mem_map_of_mem (embedM d.radical) m.property
        change embedM d.radical (m : d.overgroup) * (z : FreeAmalgam d.radical) *
          (embedM d.radical (m : d.overgroup))⁻¹ = (z : FreeAmalgam d.radical)
        rw [hzm _ hm,mul_inv_cancel_right])
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    ((forwardMovedSpan_le d.radical c).trans (localZSpan_le_V d.radical hd)).trans
      ((replacementGeometry h d).V_local _ rfl hb)
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hlow := (one_lt_card_iff_ne_bot (_root_.commutator P)).mpr hne
  have hcard : Nat.card (_root_.commutator P) = 2 := by omega
  have hgraph : Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
    rw [←P.map_subtype_commutator,card_map_of_injective P.subtype_injective]
    exact hcard
  refine ⟨hci,hgraph,?_⟩
  intro A hA hi
  have ht := ClassTwo.commutator_eq_of_index_le_two_of_center_index_gt_four
    hcent hcard (by omega) (A.subgroupOf P) hi
  have hm := congrArg (Subgroup.map P.subtype) ht
  rwa [map_commutator,map_subgroupOf_eq_of_le hA,P.map_subtype_commutator] at hm


include s in
/-- The endpoint action and the selected natural quotient identify the full
core's derived line and preserve it through each index-two subgroup. All
indices and commutators use the same original path and quotient marking. -/
theorem selected_core_derived_transfer
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
        center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6))
    (hE : ∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
      (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))
          (E (QuotientGroup.mk' _ x)).toAdd)
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2)
    (hactor : ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
    C ≤ Z d.radical (alpha d.radical) ⊔ forwardMovedSpan d.radical (p.walk.getVert 2) ∧
      Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ C → A.relIndex C ≤ 2 → ⁅A,A⁆ = ⁅C,C⁆ := by
  let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
  let W := forwardMovedSpan d.radical (p.walk.getVert 2)
  have hsupp := selected_core_commutator_le_seed_sup_moved_span s hc hb p hsmall E τ hE hindex hactor
  have heq := selected_core_derived_eq_of_supplement hb p hsupp
  have hd : (cosetGraph d.radical).dist (p.walk.getVert 2) (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)]
  have ht := selected_moved_span_derived_transfer s hb (p.walk.getVert 2) hd hfixed E τ hE
  have hWQ : W ≤ Q d.radical (alpha d.radical) :=
    (forwardMovedSpan_le d.radical _).trans (selected_span_le_core hb p)
  have hWC : W ≤ C := commutator_mono (selected_span_le_core hb p) le_rfl
  have hCQ : C ≤ Q d.radical (alpha d.radical) :=
    le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (Q_normalized d.radical _))
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite W := Finite.of_injective (inclusion (hWQ.trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion (hCQ.trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  refine ⟨hsupp,by rw [heq]; exact ht.2.1,?_⟩
  intro A hA hi
  have hiW : (A ⊓ W).relIndex W ≤ 2 := by
    rw [inf_relIndex_right]
    exact (relIndex_le_of_le_right hWC index_ne_zero_of_finite).trans hi
  have hsmallDer : ⁅A ⊓ W,A ⊓ W⁆ = ⁅C,C⁆ :=
    (ht.2.2 (A ⊓ W) inf_le_right hiW).trans heq.symm
  apply le_antisymm (commutator_mono hA hA)
  rw [←hsmallDer]
  exact commutator_mono inf_le_left inf_le_left



include h in
private theorem selected_span_eq_seed_sup_moved
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) =
      Z d.radical (p.walk.getVert 2) ⊔ forwardMovedSpan d.radical (p.walk.getVert 2) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan d.radical c (alpha d.radical)
  let P₀ := forwardMovedSpan d.radical c
  let B := Z d.radical c ⊔ P₀
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent d.radical c t :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hBP : B ≤ P := sup_le (Z_le_localZSpan d.radical _ _) (forwardMovedSpan_le d.radical _)
  have hLB : Ltilde d.radical (alpha d.radical) ≤ normalizer (B : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hBP le_rfl).trans (show P₀ ≤ B from le_sup_right))
  have hQtG : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hQtGc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hQtB : Q d.radical t ≤ normalizer (B : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQtGc.trans (Z_normalized d.radical c))
      (hQtG.trans (forwardMovedSpan_normalized d.radical c))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hGB : stabilizer d.radical (alpha d.radical) ≤ normalizer (B : Set (FreeAmalgam d.radical)) := by
    rw [←selected_residual_edge_generation (h := h) rfl hat]
    exact sup_le hLB hQtB
  apply le_antisymm _ hBP
  dsimp only [P]
  rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro g
  rintro _ ⟨z,hz,rfl⟩
  exact (mem_normalizer_iff.mp (hGB ((stabilizer d.radical (alpha d.radical)).inv_mem g.property)) z).mp
    ((show Z d.radical c ≤ B from le_sup_left) hz)

include h in
private theorem selected_moved_span_idempotent
    (hb : 2 < replacementDistance h d) (c : Vertex d.radical)
    (hd : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2) :
    ⁅forwardMovedSpan d.radical c,Ltilde d.radical (alpha d.radical)⁆ = forwardMovedSpan d.radical c := by
  let P := localZSpan d.radical c (alpha d.radical)
  let W := P.comap (embedM d.radical)
  have hPQ : P ≤ Q d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical hd).trans (V_le_Q d.radical (geometry := replacementGeometry h d) rfl hb)
  have hPG : P ≤ (embedM d.radical).range :=
    (hPQ.trans (fun _ hx => hx.1)).trans_eq (stabilizer_m_base d.radical)
  have hmW : W.map (embedM d.radical) = P := map_comap_eq_self hPG
  let : W.Normal := by
    refine ⟨?_⟩
    intro x hx g
    change embedM d.radical (g*x*g⁻¹) ∈ P
    rw [map_mul,map_mul,map_inv]
    apply le_normalizer_iff.mp (localZSpan_normalized d.radical c (alpha d.radical))
    · change embedM d.radical g ∈ stabilizer d.radical (mVertex d.radical 1)
      rw [stabilizer_m_base]
      exact ⟨g,rfl⟩
    · exact hx
  have hWQ : W ≤ pCore 2 d.overgroup := by
    intro x hx
    have hxQ := hPQ hx
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at hxQ
    obtain ⟨y,hy,he⟩ := hxQ
    exact (embedM_injective d.radical he) ▸ hy
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hres : pResidual 2 d.overgroup = replacementComponent d := replacement_residual h d
  have hK : IsPPerfect 2 (replacementComponent d) :=
    hres ▸ isPPerfect_pResidual 2
  have hi := commutator_isPPerfect_idempotent (replacementComponent d) W hK
    (pCore_isPGroup.to_le hWQ) le_normalizer_of_normal
  have hm := congrArg (Subgroup.map (embedM d.radical)) hi
  rw [map_commutator,map_commutator,hmW,←hres,←Ltilde_alpha] at hm
  exact hm

include h in
/-- The component-moved selected span retains the entire original derived
subgroup. Coprime generation makes its residual action idempotent; the
three-subgroups lemma controls the cross commutator with the seed. -/
theorem selected_span_derived_eq_moved
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ =
    ⁅forwardMovedSpan d.radical (p.walk.getVert 2),forwardMovedSpan d.radical (p.walk.getVert 2)⁆ := by
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  let P₀ := forwardMovedSpan d.radical c
  let J := stabilizer d.radical (alpha d.radical)
  let C := ⁅P₀,P₀⁆
  have hd : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)]
  have hP₀P : P₀ ≤ P := forwardMovedSpan_le d.radical c
  have hPG : P ≤ J := (localZSpan_le_V d.radical hd).trans
    ((replacementGeometry h d).V_local _ rfl hb)
  have hSG : Z d.radical c ≤ J := (Z_le_localZSpan d.radical _ _).trans hPG
  have hNG : J ≤ normalizer (C : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅P₀,P₀⁆).map (MulAut.conj g).toMonoidHom = _
    have hn : P₀.map (MulAut.conj g).toMonoidHom = P₀ :=
      mem_normalizer_iff_map_conj_eq.mp (forwardMovedSpan_normalized d.radical c hg)
    rw [map_commutator,hn]
  have hcross : ⁅P₀,P⁆ ≤ C := by
    have hi : ⁅P₀,Ltilde d.radical (alpha d.radical)⁆ = P₀ :=
      selected_moved_span_idempotent (h := h) hb c hd
    conv_lhs => rw [←hi]
    apply commutator_commutator_le_of_rotate_of_le_normalizer
      ((hP₀P.trans hPG).trans hNG) ((Ltilde_le_stabilizer _).trans hNG) (hPG.trans hNG)
    · rw [commutator_comm (Ltilde d.radical (alpha d.radical))]
      exact le_rfl
    · have hz : ⁅⁅P,P₀⁆,Ltilde d.radical (alpha d.radical)⁆ = ⊥ :=
        commutator_eq_bot_iff_le_centralizer.mpr ((commutator_mono le_rfl hP₀P).trans hfixed)
      exact hz.le.trans bot_le
  have hgen : P = Z d.radical c ⊔ P₀ := selected_span_eq_seed_sup_moved (h := h) hb p
  have hSP : ⁅Z d.radical c,P⁆ ≤ C := by
    rw [hgen,commutator_comm]
    apply commutator_sup_le_of_relative_normal J _ _ _ C hNG hSG (hP₀P.trans hPG)
    · have hc : color d.radical c = false :=
        (p.vertex_color (by have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)).mpr (by decide)
      let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hc
      exact (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff_isMulCommutative.mpr inferInstance)).le.trans bot_le
    · exact (commutator_mono le_rfl (Z_le_localZSpan d.radical _ _)).trans hcross
  apply le_antisymm _ (commutator_mono hP₀P hP₀P)
  calc
    ⁅P,P⁆ = ⁅Z d.radical c ⊔ P₀,P⁆ := by rw [←hgen]
    _ ≤ C := commutator_sup_le_of_relative_normal J _ _ _ C hNG hSG (hP₀P.trans hPG) hSP hcross

include s in
/-- Transfer back to the whole selected span preserves its literal derived
subgroup, rather than replacing it with the moved subgroup's commutator. -/
theorem selected_span_derived_transfer
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
        center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)))
    (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6))
    (hequiv : ∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
      (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))
          (E (QuotientGroup.mk' _ x)).toAdd) :
    Nat.card (⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
    ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) →
      A.relIndex (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2 →
      ⁅A,A⁆ = ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ := by
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  let P₀ := forwardMovedSpan d.radical c
  have hd : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)]
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical hd).trans ((replacementGeometry h d).V_local _ rfl hb)
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hP₀P : P₀ ≤ P := forwardMovedSpan_le d.radical c
  let : Finite P₀ := Finite.of_injective (inclusion hP₀P) (inclusion_injective _)
  have hm := selected_span_derived_eq_moved (h := h) hb p hfixed
  have ht := selected_moved_span_derived_transfer s hb c hd hfixed E τ hequiv
  refine ⟨by rw [hm]; exact ht.2.1,?_⟩
  intro A hA hi
  have hi₀ : (A ⊓ P₀).relIndex P₀ ≤ 2 := by
    rw [inf_relIndex_right]
    exact (relIndex_le_of_le_right hP₀P index_ne_zero_of_finite).trans hi
  have he : ⁅A ⊓ P₀,A ⊓ P₀⁆ = ⁅P,P⁆ :=
    (ht.2.2 (A ⊓ P₀) inf_le_right hi₀).trans hm.symm
  apply le_antisymm (commutator_mono hA hA)
  rw [←he]
  exact commutator_mono inf_le_left inf_le_left

include s in
private theorem selected_natural_quotient_and_transfer
    (hc : DistanceTwo.CentralLayer d)
    (hsq : IsSQTK KnownSimple.IsKnownSimple d.overgroup)
    (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2), Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ∃ (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
          center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
        Multiplicative (BinaryPermutation.natural (Fin 6)))
      (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6)),
      (∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
        (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 6)
            (τ (s.projection m))
            (E (QuotientGroup.mk' _ x)).toAdd) ∧
      (center (forwardMovedSpan d.radical (p.walk.getVert 2))).index = 16 ∧
      Nat.card (⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) →
        A.relIndex (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2 →
        ⁅A,A⁆ = ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ := by
  obtain ⟨E,τ,hequiv⟩ := selected_natural_quotient_of_path_estimates s hc hb
    hsq p hsmall hnonabelian hfixed hindex hcomm
  have hd : (cosetGraph d.radical).dist (p.walk.getVert 2) (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)]
  exact ⟨E,τ,hequiv,(selected_moved_span_derived_transfer s hb _ hd hfixed E τ hequiv).1,
    selected_span_derived_transfer s hb p hfixed E τ hequiv⟩

/-- The original replacement supplies the marking, central layer and SQTK
inputs. The selected-path estimates stay with this task's source assembly. -/
theorem selected_natural_quotient_and_transfer_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2), Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ∃ (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
          center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
        Multiplicative (BinaryPermutation.natural (Fin 6)))
      (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6)),
      (∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
        (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 6)
            (τ (SourceReduction.projection h e hz hn d m))
            (E (QuotientGroup.mk' _ x)).toAdd) ∧
      (center (forwardMovedSpan d.radical (p.walk.getVert 2))).index = 16 ∧
      Nat.card (⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) →
        A.relIndex (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2 →
        ⁅A,A⁆ = ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have result := selected_natural_quotient_and_transfer s
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d)
    (h.sqtk.subgroup d.overgroup) hb p hsmall hnonabelian hfixed hindex hcomm
  rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at result


open scoped Pointwise

include h in
private theorem selected_component_radical_sup : replacementComponent d ⊔ d.radical = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
  exact mul_mem (mem_sup_left hk) (mem_sup_right hr)

include h in
/-- A nonabelian selected orbit span supplies a critical conjugate of its
seed. The walk uses the original first edge, passes through the original
base vertex, and then uses its image under the same conjugator. -/
theorem selected_span_conjugate_critical_path
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    replacementDistance h d = 4 ∧
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
          (p.walk.getVert 2) (act d.radical x (p.walk.getVert 2)),
          q.walk.getVert 1 = p.walk.getVert 1 ∧
          q.walk.getVert 2 = alpha d.radical ∧
          q.walk.getVert 3 = act d.radical x (p.walk.getVert 1) := by
  classical
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  have hex : ∃ x ∈ stabilizer d.radical (alpha d.radical),
      ⁅Z d.radical c,Z d.radical (act d.radical x c)⁆ ≠ ⊥ := by
    by_contra! hn
    have hZC : Z d.radical c ≤ centralizer (P : Set (FreeAmalgam d.radical)) := by
      apply le_centralizer_iff.mpr
      dsimp only [P]
      rw [localZSpan_eq_conjugates]
      apply iSup_le
      intro g
      have hg := le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (hn g g.property))
      rwa [Z_act] at hg
    have hPC : P ≤ centralizer (P : Set (FreeAmalgam d.radical)) := by
      conv_lhs => dsimp only [P]; rw [localZSpan_eq_conjugates]
      apply iSup_le
      intro g
      have hg := (map_mono (f := (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom)
        hZC).trans (map_centralizer_le_centralizer_image _ _)
      have hnP := mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized d.radical c (alpha d.radical)
          ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
      change P.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = P at hnP
      change (Z d.radical c).map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom ≤
        centralizer ((P.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom) : Set (FreeAmalgam d.radical)) at hg
      rwa [hnP] at hg
    exact hnonabelian (commutator_eq_bot_iff_le_centralizer.mpr hPC)
  obtain ⟨x,hx,hcomm⟩ := hex
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hxc : color d.radical (act d.radical x c) = false := by
    rw [action_preserves_color,hc]
  have hn : ¬ Z d.radical c ≤ Q d.radical (act d.radical x c) := by
    intro hh
    exact hcomm (commutator_eq_bot_iff_le_centralizer.mpr
      (hh.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical _ hxc)))))
  let v := p.walk.take 2
  have hv : v.length = 2 := by
    rw [SimpleGraph.Walk.take_length,inf_eq_left.mpr (by omega)]
  have hfix : act d.radical x (alpha d.radical) = alpha d.radical := hx
  let w := v.reverse.append ((actWalk d.radical x v).copy hfix rfl)
  have hw : w.length = 4 := by
    rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.length_copy,actWalk_length,hv]
  have hdist : (cosetGraph d.radical).dist c (act d.radical x c) ≤ 4 :=
    hw ▸ SimpleGraph.dist_le w
  have hmin := criticalDistance_le d.radical c
    ((replacementGeometry h d).exists_critical c hc) hn
  rw [(replacementGeometry h d).distance_constant c hc] at hmin
  change replacementDistance h d ≤ _ at hmin
  have heven := replacementDistance_even h d
  rw [Nat.even_iff] at heven
  have hb4 : replacementDistance h d = 4 := by omega
  have hd : (cosetGraph d.radical).dist c (act d.radical x c) =
      replacementDistance h d := by omega
  let q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical x c) := {
    start_color := hc
    walk := w
    shortest := hw.trans (hd.trans hb4).symm
    critical := ⟨by rw [(replacementGeometry h d).distance_constant c hc]; exact hd,hn⟩ }
  refine ⟨hb4,x,hx,q,?_,?_,?_⟩
  · change w.getVert 1 = _
    simp only [w,SimpleGraph.Walk.getVert_append,SimpleGraph.Walk.length_reverse,hv,
      show (1:ℕ) < 2 by decide,if_pos,SimpleGraph.Walk.getVert_reverse,
      v,SimpleGraph.Walk.take_getVert]
    rfl
  · change w.getVert 2 = _
    simp only [w,SimpleGraph.Walk.getVert_append',SimpleGraph.Walk.length_reverse,hv,
      le_refl,if_pos,SimpleGraph.Walk.getVert_reverse,Nat.sub_self,
      SimpleGraph.Walk.getVert_zero]
  · change w.getVert 3 = _
    simp only [w,SimpleGraph.Walk.getVert_append,SimpleGraph.Walk.length_reverse,hv,
      show ¬ (3:ℕ) < 2 by decide,SimpleGraph.Walk.getVert_copy,actWalk_getVert,
      v,SimpleGraph.Walk.take_getVert]
    rfl

private theorem selected_small_subgroup_centralized
    {M : Type*} [Group M] [Finite M] (A B : Subgroup M)
    (hn : A ≤ normalizer (B : Set M)) (hc : Nat.card B ≤ 2) :
    A ≤ centralizer (B : Set M) := by
  have hp := Nat.card_pos (α := B)
  have hh : Nat.card B = 1 ∨ Nat.card B = 2 := by omega
  rcases hh with hh | hh
  · rw [card_eq_one.mp hh]
    intro a _ b hb
    have hb1 : b = 1 := mem_bot.mp hb
    simp only [hb1,mul_one,one_mul]
  · exact hn.trans (normalizer_le_centralizer_of_card_two B hh)

include s in
private theorem selected_derived_fixed_of_two_central_lines
    (D : Subgroup d.overgroup) (hDQ : D≤pCore 2 d.overgroup)
    (hDN : d.radical≤normalizer (D:Set d.overgroup))
    (hDcard : Nat.card (⁅D,D⁆:Subgroup d.overgroup)≤2)
    (hCcard : Nat.card (⁅⁅pCore 2 d.overgroup,replacementComponent d⁆,⁅pCore 2 d.overgroup,replacementComponent d⁆⁆:Subgroup d.overgroup)≤2)
    (hcomm : ⁅D,⁅pCore 2 d.overgroup,replacementComponent d⁆⁆≤⁅⁅pCore 2 d.overgroup,replacementComponent d⁆,⁅pCore 2 d.overgroup,replacementComponent d⁆⁆) :
    ⁅D,D⁆≤centralizer (replacementComponent d:Set d.overgroup) := by
  let := replacementComponent_normal h d
  let C := ⁅pCore 2 d.overgroup,replacementComponent d⁆
  have hDn : d.radical ≤ normalizer ((⁅D,D⁆ : Subgroup d.overgroup) : Set d.overgroup) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hDN hg)]
  have hDC : ⁅D,D⁆ ≤ centralizer (d.radical : Set d.overgroup) :=
    le_centralizer_iff.mp (selected_small_subgroup_centralized _ _ hDn hDcard)
  have hCC : ⁅C,C⁆ ≤ centralizer (d.radical : Set d.overgroup) :=
    le_centralizer_iff.mp (selected_small_subgroup_centralized _ _ le_normalizer_of_normal hCcard)
  let N := D⊔C
  let H := ⁅D,D⁆⊔⁅C,C⁆
  have hCQ : C≤pCore 2 d.overgroup := commutator_le_left _ _
  have hDR : D≤d.radical := hDQ.trans (replacement_core_le_radical h d)
  have hCR : C≤d.radical := hCQ.trans (replacement_core_le_radical h d)
  have hHR : H≤centralizer (d.radical:Set d.overgroup) := sup_le hDC hCC
  have hHN : d.radical≤normalizer (H:Set d.overgroup) :=
    (le_centralizer_iff.mp hHR).trans (Subgroup.centralizer_le_normalizer _)
  have hNC : ⁅N,N⁆≤H := by
    apply commutator_sup_le_of_relative_normal d.radical D C N H hHN hDR hCR
    · rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal d.radical D C D H hHN hDR hCR le_sup_left
      exact (by rw [commutator_comm]; exact hcomm.trans le_sup_right)
    · rw [commutator_comm]
      exact commutator_sup_le_of_relative_normal d.radical D C C H hHN hDR hCR
        (hcomm.trans le_sup_right) le_sup_right
  have hNnorm : (⊤:Subgroup d.overgroup)≤normalizer (N:Set d.overgroup) := by
    rw [←selected_component_radical_sup (h := h)]
    apply sup_le
    · apply le_normalizer_iff_commutator_le_right.mpr
      rw [commutator_comm]
      exact (commutator_mono (sup_le hDQ hCQ) le_rfl).trans le_sup_right
    · apply le_trans (le_inf hDN (le_normalizer_of_normal (H:=C)))
        (normalizer_inf_normalizer_le_normalizer_sup D C)
  let : N.Normal := ⟨by
    intro n hn g
    exact (le_normalizer_iff.mp hNnorm g (mem_top _)) n hn⟩
  have hNQ : ⁅N,N⁆≤pCore 2 d.overgroup :=
    (show ⁅N,N⁆≤N from commutator_le_left _ _).trans (sup_le hDQ hCQ)
  have hcardH : Nat.card H≤4 := by
    have hprod : ((⁅D,D⁆:Subgroup d.overgroup):Set d.overgroup)*((⁅C,C⁆:Subgroup d.overgroup):Set d.overgroup)=(H:Set d.overgroup) :=
      (coe_mul_of_right_le_normalizer_left _ _
        (((commutator_le_left C C).trans hCR).trans
          ((le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _)))).symm
    let f : (⁅D,D⁆:Subgroup d.overgroup)×(⁅C,C⁆:Subgroup d.overgroup)→H :=
      fun x => ⟨x.1*x.2,H.mul_mem (mem_sup_left x.1.property) (mem_sup_right x.2.property)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x,hx⟩
      have hx' : x∈((⁅D,D⁆:Subgroup d.overgroup):Set d.overgroup)*((⁅C,C⁆:Subgroup d.overgroup):Set d.overgroup) := hprod.symm ▸ hx
      obtain ⟨a,ha,b,hb,rfl⟩ := hx'
      exact ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl⟩
    have hh := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_prod] at hh
    exact hh.trans (Nat.mul_le_mul hDcard hCcard)
  have hcard : (⊥:Subgroup d.overgroup).relIndex ⁅N,N⁆≤8 := by
    rw [relIndex_bot_left]
    exact (card_le_of_le hNC).trans (hcardH.trans (by decide))
  have hker : IsPGroup 2 s.projection.ker := by
    rw [s.projection_kernel]
    exact pCore_isPGroup
  have hh := commutator_pResidual_le_of_symmetricSix_small_section s.projection
    (s.surjective) hker ⁅N,N⁆ ⊥
    (hNQ.trans_eq s.projection_kernel.symm) hcard
  rw [replacement_residual h d] at hh
  exact commutator_eq_bot_iff_le_centralizer.mp
    (le_bot_iff.mp ((commutator_mono (commutator_mono le_sup_left le_sup_left) le_rfl).trans hh))

include h in
private theorem selected_edge_coordinates {c t : Vertex d.radical}
    (hc : color d.radical c=false) (hct : Adjacent d.radical c t) :
    ∃ i : d.overgroup→*FreeAmalgam d.radical, Function.Injective i ∧
      d.radical.map i=Q d.radical t ∧ (pCore 2 d.overgroup).map i=Q d.radical c ∧ (replacementComponent d).map i=Ltilde d.radical c := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_⟩
    · have he := Q_act d.radical g (beta d.radical)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
    · have he := Q_act d.radical g (alpha d.radical)
      rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := Ltilde_act d.radical g (alpha d.radical)
      rw [Ltilde_alpha,replacement_residual h d] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc

include s in
private theorem selected_derived_fixed_of_two_central_lines_at
    {c t : Vertex d.radical} (hc : color d.radical c=false) (hct : Adjacent d.radical c t)
    (D : Subgroup (FreeAmalgam d.radical)) (hDQ : D≤Q d.radical c)
    (hDN : Q d.radical t≤normalizer (D:Set (FreeAmalgam d.radical)))
    (hDcard : Nat.card (⁅D,D⁆:Subgroup (FreeAmalgam d.radical))≤2)
    (hCcard : Nat.card (⁅⁅Q d.radical c,Ltilde d.radical c⁆,⁅Q d.radical c,Ltilde d.radical c⁆⁆:Subgroup (FreeAmalgam d.radical))≤2)
    (hcomm : ⁅D,⁅Q d.radical c,Ltilde d.radical c⁆⁆≤⁅⁅Q d.radical c,Ltilde d.radical c⁆,⁅Q d.radical c,Ltilde d.radical c⁆⁆) :
    ⁅D,D⁆≤centralizer (Ltilde d.radical c:Set (FreeAmalgam d.radical)) := by
  obtain ⟨i,hi,hiR,hiQ,hiL⟩ := selected_edge_coordinates (h := h) hc hct
  let D₀ := D.comap i
  let C₀ := ⁅pCore 2 d.overgroup,replacementComponent d⁆
  have hDm : D₀.map i=D := map_comap_eq_self (hDQ.trans (hiQ ▸ map_le_range i _))
  have hCm : C₀.map i=⁅Q d.radical c,Ltilde d.radical c⁆ := by rw [map_commutator,hiQ,hiL]
  have hDDm : (⁅D₀,D₀⁆:Subgroup d.overgroup).map i=⁅D,D⁆ := by rw [map_commutator,hDm]
  have hCCm : (⁅C₀,C₀⁆:Subgroup d.overgroup).map i=⁅⁅Q d.radical c,Ltilde d.radical c⁆,⁅Q d.radical c,Ltilde d.radical c⁆⁆ := by
    rw [map_commutator,hCm]
  have hD₀Q : D₀≤pCore 2 d.overgroup := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hDm,hiQ]
  have hD₀N : d.radical≤normalizer (D₀:Set d.overgroup) :=
    ((map_le_iff_le_comap).mp (hiR ▸ hDN)).trans (le_normalizer_comap i)
  have hD₀card : Nat.card (⁅D₀,D₀⁆:Subgroup d.overgroup)≤2 := by
    rwa [←hDDm,card_map_of_injective hi] at hDcard
  have hC₀card : Nat.card (⁅C₀,C₀⁆:Subgroup d.overgroup)≤2 := by
    rwa [←hCCm,card_map_of_injective hi] at hCcard
  have hcomm₀ : ⁅D₀,C₀⁆≤⁅C₀,C₀⁆ := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [map_commutator,hDm,hCm,hCCm]
  have hh := selected_derived_fixed_of_two_central_lines s D₀ hD₀Q hD₀N
    hD₀card hC₀card hcomm₀
  have hm := (map_mono (f:=i) hh).trans (map_centralizer_le_centralizer_image _ _)
  change (⁅D₀,D₀⁆:Subgroup d.overgroup).map i≤centralizer ((replacementComponent d).map i:Set (FreeAmalgam d.radical)) at hm
  rwa [hDDm,hiL] at hm

include s in
/-- The index-two transfer and the opposite core estimates contradict the
critical commutator on the same pair of conjugate seeds. This retains the
central attachment of the order-thirty-two moving cover. -/
theorem selected_terminal_false_of_opposite_core_bounds
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hcard : Nat.card (⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2)
    (htransfer :
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2)⁆ =
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆)
    (hCcard : Nat.card (⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2)
    (hcross : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ ≤
      ⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
        ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆) : False := by
  have hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ := by
    intro hz
    rw [hz,card_bot] at hcard
    omega
  obtain ⟨_,x,hx,q,_,_,_⟩ := selected_span_conjugate_critical_path hb p hnonabelian
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan d.radical c (alpha d.radical)
  let D := P ⊓ Q d.radical c
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcolor : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hQa : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hz => hz.2 _ (adjacent_symm d.radical hat)
  have hQc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hz => hz.2 _ (adjacent_symm d.radical hct)
  have hPN : stabilizer d.radical (alpha d.radical) ≤
      normalizer ((⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized d.radical c (alpha d.radical) hg)]
  have hPC : ⁅P,P⁆ ≤ centralizer
      (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hPN.trans (normalizer_le_centralizer_of_card_two _ hcard))
  have hDN : Q d.radical t ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQa.trans (localZSpan_normalized d.radical c (alpha d.radical)))
      (hQc.trans (Q_normalized d.radical c))).trans inf_normalizer_le_normalizer_inf
  have hDcard : Nat.card (⁅D,D⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
    change Nat.card (⁅P ⊓ Q d.radical c,P ⊓ Q d.radical c⁆ :
      Subgroup (FreeAmalgam d.radical)) ≤ 2
    rw [htransfer,hcard]
  have hfixed := selected_derived_fixed_of_two_central_lines_at s hcolor hct D
    inf_le_right hDN hDcard hCcard hcross
  rw [htransfer] at hfixed
  have hcenter : ⁅P,P⁆ ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←selected_residual_edge_generation (h := h) hcolor hct]
    exact sup_le (le_centralizer_iff.mp hfixed)
      (hQa.trans (le_centralizer_iff.mp hPC))
  have hcP : Z d.radical c ≤ P := Z_le_localZSpan d.radical _ _
  have hxP : Z d.radical (act d.radical x c) ≤ P := by
    rw [Z_act]
    exact (map_mono hcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized d.radical c (alpha d.radical)
        ((stabilizer d.radical (alpha d.radical)).inv_mem hx)))
  exact critical_commutator_not_central s hc q
    ((commutator_mono hcP hxP).trans hcenter)

include s in
/-- The constructed natural quotient supplies the order and transfer
premises of the terminal contradiction. The conjugate critical path is
constructed from nonabelianness; the selected-span and core estimates remain. -/
theorem selected_natural_terminal_false
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (hsq : IsSQTK KnownSimple.IsKnownSimple d.overgroup)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical))
    (hCcard : Nat.card (⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2)
    (hcross : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ ≤
      ⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
        ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆) : False := by
  obtain ⟨E,τ,hequiv⟩ := selected_natural_quotient_of_path_estimates s hc hb hsq p
    hsmall hnonabelian hfixed hindex hcomm
  have ht := selected_span_derived_transfer s hb p hfixed E τ hequiv
  have hi : (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2 := by
    rwa [inf_relIndex_left]
  exact selected_terminal_false_of_opposite_core_bounds s hc hb p ht.1
    (ht.2 _ inf_le_left hi) hCcard hcross

/-- The original replacement discharges the marking, central-layer and SQTK
premises. This task retains the displayed selected-path and core estimates. -/
theorem selected_natural_terminal_false_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical))
    (hCcard : Nat.card (⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2)
    (hcross : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ ≤
      ⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
        ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆) : False := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  exact selected_natural_terminal_false s hc hb (h.sqtk.subgroup d.overgroup)
    p hnonabelian hsmall hfixed hindex hcomm hCcard hcross

/-- The literal replacement supplies the symmetric marking, central layer and
SQTK premises. Its selected-path estimates and the core endpoint action
remain obligations of this task's final source assembly. -/
theorem selected_core_derived_transfer_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2), Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical))
    (hcoreIndex : (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2)
    (hcoreActor : ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
    C ≤ Z d.radical (alpha d.radical) ⊔ forwardMovedSpan d.radical (p.walk.getVert 2) ∧
      Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ C → A.relIndex C ≤ 2 → ⁅A,A⁆ = ⁅C,C⁆ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨E,τ,hE⟩ := selected_natural_quotient_of_path_estimates s hc hb
    (h.sqtk.subgroup d.overgroup) p hsmall hnonabelian hfixed hindex hcomm
  exact selected_core_derived_transfer s hc hb p hsmall hfixed E τ hE hcoreIndex hcoreActor

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
