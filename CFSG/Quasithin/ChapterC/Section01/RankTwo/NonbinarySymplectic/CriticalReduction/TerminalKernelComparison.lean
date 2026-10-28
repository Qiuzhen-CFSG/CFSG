module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalKernelDisplacement

/-!
# Comparing the full terminal critical kernels

On the same saturated large-mover terminal sequence, let a,z be the
endpoints of the second backward shift and c,e those of the preceding
shift. Set E = Z_a intersect Q_z and R_gamma = [E,Z_e intersect Q_c].
The whole moving intersection U_e intersect Q_c normalizes E joined
with Z_c. The proved endpoint normalizer escape and radius quadraticity
therefore apply the full-cover hyperplane comparison to this join.
It gives R_gamma contained in [Z_c,Z_e] and bounds its order by q;
the preceding lower bound makes its order exactly q.

Adjoining R_4 = [Z_a,Z_z] retains the full moving layer at a. The joined
subgroup centralizes both nearby endpoint seeds. Actual selected-edge
generation and its residual conjugator propagate the first-edge
intersection into the full vertex center at a. Saturation of R_4 gives
the reverse inclusion. Thus (R_gamma join R_4) intersect Z_t is exactly
U_a intersect Z(G_a), including the entire central covering kernel.
All periodic kernels, overlaps, quotient orders and X/Z/U identities
remain attached to the same selected paths, at every nonbinary degree.

The existing private model comparison is now exported by
`TrappedRootComparison`; its proof is unchanged. This is the commutator
and joined-kernel comparison on MS93 p.922, not the terminal contradiction.
The remaining normalizer contradiction, unequal-contained Lambda
selectors, (5.10)--(5.12) exclusions and actual minimum-replacement
distance-two witness remain required. The independent original-radical
characteristic-control obligation is unchanged.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.9)--(5.10), printed pp.866--867 and 920--923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open ChapterB.QuasisimpleSource MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

/-- The full critical-intersection comparison retains containment in the
original critical commutator, including its central kernel. -/
theorem Input.replacement_critical_intersection_le_commutator_of_comparison
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (Y : Subgroup (FreeAmalgam d.radical)) (hZaY : Z d.radical a ≤ Y)
    (hYQ : Y ≤ Q d.radical a) (hYS : Y ≤ stabilizer d.radical z)
    (hquad : ⁅⁅X d.radical z ⊓ Q d.radical a,Y⁆,Y⁆=⊥)
    (hi : (Q d.radical z).relIndex (Z d.radical a)=Nat.card F)
    (hi' : (Q d.radical a).relIndex (Z d.radical z)=Nat.card F)
    (hbad : ¬ ⁅Y,Z d.radical z⁆ ≤ Z d.radical a ⊔ ⁅Y,X d.radical z ⊓ Q d.radical a⁆) :
    ⁅Y,X d.radical z ⊓ Q d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ := by
  let A := X d.radical z ⊓ Q d.radical a
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [hi]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hAU : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ Q d.radical a := by
    rw [←hCa]
    ext x
    exact ⟨fun hx => ⟨hx.1,hUS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have hZX : Z d.radical z ≤ X d.radical z := geometry.omega_bound z path.end_color
    (by rw [geometry.distance_constant z path.end_color]; exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  have hUA : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) ≤ A := by
    rw [hAU]
    exact inf_le_inf ((U_le_Z z).trans hZX) le_rfl
  have hpos : 0 < geometry.b d.radical := by omega
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let β := (e.groupEquiv.toMonoidHom.comp κC).comp (inclusion hYS)
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hact (y : Y) (w : s.space.toSubmodule) : j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hYS y)))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hYS y) w
  let βT := β.comp (inclusion (show Z d.radical a ≤ Y from hZaY))
  have hcard : Nat.card βT.range=Nat.card E.Carrier := by
    have hmark : βT.ker=(Q d.radical z).subgroupOf (Z d.radical a) := by
      ext x
      change e.groupEquiv (κC (inclusion hYS (inclusion hZaY x)))=1 ↔ x.val ∈ Q d.radical z
      rw [e.groupEquiv.map_eq_one_iff]
      have heq : κC (inclusion hYS (inclusion hZaY x))=1 ↔
          inclusion hYS (inclusion hZaY x) ∈ κ.ker := Subtype.ext_iff
      rw [heq]
      constructor
      · intro hx
        exact hκQ ▸ mem_map_of_mem (stabilizer d.radical z).subtype hx
      · intro hx
        obtain ⟨y,hy,hyx⟩ := hκQ.symm ▸ hx
        have he : y=inclusion hYS (inclusion hZaY x) := Subtype.ext hyx
        exact he ▸ hy
    rw [←index_ker,hmark]
    exact hi.trans hFc.symm
  have hactT (x : Z d.radical a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (βT x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ :=
    hact (inclusion hZaY x) w
  obtain ⟨hd,hrootquad⟩ := critical_root_coordinates_of_reciprocal_index_field path hpos hCa hFl
    σ p he j hj hjr βT hactT hcard (hi'.trans hFc.symm)
  have hcomm : ⁅Z d.radical a,j.range⁆ ≤ Z d.radical a := by
    rw [hjr]
    exact (commutator_mono le_rfl (U_le_Z z)).trans (critical_commutator_le_start_seed path)
  have hcent : Y ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)))
  have hwhole : ⁅Y,X d.radical z ⊓ Q d.radical a⁆ =
      ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ := by
    rw [(h.replacement_root_intersection_fixed_and_commutator d path hb hsmall Y hYS).1,hAU]
  have hbadU : ¬ ⁅Y,U d.radical z⁆ ≤ Z d.radical a ⊔
      ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ := by
    rw [←hwhole]
    intro hh
    apply hbad
    rw [commutator_comm Y (Z d.radical z),
      h.replacement_Z_commutator_eq_U d geometry hb path.end_color Y hYS,
      commutator_comm (U d.radical z)]
    exact hh
  have hbound := TrappedRootComparison.embedded_root_hyperplane_le_commutator_of_comparison hFl p he j hj Y
    (Z d.radical a) hZaY β hact hcard hd hrootquad hcomm hcent
    (by rw [hjr]; exact le_bot_iff.mp ((commutator_mono (commutator_mono hUA le_rfl) le_rfl).trans_eq hquad))
    (by rw [hjr]; exact hbadU)
  rw [hjr,←hwhole] at hbound
  exact hbound.trans (commutator_mono le_rfl (U_le_Z z))


/-- On the same saturated terminal sequence, the nonzero mutual-kernel
commutator lies in the preceding full critical commutator and has order q.
Its join with R₄ has exactly the original full central kernel at the first edge. -/
theorem Input.replacement_large_mover_terminal_kernel_comparison
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical p.first)
      (Q d.radical p.first) (Q d.radical (p.path.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical p.first)) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (pointPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, let C := fun j => U d.radical (s j).first ⊓
          centralizer (stabilizer d.radical (s j).first : Set (FreeAmalgam d.radical))
        let D := ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆
        C (i+2) = C i ∧
        D ⊓ Z d.radical ((s (i+2)).path.walk.getVert 1) = C i ∧
        D ⊓ (stabilizer d.radical (s (i+1)).first ⊓
          centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) = C i ∧
        Nat.card D = Nat.card F * Nat.card (C 0) ∧
        (∀ k, C i ≤ stabilizer d.radical (s (i+k)).first ⊓
          centralizer (stabilizer d.radical (s (i+k)).first : Set (FreeAmalgam d.radical))) ∧
        (Q d.radical (s (i+2)).last).relIndex (Z d.radical (s (i+2)).first)=Nat.card F ∧
        (Q d.radical (s (i+2)).first).relIndex (Z d.radical (s (i+2)).last)=Nat.card F ∧
        (¬ Z d.radical (s (i+2)).first ⊓ Q d.radical (s (i+2)).last ≤
          B d.radical (s (i+1)).first (geometry.Z_normal (s (i+1)).first))) ∧
      (∀ i, let a := (s (i+2)).first
        let z := (s (i+2)).last
        let c := (s (i+1)).first
        let e := (s (i+1)).last
        let E := Z d.radical a ⊓ Q d.radical z
        let D := ⁅E,Z d.radical e ⊓ Q d.radical c⁆
        (Q d.radical e).relIndex (Z d.radical c)=Nat.card F ∧
        (Q d.radical c).relIndex (Z d.radical e)=Nat.card F ∧
        ¬ ⁅E,Z d.radical e⁆ ≤ Z d.radical c ∧
        (¬ Z d.radical e ≤ normalizer ((E ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
        D ≠ ⊥ ∧ Nat.card F ≤ Nat.card D ∧
        ⁅E,X d.radical e ⊓ Q d.radical c⁆ = D ∧
        D = ⁅E,U d.radical e ⊓ Q d.radical c⁆ ∧
        D ≤ E ⊓ U d.radical e ∧ ⁅D,E⁆=⊥ ∧
        D ≤ ⁅Z d.radical c,Z d.radical e⁆ ∧ Nat.card D=Nat.card F ∧
        (D ⊔ ⁅Z d.radical a,Z d.radical z⁆) ⊓
          Z d.radical ((s (i+2)).path.walk.getVert 1) =
          U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  obtain ⟨s,hs0,hs,hover,hdata,hdisp⟩ := h.replacement_large_mover_terminal_kernel_displacement d p hb hJm
  refine ⟨s,hs0,hs,hover,hdata,?_⟩
  intro i
  dsimp only
  obtain ⟨hic,hie,hbad,hnotnorm,hne,hlo,hX,hU,hEU,hquadE⟩ := hdisp i
  let a := (s (i+2)).first
  let z := (s (i+2)).last
  let c := (s (i+1)).first
  let e := (s (i+1)).last
  let E := Z d.radical a ⊓ Q d.radical z
  let Y := E ⊔ Z d.radical c
  let A := U d.radical e ⊓ Q d.radical c
  obtain ⟨w,hw,hcw,haw,hfirst⟩ := (hs (i+1)).choice
  have hEV : E ≤ V d.radical c := inf_le_left.trans
    (le_sup_left.trans (neighbor_seed_join_le_radius hcw haw))
  have hYV : Y ≤ V d.radical c := sup_le hEV (Z_le_VBall d.radical c 2)
  have hYQ : Y ≤ Q d.radical c := hYV.trans
    (geometry.V_le_Q (by omega) c (s (i+1)).path.start_color)
  have hdist : (cosetGraph d.radical).dist z e=2 := by
    simpa only [show i+1+1=i+2 by omega] using
      shifted_last_distance (pointPathChoice geometry (Nat.card F)) s hs (i+1) 1 (by omega)
  have hES : E ≤ stabilizer d.radical e := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two z e (s (i+2)).path.end_color
      (s (i+1)).path.end_color hdist.le)
  have hYS : Y ≤ stabilizer d.radical e := sup_le hES
    (Z_le_stabilizer_of_dist_le c (geometry.exists_critical c (s (i+1)).path.start_color)
      (s (i+1)).path.critical.1.le)
  have hcQz : Z d.radical c ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt _ c (geometry.exists_critical c (s (i+1)).path.start_color)
    have hz := (hs (i+1)).last_eq
    simp only [show i+1+1=i+2 by omega] at hz
    dsimp only [c,z]
    rw [hz,(s (i+1)).path.dist_start (by rw [(s (i+1)).path.length_eq_b]; omega),
      geometry.distance_constant (s (i+1)).first (s (i+1)).path.start_color]
    change geometry.b d.radical-2 < geometry.b d.radical
    omega
  have hYVz : Y ≤ V d.radical c ⊓ Q d.radical z :=
    le_inf hYV (sup_le inf_le_right hcQz)
  have hquad : ⁅⁅X d.radical e ⊓ Q d.radical c,Y⁆,Y⁆=⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono le_rfl hYVz) hYVz).trans_eq
      (h.replacement_radius_commutator_bounds d geometry hb.le (s (i+1)).path.start_color e z).2)
  have hASa : A ≤ stabilizer d.radical a := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two c a (s (i+1)).path.start_color
      (s (i+2)).path.start_color (by
        rw [SimpleGraph.dist_comm]
        simpa only [show i+1+1=i+2 by omega] using
          (shifted_start_distance (pointPathChoice geometry (Nat.card F)) s hs (i+1) 1 (by omega)).le))
  have heQz : U d.radical e ≤ Q d.radical z := by
    exact (U_le_Z e).trans (by
      apply Z_le_Q_of_dist_lt _ e (geometry.exists_critical e (s (i+1)).path.end_color)
      rw [geometry.distance_constant e (s (i+1)).path.end_color,SimpleGraph.dist_comm,hdist]
      change 2 < geometry.b d.radical; omega)
  have hANE : A ≤ normalizer (E : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change E.map (MulAut.conj x).toMonoidHom=E
    dsimp only [E]
    rw [map_inf _ _ _ (MulAut.conj x).injective,MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a (hASa hx)),
      mem_normalizer_iff_map_conj_eq.mp ((Q d.radical z).le_normalizer (heQz hx.1))]
  have hANY : A ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    (le_inf hANE ((inf_le_right.trans (fun _ hx => hx.1)).trans (Z_normalized d.radical c))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hbadY : ¬ ⁅Y,Z d.radical e⁆ ≤ Z d.radical c ⊔ ⁅Y,A⁆ := by
    intro hh
    apply hnotnorm
    exact le_normalizer_iff_commutator_le_left.mpr (hh.trans
      (sup_le le_sup_right (le_normalizer_iff_commutator_le_left.mp hANY)))
  have hsmall : (Q d.radical e).relIndex (Z d.radical c) < Nat.card F^2 := by
    rw [hic]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith
  have hfull := (h.replacement_root_intersection_fixed_and_commutator d
    (s (i+1)).path hb.le hsmall Y hYS).1
  have hbadfull : ¬ ⁅Y,Z d.radical e⁆ ≤ Z d.radical c ⊔
      ⁅Y,X d.radical e ⊓ Q d.radical c⁆ := by
    rw [hfull]; exact hbadY
  have hbound := h.replacement_critical_intersection_le_commutator_of_comparison d
    (s (i+1)).path hb.le Y le_sup_right hYQ hYS hquad hic hie hbadfull
  have hcard := h.replacement_critical_intersection_bound_of_comparison d
    (s (i+1)).path hb.le Y le_sup_right hYQ hYS hquad hic hie hbadfull
  rw [hfull] at hbound hcard
  have hsub : ⁅E,Z d.radical e ⊓ Q d.radical c⁆ ≤ ⁅Y,A⁆ := by
    rw [hU]
    exact commutator_mono le_sup_left le_rfl
  have hfin : ⁅Y,A⁆ ≤ U d.radical e := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hYS.trans (U_normalized e)))
  let := finite_stabilizer d.radical e
  let : Finite (⁅Y,A⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion (hfin.trans ((U_le_Z e).trans (Z_le_stabilizer d.radical e)))) (inclusion_injective _)
  have hupper := (Nat.card_le_card_of_injective _ (inclusion_injective hsub)).trans hcard
  let D := ⁅E,Z d.radical e ⊓ Q d.radical c⁆
  let D₄ := ⁅Z d.radical a,Z d.radical z⁆
  let I := (D ⊔ D₄) ⊓ Z d.radical w
  have hDUa : D ≤ U d.radical a := by
    dsimp only [D,E,a,z,c,e]
    rw [hU]
    apply (commutator_mono inf_le_left le_rfl).trans
    rw [h.replacement_Z_commutator_eq_U d geometry hb.le (s (i+2)).path.start_color A hASa]
    exact le_normalizer_iff_commutator_le_left.mp (hASa.trans (U_normalized a))
  have hD₄Ua : D₄ ≤ U d.radical a := by
    dsimp only [D₄,a,z]
    rw [h.replacement_Z_commutator_eq_U d geometry hb.le (s (i+2)).path.start_color
      (Z d.radical (s (i+2)).last) ((s (i+2)).path.endpoint_Z_le_start_stabilizer (by omega))]
    exact le_normalizer_iff_commutator_le_left.mp
      (((s (i+2)).path.endpoint_Z_le_start_stabilizer (by omega)).trans (U_normalized a))
  have hIU : I ≤ U d.radical a := inf_le_left.trans (sup_le hDUa hD₄Ua)
  obtain ⟨v,hv,hav,hcv,hfirst₀⟩ := (hs i).choice
  obtain ⟨y,hy,hyv,hyw,hidx⟩ := hw.1
  have he := (hs i).overlap 0 (by omega)
  simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
  rw [he] at hyv
  have hwcol : color d.radical w=true := by
    have hn := adjacent_color_ne d.radical hcw
    rw [(s (i+1)).path.start_color] at hn
    cases hh : color d.radical w <;> simp_all
  have hgenC : stabilizer d.radical c ≤ Q d.radical w ⊔ Z d.radical e := by
    rw [←hw.2.1]
    exact sup_le_sup_right (Subgroup.SmallMover.join_le _ _ _ _) _
  have hgen₀ : stabilizer d.radical (s i).first ≤ Q d.radical v ⊔ Z d.radical (s i).last := by
    rw [←hv.2.1]
    exact sup_le_sup_right (Subgroup.SmallMover.join_le _ _ _ _) _
  let : IsElementaryAbelian 2 (Z d.radical e) := geometry.Z_elementary (by omega) e (s (i+1)).path.end_color
  have hDe : D ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) :=
    (hEU.trans (inf_le_right.trans (U_le_Z e))).trans
      (commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr inferInstance))
  have hD₀ : D ≤ centralizer (Z d.radical (s i).last : Set (FreeAmalgam d.radical)) :=
    (hEU.trans (inf_le_right.trans (U_le_Z e))).trans
      (endpoint_seed_centralizes_nearby geometry hb (s (i+1)).path.end_color (s i).path.end_color (by
        have hh := shifted_last_distance (pointPathChoice geometry (Nat.card F)) s hs i 1 (by omega)
        exact hh.le.trans (by decide)))
  have hD₄e : D₄ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) := by
    simpa only [show i+1+1=i+2 by omega] using
      shifted_commutator_centralizes_endpoint (pointPathChoice geometry (Nat.card F)) s hs (i+1) 1 (by omega)
  have hD₄₀ : D₄ ≤ centralizer (Z d.radical (s i).last : Set (FreeAmalgam d.radical)) :=
    shifted_commutator_centralizes_endpoint (pointPathChoice geometry (Nat.card F)) s hs i 2 (by omega)
  have hcent := (central_intersection_propagates I hwcol hcw hcv inf_le_right
    (inf_le_left.trans (sup_le hDe hD₄e)) (inf_le_left.trans (sup_le hD₀ hD₄₀))
    hgenC hgen₀ y (Ltilde_le_stabilizer _ hy) hyv.symm).2.2
  have hIeq : I=U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm (le_inf hIU hcent)
    have heq := (hdata i).2.1
    rw [←(hdata i).1] at heq
    have hw' : (s (i+2)).path.walk.getVert 1=w := by
      simpa only [show i+1+1=i+2 by omega] using hfirst
    rw [hw'] at heq
    exact heq.symm.le.trans (inf_le_inf_right _ le_sup_right)
  have hIeq' : (D ⊔ D₄) ⊓ Z d.radical ((s (i+2)).path.walk.getVert 1) =
      U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hw' : (s (i+2)).path.walk.getVert 1=w := by
      simpa only [show i+1+1=i+2 by omega] using hfirst
    rw [hw']
    exact hIeq
  exact ⟨hic,hie,hbad,hnotnorm,hne,hlo,hX,hU,hEU,hquadE,hsub.trans hbound,Nat.le_antisymm hupper hlo,hIeq'⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
