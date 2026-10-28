module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexPathSelection
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.GroupTheory.PGroup.OmegaHomomorphism

/-!
# The faithful action on the literal distance-four span quotient

For W = <Z_e^{G_a}> at the actual midpoint of a critical path, the source
branch [V_a,Q_a] <= D_a puts [W,Q_a] in W intersect B_a. Involution
generation makes W/(W intersect B_a) elementary abelian. Its conjugation
action therefore descends through the same full vertex quotient onto Sp4.
The coordinate map remains the literal quotient map.

The path moving-index theorem makes W nontrivial modulo B_a. Triviality
of the descended action would put [W,L_a] in B_a; residual idempotence
then puts it in Z_a and forces W into B_a. Simplicity proves faithfulness.
The opposite full span has elementary image under this same projection,
without asserting that its image is nontrivial or is an offender.

Source: MS93 (5.12)(2), printed pp.925--926. The preceding exclusion of
the nonfixed radius case and the subsequent FF index comparison remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

private theorem span_omega_one {M : Type*} [Group M] (R : Subgroup M) (a e : Vertex R) :
    omegaOneAmbient (localZSpan R e a) = localZSpan R e a := by
  apply le_antisymm (omegaOneAmbient_le _)
  apply iSup_le
  intro g
  rw [←DistanceEight.Z_omegaOne R (act R g e)]
  exact omegaOneAmbient_mono (le_iSup (fun g : stabilizer R a => Z R (act R g e)) g)

private theorem elementary_quotient_of_omega {G : Type*} [Group G] (W D : Subgroup G)
    [(D.subgroupOf W).Normal] (hd : ⁅W,W⁆ ≤ D) (hΩ : omegaOneAmbient W = W) :
    IsElementaryAbelian 2 (W ⧸ D.subgroupOf W) := by
  have hder : _root_.commutator W ≤ D.subgroupOf W := by
    intro w hw
    apply hd
    rw [←map_subtype_commutator]
    exact mem_map_of_mem W.subtype hw
  let : IsMulCommutative (W ⧸ D.subgroupOf W) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hder
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro w
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf W) w
  apply MonoidHom.square_eq_one_on_omega₁
  have hv : (v : G) ∈ omegaOneAmbient W := hΩ.symm ▸ v.property
  obtain ⟨x,hx,hxv⟩ := hv
  have he : x=v := Subtype.ext hxv
  rwa [←he]

private theorem elementary_image_of_omega {G J : Type*} [Group G] [Group J]
    (S Q W : Subgroup G) (f : S →* J) (hfQ : f.ker.map S.subtype = Q)
    (hWS : W ≤ S) (hd : ⁅W,W⁆ ≤ Q) (hΩ : omegaOneAmbient W = W) :
    IsElementaryAbelian 2 ((W.subgroupOf S).map f) := by
  let A := (W.subgroupOf S).map f
  have hk : f.ker = Q.subgroupOf S := by
    rw [←hfQ]
    exact (comap_map_eq_self_of_injective S.subtype_injective f.ker).symm
  let : IsMulCommutative A := by
    apply commutator_self_eq_bot_iff.mp
    change ⁅(W.subgroupOf S).map f,(W.subgroupOf S).map f⁆ = ⊥
    rw [←map_commutator,Subgroup.map_eq_bot_iff,hk]
    intro x hx
    have hm := mem_map_of_mem S.subtype hx
    rw [map_commutator,map_subgroupOf_eq_of_le hWS] at hm
    exact hd hm
  let p : W →* A := (f.comp (inclusion hWS)).codRestrict A
    (fun x => ⟨inclusion hWS x,x.property,rfl⟩)
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro y
  obtain ⟨x,hx,he⟩ := y.property
  have hpe : p ⟨x,hx⟩ = y := Subtype.ext he
  rw [←hpe]
  apply MonoidHom.square_eq_one_on_omega₁
  have hxΩ : (x : G) ∈ omegaOneAmbient W := hΩ.symm ▸ hx
  obtain ⟨v,hv,hvx⟩ := hxΩ
  have he' : v=(⟨x,hx⟩ : W) := Subtype.ext hvx
  rwa [←he']

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Construct the faithful action on the full midpoint span modulo its
literal intersection with B, retaining the exact quotient coordinates and
the elementary opposite-span image under the same full-kernel projection. -/
theorem Input.replacement_distance_four_span_action_of_radius_fixed
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let e := path.walk.getVert 2
    let W := localZSpan d.radical e a
    let D := W ⊓ B d.radical a (geometry.Z_normal a)
    ∃ E : BinaryField, E.degree=n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype=Q d.radical a ∧
        ∃ hD : (D.subgroupOf W).Normal,
          letI := hD
          ∃ hEA : IsElementaryAbelian 2 (W ⧸ D.subgroupOf W),
            letI := hEA
            ∃ σ : Representation (ZMod 2) (Sp E.Carrier) (Additive (W ⧸ D.subgroupOf W)),
              Function.Injective σ ∧
              ∃ c : BinaryConjugationSection (stabilizer d.radical a) W D (σ.comp f),
                (∀ w : W, (c.coordinates w).toAdd=
                  Additive.ofMul (QuotientGroup.mk' (D.subgroupOf W) w)) ∧
                IsElementaryAbelian 2 (((localZSpan d.radical a e).subgroupOf
                  (stabilizer d.radical a)).map f) := by
  let e := path.walk.getVert 2
  let W := localZSpan d.radical e a
  let S := stabilizer d.radical a
  let B₀ := B d.radical a (geometry.Z_normal a)
  let D := W ⊓ B₀
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hb2 : 2 < geometry.b d.radical := by omega
  have hl := path.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,hd])
  have hVQ := geometry.V_le_Q hb2 a path.start_color
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hVS := hVQ.trans hQS
  have hWS := hWV.trans hVS
  have hSW : S ≤ normalizer (W : Set (FreeAmalgam d.radical)) := localZSpan_normalized d.radical e a
  have hSB : S ≤ normalizer (B₀ : Set (FreeAmalgam d.radical)) :=
    Escape.Propagation.Rigidity.B_normalized hb2 a path.start_color
  have hSD : S ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (le_inf hSW hSB).trans inf_normalizer_le_normalizer_inf
  let hD : (D.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer (hWS.trans hSD)
  let := hD
  have hkill : ⁅W,Q d.radical a⁆ ≤ D := by
    apply le_inf (le_normalizer_iff_commutator_le_left.mp (hQS.trans hSW))
    intro x hx
    have hxc := ((commutator_mono hWV le_rfl).trans hfixed hx).2
    apply (mem_B_iff d.radical a (geometry.Z_normal a) hVS x).mpr
    refine ⟨hWV (le_normalizer_iff_commutator_le_left.mp (hQS.trans hSW) hx),?_⟩
    intro l hl
    have hc : ⁅l,x⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hxc l hl)
    rw [hc]
    exact one_mem _
  let hEA : IsElementaryAbelian 2 (W ⧸ D.subgroupOf W) :=
    elementary_quotient_of_omega W D ((commutator_mono le_rfl (hWV.trans hVQ)).trans hkill)
      (span_omega_one d.radical a e)
  let := hEA
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb4 path.start_color
  obtain ⟨σ,c,hcoord⟩ := BinaryConjugationSection.exists_descended_actor
    S W D hWS inf_le_left hSW hSD f hf (by
      intro s hs w hw
      have hsQ : (s : FreeAmalgam d.radical) ∈ Q d.radical a :=
        hfQ ▸ mem_map_of_mem S.subtype (show s ∈ f.ker from hs)
      rw [commutator_comm] at hkill
      exact hkill (commutator_mem_commutator hsQ hw))
  have hnotB : ¬ W ≤ B₀ := by
    intro hh
    have hi := h.replacement_path_moving_index_ge_field d path hb4
    have hu : U d.radical e ≤ B₀ :=
      (DistanceEight.U_le_Z d.radical e).trans ((Z_le_localZSpan d.radical e a).trans hh)
    rw [relIndex_eq_one.mpr hu] at hi
    exact (not_le_of_gt (Finite.one_lt_card (α := F))) hi
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hfaith : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases σ.normal_ker.eq_bot_or_eq_top with hk | hk
    · exact hk
    exfalso
    have hWB : ⁅W,Ltilde d.radical a⁆ ≤ B₀ := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro l hl w hw
      have hlS := Ltilde_le_stabilizer a hl
      have hs : (⟨l,hlS⟩ : S) ∈ (σ.comp f).ker := by
        change f ⟨l,hlS⟩ ∈ σ.ker
        rw [hk]
        exact mem_top _
      exact ((c.action_mem_ker_iff ⟨l,hlS⟩).mp hs w hw).2
    let := finite_stabilizer d.radical a
    let A := W.subgroupOf S
    let : A.Normal := normal_subgroupOf_of_le_normalizer hSW
    have hp : IsPGroup 2 A :=
      ((Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d)
        a path.start_color).to_le (hWV.trans hVQ)).comap_subtype
    have hid := congrArg (Subgroup.map S.subtype)
      (commutator_isPPerfect_idempotent (pResidual 2 S) A (isPPerfect_pResidual 2)
        hp le_normalizer_of_normal)
    have hAm : A.map S.subtype=W := map_subgroupOf_eq_of_le hWS
    simp only [map_commutator,hAm] at hid
    have hBZ : ⁅B₀,Ltilde d.radical a⁆ ≤ Z d.radical a := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro l hl b hb
      exact ((mem_B_iff d.radical a (geometry.Z_normal a) hVS b).mp hb).2 l hl
    have hWZ : ⁅W,Ltilde d.radical a⁆ ≤ Z d.radical a :=
      hid.symm.le.trans ((commutator_mono hWB le_rfl).trans hBZ)
    exact hnotB (radius_le_B_of_commutator geometry hb2 path.start_color W hWV hWZ)
  refine ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,?_⟩
  let W2 := localZSpan d.radical a e
  have hW2Q : W2 ≤ Q d.radical e := localZSpan_le_Q d.radical he hd.le hb2
  have hW2S : W2 ≤ S := hW2Q.trans
    (Q_le_stabilizer_of_dist_two d.radical e a he (by rw [SimpleGraph.dist_comm]; exact hd))
  obtain ⟨_,_,h2,h2Z,_,_⟩ := h.replacement_distance_four_normal_spans_of_radius_fixed d path hb hfixed
  have hder : ⁅W2,W2⁆ ≤ Q d.radical a :=
    ((commutator_mono le_rfl hW2Q).trans (h2.le.trans h2Z)).trans
      ((Z_le_VBall d.radical a 2).trans hVQ)
  exact elementary_image_of_omega S (Q d.radical a) W2 f hfQ hW2S hder
    (span_omega_one d.radical e a)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
