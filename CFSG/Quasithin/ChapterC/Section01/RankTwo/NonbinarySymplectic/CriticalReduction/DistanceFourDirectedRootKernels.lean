module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedFixedEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullKernelNormality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedFixedEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourKernelNormality

/-!
# Directed full-kernel escape for the same prescribed root selector

The source's actual first conjugator is oriented according to the selected
member. Its mixed full-kernel commutator vanishes by the same residual-orbit
argument on an actual forward extension of the transported original path.
Containment of the old kernel in the twisted kernel would make all THREE
retained generators normalize one small radius subgroup and force it into B.
The strict original B-index excludes this containment. Minimum distance then
constructs the twisted critical path and supplies its reciprocal field indices.

The internal imports retain the original forward-extension construction and
fixed-radius transport; no endpoint transitivity or omitted third seed is used.
Source: MS93 (5.12)(3), printed pp.926--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem prescribed_mixed_vanishing
    {geometry : Geometry d.radical} {a z u w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (haw : Adjacent d.radical a w) (huw : Adjacent d.radical u w)
    (r k : FreeAmalgam d.radical) (hr : r ∈ Ltilde d.radical a) (hk : k ∈ Ltilde d.radical a)
    (hru : act d.radical r (path.walk.getVert 2)=u)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ⁅Z d.radical u ⊓ Q d.radical (act d.radical k (path.walk.getVert 2)),
      Z d.radical (act d.radical k z) ⊓ Q d.radical a⁆=⊥ := by
  have hka : act d.radical k a=a := Ltilde_le_stabilizer a hk
  let p₀ := path.act k
  let p : CriticalPath d.radical geometry a (act d.radical k z) := {
    start_color := path.start_color
    walk := p₀.walk.copy hka rfl
    shortest := by
      rw [SimpleGraph.Walk.length_copy]
      exact p₀.shortest.trans (congrArg
        (fun b => (cosetGraph d.radical).dist b (act d.radical k z)) hka)
    critical := by simpa only [hka] using p₀.critical }
  have hp : p.walk.getVert 2=act d.radical k (path.walk.getVert 2) := by
    change (p₀.walk.copy hka rfl).getVert 2=_
    rw [SimpleGraph.Walk.getVert_copy]
    exact actWalk_getVert d.radical k path.walk 2
  obtain ⟨c,next,hnext⟩ := actual_forward_extension h d p hb
  let back : CriticalPath d.radical geometry a (next.walk.getVert 2) := {
    start_color := path.start_color
    walk := p.walk.copy rfl hnext.symm
    shortest := by rw [SimpleGraph.Walk.length_copy,hnext]; exact p.shortest
    critical := by simpa only [hnext] using p.critical }
  have hmid : back.walk.getVert 2=p.walk.getVert 2 := by
    change (p.walk.copy rfl hnext.symm).getVert 2=_
    rw [SimpleGraph.Walk.getVert_copy]
  have hy : act d.radical (k⁻¹*r) (p.walk.getVert 2)=u := by
    rw [hp,←act_mul,mul_inv_cancel_left]
    exact hru
  have hh := h.replacement_distance_four_fixed_kernel_commutator_eq_bot d next hb back hmid
    haw huw (k⁻¹*r) ((Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hk) hr) hy
    (radius_fixed_at d path.start_color next.start_color hfixed)
  rw [hnext,hp,h.replacement_distance_four_X_eq_Z d geometry hb p.end_color] at hh
  exact hh

private theorem prescribed_kernel_not_le_twist
    {geometry : Geometry d.radical} {a z u w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hfirst : back.walk.getVert 1=w)
    (haw : Adjacent d.radical a w) (huw : Adjacent d.radical u w)
    (r k : FreeAmalgam d.radical) (hr : r ∈ Ltilde d.radical a) (hk : k ∈ Ltilde d.radical a)
    (hru : act d.radical r (path.walk.getVert 2)=u)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical u))
    (hgen : (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
      Z d.radical (act d.radical k z)=stabilizer d.radical a) :
    ¬ Z d.radical u ⊓ Q d.radical (path.walk.getVert 2) ≤
      Z d.radical u ⊓ Q d.radical (act d.radical k (path.walk.getVert 2)) := by
  intro hcontain
  let e := path.walk.getVert 2
  let W := Z d.radical u ⊓ Q d.radical e
  let Y := W ⊔ Z d.radical a
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hb2 : 2 < geometry.b d.radical := by omega
  have hka : act d.radical k a=a := Ltilde_le_stabilizer a hk
  have he : color d.radical e=false := back.end_color
  have hZVu : Z d.radical u ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius haw huw)
  have hWQa : W ≤ Q d.radical a := inf_le_left.trans
    (hZVu.trans (geometry.V_le_Q hb2 a path.start_color))
  have hez : (cosetGraph d.radical).dist e z=2 := by
    dsimp only [e]
    rw [path.dist_end,path.length_eq_b,hb]
  have hWS : W ≤ stabilizer d.radical (act d.radical k z) :=
    (hcontain.trans inf_le_right).trans
      (Q_le_stabilizer_of_dist_le_two _ _
        (by rw [action_preserves_color]; exact he)
        (by rw [action_preserves_color]; exact path.end_color)
        (by rw [dist_act,hez]))
  have hcomm := prescribed_mixed_vanishing h d path hb haw huw r k hr hk hru hfixed
  have hfix : W ≤ centralizer
      ((Z d.radical (act d.radical k z) ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    hcontain.trans (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hle := h.replacement_critical_fixed_intersection_displacement d (path.act k)
    (by omega) W hWS (by simpa only [hka] using hWQa) (by simpa only [hka] using hfix)
  rw [hka] at hle
  have hRZa : ⁅Z d.radical a,Z d.radical (act d.radical k z)⁆ ≤ Z d.radical a := by
    have hh := critical_commutator_le_start_seed (path.act k)
    simpa only [hka] using hh
  have hZn : Z d.radical (act d.radical k z) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    apply normalizes_join_of_commutators _ W (Z d.radical a)
    · exact (hle.trans hRZa).trans le_sup_right
    · rw [commutator_comm]
      exact hRZa.trans le_sup_right
  obtain ⟨c,next,hnext⟩ := actual_forward_extension h d path hb
  let back₀ : CriticalPath d.radical geometry a (next.walk.getVert 2) := {
    start_color := path.start_color
    walk := path.walk.copy rfl hnext.symm
    shortest := by rw [SimpleGraph.Walk.length_copy,hnext]; exact path.shortest
    critical := by simpa only [hnext] using path.critical }
  have hmid₀ : back₀.walk.getVert 2=e := by
    change (path.walk.copy rfl hnext.symm).getVert 2=e
    rw [SimpleGraph.Walk.getVert_copy]
  have hfirsttwo := h.replacement_distance_four_fixed_full_kernel_normalized d next hb back₀
    hmid₀ haw huw r (Ltilde_le_stabilizer a hr) hru
    (radius_fixed_at d path.start_color next.start_color hfixed) back hfirst
  rw [hnext] at hfirsttwo
  have hLN : Ltilde d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    apply (Ltilde_le_stabilizer a).trans
    rw [←hgen]
    exact sup_le hfirsttwo hZn
  have hroot := (h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed path).2
  have hsmall : (Q d.radical a).relIndex (Z d.radical z)<Nat.card F^2 := by
    rw [hroot]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  have hSV : Z d.radical u ⊔ Z d.radical a ≤ V d.radical a := neighbor_seed_join_le_radius haw huw
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hSV.trans
      ((geometry.V_le_Q hb2 a path.start_color).trans (fun _ hx => hx.1)))) (inclusion_injective _)
  have hbound := h.replacement_root_neighbor_seed_index_le_cube d path hb4 haw huw hsmall
  have hiY : (Z d.radical a).relIndex Y ≤ Nat.card F^3 :=
    (relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
      ((neighbor_seed_join_index_le geometry (by omega) path.start_color haw huw).trans hbound)
  have hYB := h.replacement_small_radius_le_B d geometry hb2 path.start_color Y
    ((sup_le_sup inf_le_left le_rfl).trans hSV) hLN
    (hiY.trans_lt (Nat.pow_lt_pow_right (by exact Finite.one_lt_card) (by decide : 3<4)))
  have hWB : W ≤ B d.radical a (geometry.Z_normal a) := le_sup_left.trans hYB
  let := finite_Z d.radical u
  have hsmallZ := relIndex_le_of_le_left hWB (L := Z d.radical u) index_ne_zero_of_finite
  rw [inf_relIndex_left,
    (h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed back).1] at hsmallZ
  exact hmove.not_ge (((B d.radical a (geometry.Z_normal a)).relIndex_le_of_le_right
    (U_le_Z u) index_ne_zero_of_finite).trans hsmallZ)

/-- A failed prescribed seed budget forces directed full-kernel escape and
an actual twisted critical path for the same complete equal-root selector. -/
theorem Input.replacement_distance_four_prescribed_directed_root_kernels
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)))
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical (path.walk.getVert 1)).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ (path.walk.getVert 1)
      let c₁ := act d.radical g⁻¹ (path.walk.getVert 2)
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      let J₁ := Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
        (Q d.radical t₁) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical c₂) (Q d.radical c₂)
        (Q d.radical t₂) (Nat.card F^2)
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₁ : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₂ : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (((((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
        (stabilizer d.radical a).subtype : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ∃ back : CriticalPath d.radical geometry v (path.walk.getVert 2),
          back.walk.getVert 1 = w ∧
          (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
          ∃ r ∈ Ltilde d.radical a, ∃ k ∈ Ltilde d.radical a,
            act d.radical r (path.walk.getVert 2)=v ∧
            ((v=c₁ ∧ w=t₁ ∧ r=g⁻¹ ∧ k=x⁻¹) ∨
              (v=c₂ ∧ w=t₂ ∧ r=g⁻¹*x ∧ k=x)) ∧
            ((Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
              (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
                Z d.radical (act d.radical k z)=stabilizer d.radical a) ∧
            (¬ Z d.radical v ⊓ Q d.radical (path.walk.getVert 2) ≤
              Z d.radical v ⊓ Q d.radical (act d.radical k (path.walk.getVert 2))) ∧
            ∃ _companion : CriticalPath d.radical geometry v
                (act d.radical k (path.walk.getVert 2)),
              (Q d.radical (act d.radical k (path.walk.getVert 2))).relIndex (Z d.radical v)=Nat.card F ∧
              (Q d.radical v).relIndex
                (Z d.radical (act d.radical k (path.walk.getVert 2)))=Nat.card F := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
      hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,back,hfirst,hover⟩ :=
    h.replacement_distance_four_prescribed_equal_fixed_escape d path hb hfixed hequal hJm
  refine ⟨E,hE,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
    hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,back,hfirst,hover,?_⟩
  let e := path.walk.getVert 2
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  obtain ⟨r,hr,k,hk,hrv,horiented,hgen⟩ :
      ∃ r ∈ Ltilde d.radical a, ∃ k ∈ Ltilde d.radical a,
        act d.radical r e=v ∧
        ((v=act d.radical g⁻¹ e ∧ w=act d.radical g⁻¹ (path.walk.getVert 1) ∧ r=g⁻¹ ∧ k=x⁻¹) ∨
          (v=act d.radical x (act d.radical g⁻¹ e) ∧
            w=act d.radical x (act d.radical g⁻¹ (path.walk.getVert 1)) ∧ r=g⁻¹*x ∧ k=x)) ∧
        ((Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
            Z d.radical (act d.radical k z)=stabilizer d.radical a) := by
    rcases hwhich with ⟨hv,hw⟩ | ⟨hv,hw⟩
    · refine ⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,x⁻¹,(Ltilde d.radical a).inv_mem hx,
        hv.symm,Or.inl ⟨hv,hw,rfl,rfl⟩,?_⟩
      simpa only [hv,hw,Z_act,inv_inv] using hgen1
    · refine ⟨g⁻¹*x,(Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hg) hx,
        x,hx,?_,Or.inr ⟨hv,hw,rfl,rfl⟩,?_⟩
      · rw [act_mul]
        exact hv.symm
      · simpa only [hv,hw,Z_act] using hgen2
  have hra : act d.radical r a=a := Ltilde_le_stabilizer a hr
  have hka : act d.radical k a=a := Ltilde_le_stabilizer a hk
  have hmovev : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) := by
    rw [←hrv,movingIndex_act geometry (by omega) path.start_color r (Ltilde_le_stabilizer a hr)]
    exact hmove
  have hnot := prescribed_kernel_not_le_twist h d path hb back hfirst haw hvw r k hr hk
    hrv hfixed hmovev hgen
  have hescape : ¬ Z d.radical v ≤ Q d.radical (act d.radical k e) := by
    intro hh
    apply hnot
    exact le_inf inf_le_left (inf_le_left.trans hh)
  have hmin := criticalDistance_le d.radical v (geometry.exists_critical v back.start_color) hescape
  have hae : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hva : (cosetGraph d.radical).dist v a=2 := by
    rw [←hrv,←hra,dist_act,SimpleGraph.dist_comm]
    exact hae
  have hake : (cosetGraph d.radical).dist a (act d.radical k e)=2 := by
    rw [←hka,dist_act]
    exact hae
  have hupper := (cosetGraph_connected d.radical).dist_triangle (u:=v) (v:=a)
    (w:=act d.radical k e)
  rw [hva,hake] at hupper
  have hd : (cosetGraph d.radical).dist v (act d.radical k e)=
      criticalDistance d.radical v (geometry.exists_critical v back.start_color) := by
    rw [geometry.distance_constant v back.start_color] at hmin ⊢
    change geometry.b d.radical ≤ _ at hmin
    change _=geometry.b d.radical
    omega
  let companion : CriticalPath d.radical geometry v (act d.radical k e) :=
    CriticalPath.ofPair back.start_color ⟨hd,hescape⟩
  obtain ⟨hi,hi'⟩ := h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed companion
  exact ⟨r,hr,k,hk,hrv,horiented,hgen,hnot,companion,hi,hi'⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
