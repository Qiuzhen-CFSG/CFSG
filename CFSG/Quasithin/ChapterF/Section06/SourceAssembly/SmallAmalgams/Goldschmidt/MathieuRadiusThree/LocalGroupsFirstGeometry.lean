module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelations
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth

/-!
# The first Mathieu endpoint's labeled generator frame

Four labels on the selected track and one label on the adjoining branch
supply the six involutions used in the first-endpoint presentation. The
neighbor-product identity identifies the off-track inner label. Three
literal six-edge paths then give the conjugation formulas and the central
square of the product of the two end generators. Conjugation transports
this frame to every vertex of the labeled type.

Source: Goldschmidt (1980), (6.12.5)--(6.12.6), printed pp.404--406.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open scoped commutatorElement
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- The literal involutions used to recognize the first Mathieu endpoint.
The center and the two inner labels generate the source eight-group. -/
structure FirstGeometry (d : CanonicalLabelSetup F s) (a : RankTwo.Vertex F)
    (u v A B C : G) : Prop where
  generators : d.labelBall a 2 = closure ({d.label a, u, v} : Set G)
  u_sq : u ^ 2 = 1
  v_sq : v ^ 2 = 1
  A_sq : A ^ 2 = 1
  B_sq : B ^ 2 = 1
  C_sq : C ^ 2 = 1
  z_sq : d.label a ^ 2 = 1
  uv : Commute u v
  zu : Commute (d.label a) u
  zv : Commute (d.label a) v
  zA : Commute (d.label a) A
  zB : Commute (d.label a) B
  zC : Commute (d.label a) C
  Au : A * u * A⁻¹ = u
  Av : A * v * A⁻¹ = d.label a * u * v
  Bu : B * u * B⁻¹ = d.label a * u * v
  Bv : B * v * B⁻¹ = v
  Cu : C * u * C⁻¹ = u
  Cv : C * v * C⁻¹ = u * v
  AC : (A * C) ^ 2 = d.label a
  A_mem : A ∈ d.labelBall a 4
  B_mem : B ∈ d.labelBall a 4
  C_mem : C ∈ d.labelBall a 4
  A_label : ∃ b : RankTwo.Vertex F, b.type = d.side ∧ (RankTwo.graph F).dist a b = 4 ∧ A = d.label b
  B_label : ∃ b : RankTwo.Vertex F, b.type = d.side ∧ (RankTwo.graph F).dist a b = 4 ∧ B = d.label b
  C_label : ∃ b : RankTwo.Vertex F, b.type = d.side ∧ (RankTwo.graph F).dist a b = 4 ∧ C = d.label b

private theorem exists_forward (h : CubicTreeAction F) (v a : RankTwo.Vertex F) :
    ∃ u, (RankTwo.graph F).Adj v u ∧ u ≠ a := by
  by_contra! hh
  have hi : Subsingleton ((RankTwo.graph F).neighborSet v) := ⟨fun x y =>
    Subtype.ext ((hh x x.property).trans (hh y y.property).symm)⟩
  have hc : Nat.card ((RankTwo.graph F).neighborSet v) ≤ 1 := by
    let f : (RankTwo.graph F).neighborSet v → Unit := fun _ => ()
    simpa using Nat.card_le_card_of_injective f (fun x y _ => Subsingleton.elim _ _)
  rw [h.card_neighbor v] at hc
  omega

private theorem path_dist (h : CubicTreeAction F) {n : ℕ} {a : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) n a) (hp : p.Nonbacktracking) :
    (RankTwo.graph F).dist a p.endpoint = n :=
  geodesic_of_nonbacktracking_of_cycle_bound h.tree.connected
    (N := 2*n) (fun _ _ hc => (h.tree.isAcyclic _ hc).elim) p hp (by omega)

private theorem six_comm {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) {a : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) 6 a) (hp : p.Nonbacktracking)
    (ha : a.type = d.side) :
    ⁅d.label a,d.label p.endpoint⁆ =
      d.label (p.toWalk.getVert 2) * d.label (p.toWalk.getVert 4) :=
  r.six_arc a p.endpoint p.toWalk ha
    (isPath_of_nonbacktracking_of_cycle_bound (N := 7)
      (fun _ _ hc => (h.action.tree.isAcyclic _ hc).elim) p hp (by decide)) rfl

private theorem commute_conj {x y : G} (h : Commute x y) : x*y*x⁻¹=y := by
  rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem comm_conj {x y z : G} (hc : ⁅x,y⁆ = z) : x*y*x⁻¹=z*y := by
  have he := congrArg (fun q : G => q*y) hc
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using he

private theorem exists_firstGeometry_center {h : LargeTreeSource F s}
    {d : CanonicalLabelSetup F s} (r : LocalRelations h d) (hr : d.radius = 3) :
    ∃ u v A B C : G, FirstGeometry d (d.track.vertex d.center) u v A B C := by
  let t := h.action.toCubicTreeAction
  let p : ℤ → RankTwo.Vertex F := fun i => d.track.vertex (d.center+i)
  have hinj : Function.Injective p := by
    intro i j hij
    have hh := d.track.injective hij
    omega
  have hadj (i : ℤ) : (RankTwo.graph F).Adj (p i) (p (i+1)) := by
    simpa only [p, add_assoc] using d.track.adjacent (d.center+i)
  have hne {i j : ℤ} (hij : i ≠ j) : p i ≠ p j := fun hh => hij (hinj hh)
  have hp0 : p 0 = d.track.vertex d.center := by simp only [p, add_zero]
  have htype (k : ℤ) : (p (2*k)).type = d.side := d.shifted_type k
  have ht0 : (p 0).type = d.side := by simpa using htype 0
  have htm2 : (p (-2)).type = d.side := by simpa using htype (-1)
  have htp2 : (p 2).type = d.side := by simpa using htype 1
  have htm4 : (p (-4)).type = d.side := by simpa using htype (-2)
  have htp4 : (p 4).type = d.side := by simpa using htype 2
  have hdist (i : ℤ) (n : ℕ) : (RankTwo.graph F).dist (p i) (p (i+n)) = n := by
    have hh := path_dist t (d.track.arc (d.center+i) n) (d.track.arc_nonbacktracking _ _)
    simpa only [Track.arc_endpoint, p, add_assoc] using hh
  have hbound {i j : ℤ} (hn : (i-j).natAbs ≤ 4) :
      (RankTwo.graph F).dist (p i) (p j) ≤ 4 := by
    by_cases hij : i ≤ j
    · have hh := hdist i (j-i).toNat
      have he : i + ((j-i).toNat : ℤ) = j := by omega
      rw [he] at hh
      rw [hh]
      omega
    · rw [SimpleGraph.dist_comm]
      have hh := hdist j (i-j).toNat
      have he : j + ((i-j).toNat : ℤ) = i := by omega
      rw [he] at hh
      rw [hh]
      omega
  obtain ⟨f,hfc⟩ := d.exists_radiusThree_foldedBranchFrame t hr
  have hc0 : f.c 0 = p (-2) := by simp only [hfc, p, sub_eq_add_neg, Matrix.cons_val_zero]
  have he0 : (f.e 0).val = p (-1) := by
    apply DistanceTwoGeometry.midpoint_unique t.tree.isAcyclic (f.c_ne_center 0).symm
      (f.e 0).property (f.c_adj 0)
    · simpa [hp0] using (hadj (-1)).symm
    · rw [hc0]
      exact (by simpa using (hadj (-2)).symm)
  let w := f.d 0
  have hw : (RankTwo.graph F).Adj (p (-1)) w := by simpa only [← he0] using f.d_adj 0
  have hw0 : w ≠ p 0 := by simpa only [hp0] using f.d_ne_center 0
  have hwu : w ≠ p (-2) := by simpa only [← hc0] using (f.c_ne_d 0).symm
  obtain ⟨q,hq,hqn⟩ := exists_forward t w (p (-1))
  obtain ⟨c,hc,hcn⟩ := exists_forward t q w
  let pc : BasedWalk (RankTwo.graph F) 4 (p 0) :=
    ⟨⟨p (-1),(by simpa using (hadj (-1)).symm)⟩,⟨⟨w,hw⟩,⟨⟨q,hq⟩,⟨⟨c,hc⟩,PUnit.unit⟩⟩⟩⟩
  have hpc : pc.Nonbacktracking := ⟨hw0,hqn,hcn,trivial⟩
  have hdc : (RankTwo.graph F).dist (p 0) c = 4 := path_dist t pc hpc
  have htc : c.type = d.side :=
    ((RankTwo.even_dist_iff F t.generated _ _).mp (by rw [hdc]; decide)).symm.trans
      (ht0)
  have htw : w.type = d.side := (f.d_type t 0).trans d.center_type
  let z := d.label (p 0)
  let u := d.label (p (-2))
  let v := d.label (p 2)
  let A := d.label (p (-4))
  let B := d.label (p 4)
  let C := d.label c
  have hsquare (k : ℤ) : d.label (p (2*k)) ^ 2 = 1 := by
    simpa only [d.order_two _ (htype k)] using pow_orderOf_eq_one (d.label (p (2*k)))
  have hCsq : C ^ 2 = 1 := by
    simpa only [C, d.order_two _ htc] using pow_orderOf_eq_one (d.label c)
  have hcomm (i j : ℤ) (hn : (2*i-2*j).natAbs ≤ 4) :
      Commute (d.label (p (2*i))) (d.label (p (2*j))) :=
    d.labels_commute_of_dist_le (htype i) (htype j)
      (by have := hbound hn; omega) (by have := hbound hn; have := h.five_le; omega)
  have hu2 : u ^ 2 = 1 := by simpa [u] using hsquare (-1)
  have hv2 : v ^ 2 = 1 := by simpa [v] using hsquare 1
  have hA2 : A ^ 2 = 1 := by simpa [A] using hsquare (-2)
  have hB2 : B ^ 2 = 1 := by simpa [B] using hsquare 2
  have hz2 : z ^ 2 = 1 := by simpa [z] using hsquare 0
  have huv : Commute u v := by simpa [u,v] using hcomm (-1) 1 (by decide)
  have hzu : Commute z u := by simpa [z,u] using hcomm 0 (-1) (by decide)
  have hzv : Commute z v := by simpa [z,v] using hcomm 0 1 (by decide)
  have hzA : Commute z A := by simpa [z,A] using hcomm 0 (-2) (by decide)
  have hzB : Commute z B := by simpa [z,B] using hcomm 0 2 (by decide)
  have hAu : Commute A u := by simpa [A,u] using hcomm (-2) (-1) (by decide)
  have hBv : Commute B v := by simpa [B,v] using hcomm 2 1 (by decide)
  have hzw : d.label w = z*u := by
    have hh := d.neighbor_product (p (-1)) (p 0) (p (-2)) w
      (by simpa using hadj (-1)) (by simpa using (hadj (-2)).symm) hw
      (hne (by decide)) hw0.symm hwu.symm (ht0)
    have hh' := mul_eq_one_iff_eq_inv.mp hh
    exact (d.label_inv htw).symm.trans hh'.symm
  have hAC : ⁅A,C⁆ = z := by
    let ac : BasedWalk (RankTwo.graph F) 6 (p (-4)) :=
      ⟨⟨p (-3),by simpa using hadj (-4)⟩,⟨⟨p (-2),by simpa using hadj (-3)⟩,⟨⟨p (-1),by simpa using hadj (-2)⟩,
        ⟨⟨w,hw⟩,⟨⟨q,hq⟩,⟨⟨c,hc⟩,PUnit.unit⟩⟩⟩⟩⟩⟩
    have hac : ac.Nonbacktracking :=
      ⟨hne (by decide),hne (by decide),hwu,hqn,hcn,trivial⟩
    have hh : ⁅A,C⁆ = u*d.label w := six_comm r ac hac (htm4)
    rw [hh,hzw,← mul_assoc,hzu.symm.eq,mul_assoc,
      show u*u=1 from d.label_mul_self (htm2),mul_one]
  have hAv : ⁅A,v⁆ = u*z := by
    let av : BasedWalk (RankTwo.graph F) 6 (p (-4)) :=
      ⟨⟨p (-3),by simpa using hadj (-4)⟩,⟨⟨p (-2),by simpa using hadj (-3)⟩,⟨⟨p (-1),by simpa using hadj (-2)⟩,
        ⟨⟨p 0,by simpa using hadj (-1)⟩,⟨⟨p 1,hadj 0⟩,⟨⟨p 2,hadj 1⟩,PUnit.unit⟩⟩⟩⟩⟩⟩
    exact six_comm r av ⟨hne (by decide),hne (by decide),hne (by decide),
      hne (by decide),hne (by decide),trivial⟩ (htm4)
  have hBu : ⁅B,u⁆ = v*z := by
    let bu : BasedWalk (RankTwo.graph F) 6 (p 4) :=
      ⟨⟨p 3,(hadj 3).symm⟩,⟨⟨p 2,(hadj 2).symm⟩,⟨⟨p 1,(hadj 1).symm⟩,
        ⟨⟨p 0,(hadj 0).symm⟩,⟨⟨p (-1),(by simpa using (hadj (-1)).symm)⟩,
          ⟨⟨p (-2),(by simpa using (hadj (-2)).symm)⟩,PUnit.unit⟩⟩⟩⟩⟩⟩
    exact six_comm r bu ⟨hne (by decide),hne (by decide),hne (by decide),
      hne (by decide),hne (by decide),trivial⟩ (htp4)
  have hCv : ⁅C,v⁆ = u := by
    let cv : BasedWalk (RankTwo.graph F) 6 c :=
      ⟨⟨q,hc.symm⟩,⟨⟨w,hq.symm⟩,⟨⟨p (-1),hw.symm⟩,
        ⟨⟨p 0,by simpa using hadj (-1)⟩,⟨⟨p 1,hadj 0⟩,⟨⟨p 2,hadj 1⟩,PUnit.unit⟩⟩⟩⟩⟩⟩
    have hcv : cv.Nonbacktracking := ⟨hcn.symm,hqn.symm,hw0.symm,
      hne (by decide),hne (by decide),trivial⟩
    have hh : ⁅C,v⁆ = d.label w*z := six_comm r cv hcv htc
    rw [hh,hzw,hzu.eq,mul_assoc,
      show z*z=1 from d.label_mul_self (ht0),mul_one]
  have hCu : Commute C u := by
    let cu : BasedWalk (RankTwo.graph F) 4 c :=
      ⟨⟨q,hc.symm⟩,⟨⟨w,hq.symm⟩,⟨⟨p (-1),hw.symm⟩,
        ⟨⟨p (-2),(by simpa using (hadj (-2)).symm)⟩,PUnit.unit⟩⟩⟩⟩
    have hh : (RankTwo.graph F).dist c (p (-2)) = 4 :=
      path_dist t cu ⟨hcn.symm,hqn.symm,hwu.symm,trivial⟩
    exact d.labels_commute_of_dist_le htc (htm2) (by omega)
      (by have := h.five_le; omega)
  refine ⟨u,v,A,B,C,?_⟩
  rw [← hp0]
  refine ⟨?_,hu2,hv2,hA2,hB2,hCsq,hz2,huv,hzu,hzv,hzA,hzB,?_,
    commute_conj hAu,?_,?_,commute_conj hBv,commute_conj hCu,comm_conj hCv,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := d.radiusThree_radiusTwo_track_generators t hr (d.radiusThree_track_commutator h hr)
    rw [← hp0] at hh
    rw [hh]
    congr 1
    ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_range,Fin.exists_fin_succ,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.exists_fin_zero,or_false]
    dsimp only [u,v,p]
    simp only [sub_eq_add_neg]
    aesop
  · exact d.labels_commute_of_dist_le (ht0) htc (by omega)
      (by have := h.five_le; omega)
  · rw [comm_conj hAv,hzu.symm.eq]
  · rw [comm_conj hBu,hzv.symm.eq,mul_assoc,
      huv.symm.eq,← mul_assoc]
  · simpa only [A,C,z,commutatorElement_def,d.label_inv htm4,d.label_inv htc,
      pow_two,mul_assoc] using hAC
  · exact d.label_mem_labelBall (htm4) (hbound (by decide))
  · exact d.label_mem_labelBall (htp4) (hbound (by decide))
  · exact d.label_mem_labelBall htc hdc.le
  · refine ⟨p (-4),htm4,?_,rfl⟩
    rw [SimpleGraph.dist_comm]
    simpa using hdist (-4) 4
  · exact ⟨p 4,htp4,by simpa using hdist 0 4,rfl⟩
  · exact ⟨c,htc,hdc,rfl⟩

/-- Transport preserves the literal labeled generator frame. -/
theorem FirstGeometry.conjugate {d : CanonicalLabelSetup F s}
    {a : RankTwo.Vertex F} {u v A B C : G}
    (R : FirstGeometry d a u v A B C) (ha : a.type = d.side) (g : G) :
    FirstGeometry d (g • a) ((MulAut.conj g) u) ((MulAut.conj g) v)
      ((MulAut.conj g) A) ((MulAut.conj g) B) ((MulAut.conj g) C) := by
  let φ := MulAut.conj g
  have hz : φ (d.label a) = d.label (g • a) := (d.conjugate g a ha).symm
  refine ⟨?_,?_,?_,?_,?_,?_,?_,R.uv.map φ,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [← d.labelBall_map_conj a 2 g,R.generators,MonoidHom.map_closure]
    simp only [Set.image_insert_eq,Set.image_singleton]
    rw [← hz]
    rfl
  · simpa only [map_pow,map_one] using congrArg φ R.u_sq
  · simpa only [map_pow,map_one] using congrArg φ R.v_sq
  · simpa only [map_pow,map_one] using congrArg φ R.A_sq
  · simpa only [map_pow,map_one] using congrArg φ R.B_sq
  · simpa only [map_pow,map_one] using congrArg φ R.C_sq
  · simpa only [map_pow,map_one,hz] using congrArg φ R.z_sq
  · simpa only [hz] using R.zu.map φ
  · simpa only [hz] using R.zv.map φ
  · simpa only [hz] using R.zA.map φ
  · simpa only [hz] using R.zB.map φ
  · simpa only [hz] using R.zC.map φ
  · simpa only [map_mul,map_inv] using congrArg φ R.Au
  · simpa only [map_mul,map_inv,hz] using congrArg φ R.Av
  · simpa only [map_mul,map_inv,hz] using congrArg φ R.Bu
  · simpa only [map_mul,map_inv] using congrArg φ R.Bv
  · simpa only [map_mul,map_inv] using congrArg φ R.Cu
  · simpa only [map_mul,map_inv] using congrArg φ R.Cv
  · simpa only [map_mul,map_pow,hz] using congrArg φ R.AC
  · rw [← d.labelBall_map_conj a 4 g]
    exact ⟨A,R.A_mem,rfl⟩
  · rw [← d.labelBall_map_conj a 4 g]
    exact ⟨B,R.B_mem,rfl⟩
  · rw [← d.labelBall_map_conj a 4 g]
    exact ⟨C,R.C_mem,rfl⟩
  · obtain ⟨b,hb,hd,hA⟩ := R.A_label
    refine ⟨g • b,hb,(RankTwo.dist_smul F g a b).trans hd,?_⟩
    rw [hA]
    exact (d.conjugate g b hb).symm
  · obtain ⟨b,hb,hd,hB⟩ := R.B_label
    refine ⟨g • b,hb,(RankTwo.dist_smul F g a b).trans hd,?_⟩
    rw [hB]
    exact (d.conjugate g b hb).symm
  · obtain ⟨b,hb,hd,hC⟩ := R.C_label
    refine ⟨g • b,hb,(RankTwo.dist_smul F g a b).trans hd,?_⟩
    rw [hC]
    exact (d.conjugate g b hb).symm

/-- The first-endpoint frame exists in the actual source group at every
vertex of the labeled type. No quotient or model marking is assumed. -/
theorem LocalRelations.exists_firstGeometry {h : LargeTreeSource F s}
    {d : CanonicalLabelSetup F s} (r : LocalRelations h d) (hr : d.radius = 3)
    (a : RankTwo.Vertex F) (ha : a.type = d.side) :
    ∃ u v A B C : G, FirstGeometry d a u v A B C := by
  obtain ⟨u,v,A,B,C,R⟩ := exists_firstGeometry_center r hr
  obtain ⟨g,hg⟩ := (RankTwo.same_orbit_iff F (d.track.vertex d.center) a).mpr
    (d.center_type.trans ha.symm)
  exact ⟨_,_,_,_,_,hg ▸ R.conjugate d.center_type g⟩

private theorem three_involution_swap (σ : Equiv.Perm (Fin 3))
    (hs : σ ^ 2 = 1) (hn : σ ≠ 1) : σ.IsSwap := by
  let : Fintype (Equiv.Perm (Fin 3)) := fintypePerm
  revert σ
  simp only [Equiv.Perm.IsSwap]
  decide

/-- Every label at distance four induces a transposition on the three
branches, with respect to any branch frame. -/
theorem label_branchAction_isSwap (h : LargeTreeSource F s)
    (d : CanonicalLabelSetup F s) (hr : d.radius = 3)
    {a b : RankTwo.Vertex F} (ha : a.type = d.side) (hb : b.type = d.side)
    (hab : (RankTwo.graph F).dist a b = 4) (f : BranchFrame F a)
    (k : RankTwo.stabilizer F a) (hk : k.val = d.label b) :
    (f.branchAction k).IsSwap := by
  obtain ⟨g,hga,hgb⟩ := h.exists_track_pair d ha (by rw [hab]; exact (by have := h.five_le; omega))
  rw [hab] at hgb
  have hconj : k.val = (MulAut.conj g) (d.label (d.track.vertex (d.center+2*2))) := by
    rw [hk,← hgb]
    exact d.conjugate g _ (d.shifted_type 2)
  apply three_involution_swap
  · have hks : k ^ 2 = 1 := by
      apply Subtype.ext
      change k.val ^ 2 = 1
      rw [hk]
      simpa only [d.order_two b hb] using pow_orderOf_eq_one (d.label b)
    rw [← map_pow,hks,map_one]
  · intro he
    have hadj : (RankTwo.graph F).Adj a (g • d.track.vertex (d.center-1)) := by
      rw [← hga]
      apply (translationGraphIso F g).toHom.map_adj
      convert (d.track.adjacent (d.center-1)).symm using 1
      congr 1
      omega
    obtain ⟨i,hi⟩ := f.e.surjective ⟨_,hadj⟩
    have hi' : (f.e i).val = g • d.track.vertex (d.center-1) := congrArg Subtype.val hi
    have hh := f.branchAction_eval k i
    rw [he] at hh
    simp only [Equiv.Perm.one_apply] at hh
    rw [hi',hconj] at hh
    have hfix : d.label (d.track.vertex (d.center+2*2)) •
        d.track.vertex (d.center-1) = d.track.vertex (d.center-1) := by
      apply (MulAction.toPerm g).injective
      change g • (d.label (d.track.vertex (d.center+2*2)) •
        d.track.vertex (d.center-1)) = g • d.track.vertex (d.center-1)
      simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using hh.symm
    have hf := (d.shifted_fixed_iff 2 (d.center-1)).mp hfix
    rw [hr] at hf
    omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
