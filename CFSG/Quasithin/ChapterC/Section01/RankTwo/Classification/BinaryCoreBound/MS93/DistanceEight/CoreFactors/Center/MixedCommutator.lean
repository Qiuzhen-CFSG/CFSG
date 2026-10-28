module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.NeighborMoving
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.MovingFirst

/-!
# A binary error bound for the distance-eight mixed commutator

The neighboring first hat has displacement in H at its own vertex under
that vertex kernel. The source moving-neighbor relation puts this H in
U at alpha. Thus the original core intersected with the neighboring kernel
contributes nothing modulo Vcirc at alpha. Its index in the core is at
most four, by the literal edge-kernel index from Earlier.

The central commutator with the neighboring first hat consequently defines
at most four homomorphism rows in any quotient of Z killing Vcirc. The
canonical quotient Z/(Z intersect Vcirc) is one such target. These are
actual commutator rows, with both their formula and their kernel retained.
The stabilizer-span adapter connects a bound on this seed to the whole
second hat and hence to the separate elementarity consumer.

The neighboring moving intersection has no error inside its own Z-layer:
its natural intersection with the original Z is precisely the original H,
and the neighboring H lies in the original U. The edge index bounds the
remaining error by two. Conjugation at alpha is trivial modulo Vcirc, so
the entire second-hat/core commutator still has image of order at most two.

The remaining geometric obligation is to eliminate that possible binary
error. This module does not prove its vanishing or the full mixed bound;
an image of order at most two need not be trivial.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1), (4.5.3)(i)--(iii),
printed pp.896--898, toward the collection in (4.5)(v), printed p.895.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open PathCentrality Higher NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

omit [Finite M] in
private theorem neighboring_first_le_Q (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R)) :
    hatV R (p.walk.getVert 6) (p.walk.getVert 8) ≤ Q R (alpha R) := by
  let path := Early.Orbit.SourceApplications.higherPath geometry p
  exact (Escape.Initial.Natural.conjugatesIn_contains _ (stabilizer R (alpha R))).trans
    ((hatW_le_radius R path.two_step_distances.1.le path.two_step_distances.2.1.le).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q (alpha R) rfl 4
        (by rw [earlier.distance]; decide)))

omit [Finite M] in
/-- Closing the actual seed commutator closes its entire stabilizer span.
The seed estimate remains a geometric premise. -/
theorem second_core_commutator_le_of_neighboring_first
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (hseed : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),core R (alpha R)⁆ ≤
      Vcirc R (alpha R)) :
    ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),core R (alpha R)⁆ ≤
      Vcirc R (alpha R) := by
  let P := stabilizer R (alpha R)
  let K := core R (alpha R)
  let D := Vcirc R (alpha R)
  have hAC : hatV R (p.walk.getVert 6) (p.walk.getVert 8) ≤
      commutatorPreimage P K D :=
    le_commutatorPreimage ((neighboring_first_le_Q earlier p).trans (fun _ hx => hx.1)) hseed
  have hPC : P ≤ normalizer (commutatorPreimage P K D) :=
    commutatorPreimage_normalized P K D P (Vcirc_normalized _) P.le_normalizer
      (DistanceTwo.core_normalized _) (Vcirc_normalized _)
  have hspan : hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ≤
      commutatorPreimage P K D := by
    apply iSup_le
    intro g
    exact (map_mono hAC).trans
      (mem_normalizer_iff_map_conj_eq.mp (hPC (P.inv_mem g.property))).le
  exact (commutator_mono hspan le_rfl).trans
    (commutator_commutatorPreimage_le P K D (Vcirc_normalized _))

/-- The kernel of the neighboring action has displacement in the original natural layer. -/
theorem neighboring_first_core_kernel_commutator (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      core R (alpha R) ⊓ Q R (p.walk.getVert 6)⁆ ≤ U R (alpha R) := by
  have hc := p.even_color (i := 6) (by decide) (by decide)
  have hd := p.even_color (i := 8) (by decide) (by decide)
  have hm := p.moving_neighbors source common earlier (i := 6)
    (by decide) (by decide) (by decide)
  have hseed := Early.Orbit.Source.HatIdentity.Preliminary.hatV_commutator_le_H
    common earlier hd hc
    (adjacent_symm R (p.adjacent (i := 7) (by decide)))
    (p.adjacent (i := 6) (by decide)) hm.2
  have hHU := Early.Orbit.H_le_neighbor_U common earlier hc hm.1
  have hHU' : H R (p.walk.getVert 6) ≤ U R (alpha R) := by
    simpa only [show 6 - 2 = 4 by decide, p.center_eq] using hHU
  exact (commutator_mono le_rfl inf_le_right).trans (hseed.trans hHU')

/-- Only an image of order at most four remains after the neighboring kernel. -/
theorem core_neighbor_kernel_index_le_four (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R)) :
    (Q R (p.walk.getVert 6)).relIndex (core R (alpha R)) ≤ 4 := by
  have hat : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using p.adjacent (i := 4) (by decide)
  have hct : Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) :=
    adjacent_symm R (p.adjacent (i := 5) (by decide))
  have ht : color R (p.walk.getVert 5) = true := by
    have hn := adjacent_color_ne R hat
    have ha : color R (alpha R) = false := rfl
    cases h : color R (p.walk.getVert 5) <;> simp_all
  have hK : core R (alpha R) ≤ Q R (p.walk.getVert 5) :=
    (DistanceTwo.core_le_Q _).trans (Q_le_adjacent_h R ht hat)
  have hi := earlier.edge_Q_index _ _ (p.even_color (i := 6) (by decide) (by decide)) hct
  exact (relIndex_le_of_le_right hK (by rw [hi]; decide)).trans hi.le

/-- Modulo the moving layer, the neighboring first hat has at most four
commutator rows under the original core. -/
theorem neighboring_core_error_rows
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R))
    {E : Type*} [CommGroup E] (q : Z R (alpha R) →* E)
    (hkill : ∀ z : Z R (alpha R), (z : FreeAmalgam R) ∈ Vcirc R (alpha R) → q z = 1) :
    ∃ row : core R (alpha R) →*
        (hatV R (p.walk.getVert 6) (p.walk.getVert 8) →* E),
      (∀ k a, row k a = q ⟨⁅(k : FreeAmalgam R),(a : FreeAmalgam R)⁆,
        (show ⁅core R (alpha R),hatV R (p.walk.getVert 6) (p.walk.getVert 8)⁆ ≤
            Z R (alpha R) from by
          rw [commutator_comm]
          exact (neighboring_first_core_commutator common earlier p).trans inf_le_right)
            (commutator_mem_commutator k.property a.property)⟩) ∧
      (Q R (p.walk.getVert 6)).subgroupOf (core R (alpha R)) ≤ row.ker ∧
      Nat.card row.range ≤ 4 := by
  let K := core R (alpha R)
  let A := hatV R (p.walk.getVert 6) (p.walk.getVert 8)
  let Z₀ := Z R (alpha R)
  have hKA : ⁅K,A⁆ ≤ Z₀ := by
    rw [commutator_comm]
    exact (neighboring_first_core_commutator common earlier p).trans inf_le_right
  have hAQ : A ≤ Q R (alpha R) := neighboring_first_le_Q earlier p
  have hZQ := commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes (alpha R) rfl)
  let raw (k : K) : A →* Z₀ := {
    toFun a := ⟨⁅(k : FreeAmalgam R),(a : FreeAmalgam R)⁆,
      hKA (commutator_mem_commutator k.property a.property)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' a b := by
      apply Subtype.ext
      change ⁅(k : FreeAmalgam R),(a : FreeAmalgam R) * b⁆ =
        ⁅(k : FreeAmalgam R),(a : FreeAmalgam R)⁆ * ⁅(k : FreeAmalgam R),(b : FreeAmalgam R)⁆
      have hc := hZQ (hKA (commutator_mem_commutator k.property b.property)) a (hAQ a.property)
      rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc _ (a : FreeAmalgam R),hc]
      group }
  let row : K →* (A →* E) := {
    toFun k := q.comp (raw k)
    map_one' := by
      ext a
      change q ⟨⁅(1 : FreeAmalgam R),(a : FreeAmalgam R)⁆,_⟩ = 1
      rw [show (⟨⁅(1 : FreeAmalgam R),(a : FreeAmalgam R)⁆,_⟩ : Z₀) = 1 from
        Subtype.ext (by simp),map_one]
    map_mul' k l := by
      ext a
      have he : raw (k*l) a = raw l a * raw k a := by
        apply Subtype.ext
        change ⁅(k : FreeAmalgam R) * l,(a : FreeAmalgam R)⁆ =
          ⁅(l : FreeAmalgam R),(a : FreeAmalgam R)⁆ * ⁅(k : FreeAmalgam R),(a : FreeAmalgam R)⁆
        have hc := hZQ (hKA (commutator_mem_commutator l.property a.property)) k
          (DistanceTwo.core_le_Q _ k.property)
        rw [commutatorElement_mul_left_eq_conj_mul,hc,mul_inv_cancel_right]
      change q (raw (k*l) a) = q (raw k a) * q (raw l a)
      rw [he,map_mul,mul_comm] }
  have hker : (Q R (p.walk.getVert 6)).subgroupOf K ≤ row.ker := by
    intro k hk
    apply MonoidHom.mem_ker.mpr
    ext a
    apply hkill
    have hbound := neighboring_first_core_kernel_commutator common earlier p
    rw [commutator_comm] at hbound
    exact (commutator_mono (Z_le_VBall R _ 2) le_rfl)
      (hbound (commutator_mem_commutator ⟨k.property,hk⟩ a.property))
  refine ⟨row,fun _ _ => rfl,hker,?_⟩
  let := DistanceTwo.finite_core (R := R) (alpha R)
  rw [← index_ker]
  have hi : row.ker.index ≤ ((Q R (p.walk.getVert 6)).subgroupOf K).index := by
    simpa only [relIndex_top_right] using relIndex_le_of_le_left (L := ⊤) hker
      (by rw [relIndex_top_right]; exact index_ne_zero_of_finite)
  exact hi.trans (core_neighbor_kernel_index_le_four earlier p)

private theorem moving_inf_Z_at (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {c : Vertex R} (hc : color R c = false) :
    Vcirc R c ⊓ Z R c = U R c ⊔ H R c := by
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) rfl
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R hc
  have he : act R g (alpha R) = c := by
    rw [hg]
    change mVertex R (1*g) = mVertex R g
    rw [one_mul]
  have h := congrArg (fun A : Subgroup (FreeAmalgam R) =>
    A.map (MulAut.conj g⁻¹).toMonoidHom) (moving_inf_Z_eq_U_sup_H common earlier p)
  rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective, Subgroup.map_sup,
    ← Vcirc_act, ← Z_act, ← U_act, ← H_act, he] at h
  exact h

/-- At a moving pair, the natural group meets the opposite Z in exactly its H. -/
theorem natural_inf_neighbor_Z_eq_H (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hm : c ∈ Escape.movingNeighbors geometry a) :
    U R c ⊓ Z R a = H R a := by
  let J := U R c ⊓ Z R a
  have hHU : H R a ≤ U R c := Early.Orbit.H_le_neighbor_U common earlier ha hm
  have hHZ := H_le_Z_of_central common ha (earlier.centrality a ha)
  have hHJ : H R a ≤ J := le_inf hHU hHZ
  let : Finite (U R c) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at c hc]; decide)
  let : Finite J := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hproper : J ≠ U R c := by
    intro heq
    have hUZ : U R c ≤ Z R a := heq ▸ (show J ≤ Z R a from inf_le_right)
    have hQa : Q R a ≤ stabilizer R c := Q_le_stabilizer_of_dist_two R a c ha hm.1
    have hcent : Z R c ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
      rw [(LocalCommutator.naturalStructure common).decomposition_at c hc]
      exact sup_le
        (hUZ.trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)))
        (inf_le_right.trans (centralizer_le hQa))
    have hzero : H R a = ⊥ := le_bot_iff.mp
      ((Early.Orbit.H_le_displacement common earlier ha hm).trans
        (commutator_eq_bot_iff_le_centralizer.mpr hcent).le)
    have hfour := Early.First.Layer.H_card_lower common earlier a ha
    rw [hzero, card_bot] at hfour
    omega
  have hcard : Nat.card J ≤ 4 := by
    have hlt : Nat.card J < 8 := by
      by_contra! h
      exact hproper (eq_of_le_of_card_ge inf_le_left (by rwa [common.natural.card_at c hc]))
    have hdiv := Nat.mem_divisors.mpr
      ⟨(common.natural.card_at c hc) ▸ card_dvd_of_le (show J ≤ U R c from inf_le_left),
        (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = ({1,2,4,8} : Finset ℕ) by decide] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    omega
  exact (eq_of_le_of_card_ge hHJ
    (hcard.trans (Early.First.Layer.H_card_lower common earlier a ha))).symm

/-- The neighboring moving intersection contributes no error inside its own Z-layer. -/
theorem neighboring_moving_intersection_kernel_le (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (Vcirc R (p.walk.getVert 6) ⊓ Z R (alpha R)) ⊓ Z R (p.walk.getVert 6) ≤
      Vcirc R (alpha R) := by
  let a := alpha R
  let c := p.walk.getVert 6
  have hc : color R c = false := p.even_color (by decide) (by decide)
  have hca : a ∈ Escape.movingNeighbors geometry c := by
    simpa only [Nat.reduceSub,p.center_eq] using
      (p.moving_neighbors source common earlier (i := 6) (by decide) (by decide) (by decide)).1
  have hac : c ∈ Escape.movingNeighbors geometry a := by
    simpa only [Nat.reduceAdd,p.center_eq] using
      (p.moving_neighbors source common earlier (i := 4) (by decide) (by decide) (by decide)).2
  have hHcU : H R c ≤ U R a := Early.Orbit.H_le_neighbor_U common earlier hc hca
  have hUV : U R a ≤ Vcirc R a := commutator_mono (Z_le_VBall R a 2) le_rfl
  have hHV : H R a ≤ Vcirc R a := le_normalizer_iff_commutator_le_left.mp
    ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Vcirc_normalized a))
  have hn : H R c ≤ normalizer (U R c : Set (FreeAmalgam R)) :=
    ((H_le_Z_of_central common hc (earlier.centrality c hc)).trans
      (Z_le_stabilizer R c)).trans (U_normalized c)
  intro x hx
  have hmem : x ∈ U R c ⊔ H R c := moving_inf_Z_at common earlier hc ▸
    (show x ∈ Vcirc R c ⊓ Z R c from ⟨hx.1.1,hx.2⟩)
  have hprod : x ∈ (U R c : Set (FreeAmalgam R)) * (H R c : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hmem
  obtain ⟨u,hu,h,hh,rfl⟩ := hprod
  have huZa : u ∈ Z R a := by
    have ht := (Z R a).mul_mem hx.1.2 ((Z R a).inv_mem (U_le_Z R a (hHcU hh)))
    simpa only [mul_inv_cancel_right] using ht
  have huHa : u ∈ H R a := natural_inf_neighbor_Z_eq_H common earlier rfl hc hac ▸
    (show u ∈ U R c ⊓ Z R a from ⟨hu,huZa⟩)
  exact (Vcirc R a).mul_mem (hHV huHa) (hUV (hHcU hh))

/-- The whole neighboring moving intersection has image of order at most two modulo Vcirc. -/
theorem neighboring_moving_intersection_index_le_two (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (Vcirc R (alpha R)).relIndex (Vcirc R (p.walk.getVert 6) ⊓ Z R (alpha R)) ≤ 2 := by
  let a := alpha R
  let c := p.walk.getVert 6
  let t := p.walk.getVert 5
  let J := Vcirc R c ⊓ Z R a
  have hc : color R c = false := p.even_color (by decide) (by decide)
  have hat : Adjacent R a t := by simpa only [p.center_eq] using p.adjacent (i := 4) (by decide)
  have hct : Adjacent R c t := adjacent_symm R (p.adjacent (i := 5) (by decide))
  let := finite_stabilizer R a
  let : Finite (Z R a) := Finite.of_injective (inclusion (Z_le_stabilizer R a)) (inclusion_injective _)
  let : Finite J := Finite.of_injective (inclusion inf_le_right) (inclusion_injective _)
  have hi : (Z R c).relIndex (Z R a) ≤ 2 := by
    exact (relIndex_le_of_le_left (Escape.EdgeTransfer.edge_Z_le c t hc hct)
      (by rw [earlier.edge_Z_index a t rfl hat]; decide)).trans
        (earlier.edge_Z_index a t rfl hat).le
  have hj : (Z R c).relIndex J ≤ 2 :=
    (relIndex_le_of_le_right (show J ≤ Z R a from inf_le_right) index_ne_zero_of_finite).trans hi
  have hle : J ⊓ Z R c ≤ Vcirc R a := neighboring_moving_intersection_kernel_le common earlier p
  have hidx := relIndex_le_of_le_left hle (L := J) index_ne_zero_of_finite
  rw [inf_relIndex_left] at hidx
  exact hidx.trans hj


private theorem overlap_span_le_join (source : LocalSource L R) (p : Early.SourcePath R (alpha R)) :
    conjugatesIn (Vcirc R (p.walk.getVert 6) ⊓ Z R (alpha R))
      (stabilizer R (alpha R)) ≤
    Vcirc R (alpha R) ⊔ (Vcirc R (p.walk.getVert 6) ⊓ Z R (alpha R)) := by
  let a := alpha R
  let J := Vcirc R (p.walk.getVert 6) ⊓ Z R a
  let E := Vcirc R a ⊔ J
  have hcomm : ⁅Z R a,stabilizer R a⁆ ≤ Vcirc R a := by
    rw [Escape.Initial.Z_commutator_stabilizer source a rfl]
    exact commutator_mono (Z_le_VBall R a 2) le_rfl
  apply iSup_le
  intro g
  rintro x ⟨z,hz,rfl⟩
  have he : (MulAut.conj (g : FreeAmalgam R)⁻¹) z =
      ⁅(g : FreeAmalgam R)⁻¹,z⁆ * z := by
    simp only [MulAut.conj_apply, commutatorElement_def]
    group
  change (MulAut.conj (g : FreeAmalgam R)⁻¹) z ∈ E
  rw [he]
  apply E.mul_mem
  · apply mem_sup_left
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator ((stabilizer R a).inv_mem g.property) hz.2)
  · exact mem_sup_right hz

/-- Even after taking every local conjugate, at most one binary error remains. -/
theorem second_core_commutator_index_le_two (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (Vcirc R (alpha R)).relIndex
      ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),core R (alpha R)⁆ ≤ 2 := by
  let a := alpha R
  let D := Vcirc R a
  let J := Vcirc R (p.walk.getVert 6) ⊓ Z R a
  let P := stabilizer R a
  have hD : D ≤ P := (Vcirc_le_V R a).trans
    (geometry.V_local a rfl common.large_distance)
  have hJ : J ≤ P := inf_le_right.trans (Z_le_stabilizer R a)
  let := finite_stabilizer R a
  let : Finite D := Finite.of_injective (inclusion hD) (inclusion_injective _)
  let : Finite (D ⊔ J : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (sup_le hD hJ)) (inclusion_injective _)
  have hle : ⁅hatW R a (p.walk.getVert 6) (p.walk.getVert 8),core R a⁆ ≤ D ⊔ J :=
    (second_core_commutator_le_neighboring_moving_span common earlier p).trans
      (overlap_span_le_join source p)
  have hi : D.relIndex (D ⊔ J) = D.relIndex J := by
    rw [sup_comm]
    have hDQ : D ≤ Q R a := (Vcirc_le_V R a).trans (V_le_Q R rfl common.large_distance)
    have hQZ : Q R a ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a rfl))
    exact relIndex_sup_of_normalizes J D
      ((hDQ.trans hQZ).trans ((centralizer_le inf_le_right).trans
        (Subgroup.centralizer_le_normalizer _)))
  exact (relIndex_le_of_le_right hle index_ne_zero_of_finite).trans
    (hi.le.trans (neighboring_moving_intersection_index_le_two common earlier p))


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
