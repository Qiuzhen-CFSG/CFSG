module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Crossing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Nontrivial
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Derived
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic
/-!
# Core displacement reductions for the contained second-layer branch

Write E for the original second layer, F for the transported second layer,
and W for the transported auxiliary span. When F lies in the original
opposite core, [E,F] lies in Z_alpha. The nontriviality proved from the
source residual triple and the edge index then give exactly two modulo
Z_middle. The same index-two argument puts all of Z_alpha in F.

If W itself lies in the original opposite core, [E,W] lies in Z_alpha.
For the larger span, evaluation at its nontrivial opposite-core coset is a
homomorphism from E to E/Z_alpha. Its kernel contains E intersect Q_middle:
the midpoint commutator bound and the exact intersection with Z_middle put
that part of the commutator in Z_beta. This bounds the left index by the
midpoint core index, which is two or four. It proves the requested bound in
the index-two case. The transported opposite core also has index two in E.
Its intersection with E commutes with W into E intersect F; bounding this
last commutator by Z_alpha is a sufficient, still explicit, condition.

A separate reduction excludes core index four if [E,E] lies in Z_beta and
the first core acts nonquadratically on Y/Z_alpha. At index four, E together
with Q_middle is the full first core. Since W normalizes E, the derived
bound makes E act quadratically on W/Z_middle. The midpoint core fixes that
quotient, so the full first core would also act quadratically, a contradiction.
Both local premises remain explicit pending their proofs; no unconditional
left-index-two bound is asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed pp.906--907,
claim (3) and the first-paragraph commutator comparison.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
/-- Containment in the original opposite core puts the second commutator
in the original Z_alpha, retaining both actual layers. -/
theorem contained_middle_second_commutator_le_Z
    (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) (e : M)
    (hcontained : (secondFlagLayer source i e).map t.conjugation.toMonoidHom ≤
      localFlagKernel source (!i) p.delta0) :
    ⁅secondFlagLayer source i p.delta0,
      (secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆ ≤ Z R (alpha R) :=
  (commutator_mono le_rfl hcontained).trans
    (Incident.secondFlagLayer_commutator_le_Z source geometry hlarge i p.delta0)

/-- In the contained branch the right source index is exactly two. -/
theorem contained_middle_second_commutator_index_eq_two
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) (e : M)
    (hactor : secondFlagLayer source i p.delta0 ≤
      (localFlagActor source (!i) e).map t.conjugation.toMonoidHom)
    (hescape : ¬ secondFlagLayer source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom)
    (hcontained : (secondFlagLayer source i e).map t.conjugation.toMonoidHom ≤
      localFlagKernel source (!i) p.delta0) :
    (Z R p.middle).relIndex
      ⁅secondFlagLayer source i p.delta0,
        (secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆ = 2 := by
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R _
  let : Finite (Z R (alpha R)) :=
    Finite.of_injective (inclusion (Z_le_stabilizer R _)) (inclusion_injective _)
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases he : color R p.middle <;> simp_all
  have hBT := Early.edge_Z_le p.middle (beta R) hcol (adjacent_symm R p.middle_neighbor)
  have hi := early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R)
  have hpos : (Z R (beta R)).relIndex (Z R (alpha R)) ≠ 0 := by omega
  have hup : (Z R p.middle).relIndex
      ⁅secondFlagLayer source i p.delta0,
        (secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆ ≤ 2 := by
    apply (relIndex_le_of_le_right
      (contained_middle_second_commutator_le_Z source geometry common.large_distance i p t e
        hcontained) ?_).trans
    · exact (relIndex_le_of_le_left hBT hpos).trans_eq hi
    · exact index_ne_zero_of_finite
  exact le_antisymm hup
    (middle_second_commutator_index_ge_two source geometry common early i hkernel p t e
      hactor hescape)

private theorem le_of_index_two_of_crossing {G : Type*} [Group G]
    (A B D F : Subgroup G) (hDA : D ≤ A) (hDF : D ≤ F)
    (hBF : B ≤ F) (hi : B.relIndex A = 2) (hnot : ¬ D ≤ B) : A ≤ F := by
  obtain ⟨u, hu, hun⟩ := SetLike.not_le_iff_exists.mp hnot
  intro a ha
  by_cases hab : a ∈ B
  · exact hBF hab
  · have hfactor : u⁻¹ * a ∈ B := by
      have hm := (B.subgroupOf A).mul_mem_iff_of_index_two hi
        (a := ⟨u⁻¹, A.inv_mem (hDA hu)⟩) (b := ⟨a, ha⟩)
      exact hm.mpr (by simp only [mem_subgroupOf, inv_mem_iff, hun, hab])
    simpa only [mul_inv_cancel_left] using F.mul_mem (hDF hu) (hBF hfactor)

/-- The contained branch forces the whole original Z_alpha into the
transported second layer, using the nonzero displacement modulo Z_middle. -/
theorem contained_middle_Z_le_second
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) (e : M)
    (hactor : secondFlagLayer source i p.delta0 ≤
      (localFlagActor source (!i) e).map t.conjugation.toMonoidHom)
    (hescape : ¬ secondFlagLayer source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom)
    (hcontained : (secondFlagLayer source i e).map t.conjugation.toMonoidHom ≤
      localFlagKernel source (!i) p.delta0) :
    Z R (alpha R) ≤ (secondFlagLayer source i e).map t.conjugation.toMonoidHom := by
  let E := secondFlagLayer source i p.delta0
  let F := (secondFlagLayer source i e).map t.conjugation.toMonoidHom
  have hDF : ⁅E,F⁆ ≤ F := le_normalizer_iff_commutator_le_right.mp
    (hactor.trans ((map_mono (Incident.secondFlagLayer_normalized source geometry
      common.large_distance i e)).trans (le_normalizer_map _)))
  have hTF : Z R p.middle ≤ F := by
    rw [← t.map_Z_alpha]
    exact map_mono (Z_le_secondFlagLayer source i e)
  have hBF : Z R (beta R) ≤ F := by
    rw [← middle_intersection_eq_edge_Z source geometry early i p]
    exact inf_le_left.trans hTF
  apply le_of_index_two_of_crossing (Z R (alpha R)) (Z R (beta R)) ⁅E,F⁆ F
    (contained_middle_second_commutator_le_Z source geometry common.large_distance i p t e
      hcontained) hDF hBF
    (early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R))
  intro h
  have hDT : ⁅E,F⁆ ≤ Z R p.middle := by
    rw [← middle_intersection_eq_edge_Z source geometry early i p] at h
    exact h.trans inf_le_left
  have hi := contained_middle_second_commutator_index_eq_two
    source geometry common early i hkernel p t e hactor hescape hcontained
  have hone : (Z R p.middle).relIndex ⁅E,F⁆ = 1 := relIndex_eq_one.mpr hDT
  change (Z R p.middle).relIndex ⁅E,F⁆ = 2 at hi
  omega

omit [Finite M] in
/-- The subcase where the whole auxiliary span is contained has left index one. -/
theorem middle_left_index_eq_one_of_Y_contained
    (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) (e : M)
    (hcontained : (Y source i e).map t.conjugation.toMonoidHom ≤
      localFlagKernel source (!i) p.delta0) :
    (Z R (alpha R)).relIndex
      ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ = 1 :=
  relIndex_eq_one.mpr ((commutator_mono le_rfl hcontained).trans
    (Incident.secondFlagLayer_commutator_le_Z source geometry hlarge i p.delta0))

private theorem commutator_index_le_of_actor_index_two {G : Type*} [Group G]
    (E W B N K : Subgroup G) [Finite E]
    (hNE : N ≤ E) (hEN : E ≤ normalizer N) (hWN : W ≤ normalizer N)
    (hWE : W ≤ normalizer E) (hEE : ⁅E,E⁆ ≤ N)
    (hi : B.relIndex W = 2) (hEB : ⁅E,W ⊓ B⁆ ≤ N)
    (hK : ⁅E ⊓ K,W⁆ ≤ N) : N.relIndex ⁅E,W⁆ ≤ K.relIndex E := by
  classical
  let NN := N.subgroupOf E
  let : NN.Normal := normal_subgroupOf_of_le_normalizer hEN
  let : IsMulCommutative (E ⧸ NN) := Normal.quotient_commutative_iff_commutator_le.mpr (by
    intro x hx
    exact hEE (by
      have hm := mem_map_of_mem E.subtype hx
      rwa [map_subtype_commutator] at hm))
  let : CommGroup (E ⧸ NN) := IsMulCommutative.instCommGroup
  let π := QuotientGroup.mk' NN
  obtain ⟨w, hw, hwn⟩ : ∃ w ∈ W, w ∉ B := by
    by_contra! h
    have hone := relIndex_eq_one.mpr h
    omega
  let c : E →* E := {
    toFun x := ⟨w * x * w⁻¹, (mem_normalizer_iff.mp (hWE hw) _).mp x.property⟩
    map_one' := Subtype.ext (by simp)
    map_mul' x y := Subtype.ext (by simp [mul_assoc]) }
  let f : E →* E ⧸ NN := π / π.comp c
  have hf (x : E) : f x = π ⟨⁅(x:G),w⁆,
      le_normalizer_iff_commutator_le_left.mp hWE
        (commutator_mem_commutator x.property hw)⟩ := by
    change π x / π (c x) = _
    rw [← map_div]
    congr 1
    apply Subtype.ext
    simp only [c, commutatorElement_def, div_eq_mul_inv, mul_inv_rev, inv_inv,
      MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  let T₀ := f.range.comap π
  let T := T₀.map E.subtype
  have hNT : N ≤ T := by
    intro n hn
    exact ⟨⟨n,hNE hn⟩, by
      change π ⟨n,hNE hn⟩ ∈ f.range
      have he : π ⟨n,hNE hn⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hn
      rw [he]
      exact f.range.one_mem, rfl⟩
  have hCT : ⁅E,W⁆ ≤ T := by
    apply commutator_le.mpr
    intro e he a ha
    by_cases haB : a ∈ B
    · exact hNT (hEB (commutator_mem_commutator he ⟨ha,haB⟩))
    · have hfactor : w⁻¹*a ∈ B := by
        have hm := (B.subgroupOf W).mul_mem_iff_of_index_two hi
          (a := ⟨w⁻¹,W.inv_mem hw⟩) (b := ⟨a,ha⟩)
        exact hm.mpr (by simp only [mem_subgroupOf,inv_mem_iff,hwn,haB])
      have hc := hEB (commutator_mem_commutator he
        (show w⁻¹*a ∈ W ⊓ B from ⟨W.mul_mem (W.inv_mem hw) ha,hfactor⟩))
      have hn := (mem_normalizer_iff.mp (hWN hw) _).mp hc
      have ht : ⁅e,w⁆ ∈ T := by
        refine ⟨⟨⁅e,w⁆,le_normalizer_iff_commutator_le_left.mp hWE
          (commutator_mem_commutator he hw)⟩, ?_,rfl⟩
        exact ⟨⟨e,he⟩, hf ⟨e,he⟩⟩
      have hp := T.mul_mem ht (hNT hn)
      have hid := commutatorElement_mul_right_eq_mul_conj e w (w⁻¹*a)
      simp only [mul_inv_cancel_left] at hid
      rw [hid]
      simpa only [mul_assoc] using hp
  have hker : K.subgroupOf E ≤ f.ker := by
    intro x hx
    change f x = 1
    rw [hf]
    exact (QuotientGroup.eq_one_iff _).mpr
      (hK (commutator_mem_commutator ⟨x.property,hx⟩ hw))
  have hTi : N.relIndex T = Nat.card f.range := by
    have hh := relIndex_map_map_of_injective NN T₀ E.subtype_injective
    rw [map_subgroupOf_eq_of_le hNE] at hh
    rw [hh]
    have hrel := relIndex_ker (f := π) T₀
    rw [QuotientGroup.ker_mk'] at hrel
    rw [hrel]
    rw [show T₀.map π = f.range from map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective NN) f.range]
  let : Finite T := Finite.of_injective (inclusion (map_subtype_le T₀))
    (inclusion_injective _)
  calc
    N.relIndex ⁅E,W⁆ ≤ N.relIndex T :=
      relIndex_le_of_le_right hCT index_ne_zero_of_finite
    _ = Nat.card f.range := hTi
    _ = f.ker.index := (index_ker f).symm
    _ ≤ (K.subgroupOf E).index := by
      simpa only [relIndex_top_right] using
        (relIndex_le_of_le_left (L := ⊤) hker index_ne_zero_of_finite)

/-- Evaluation at one nontrivial opposite-core coset bounds the left commutator
by the original layer's displacement at the midpoint. -/
theorem middle_left_index_le_core_index
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) (e : M) :
    (Z R (alpha R)).relIndex
      ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤
    (Q R p.middle).relIndex (secondFlagLayer source i p.delta0) := by
  let E := secondFlagLayer source i p.delta0
  let W := (Y source i e).map t.conjugation.toMonoidHom
  let H := Q R (beta R)
  let B := localFlagKernel source (!i) p.delta0
  have hWH : W ≤ H := transported_Y_le_edge_core source geometry common.large_distance i p t e
  have hEV : E ≤ V R (alpha R) := secondFlagLayer_le_radius source i p.delta0
  have hEQ : E ≤ Q R (alpha R) := hEV.trans (V_le_Q geometry common.large_distance _ rfl)
  have hHP : H ≤ localFlagActor source (!i) p.delta0 := by
    change Q R (beta R) ≤ _
    rw [← hkernel]
    exact Incident.flagKernel_le_incidentActor source i p.delta0 p.delta0_neighbor
  have hHE : H ≤ normalizer E := hHP.trans
    (Incident.secondFlagLayer_normalized source geometry common.large_distance i p.delta0)
  have hWN : W ≤ normalizer (Z R (alpha R)) := hWH.trans (hHP.trans
    ((localFlagActor_le_stabilizer source (!i) p.delta0).trans (Z_normalized R _)))
  have hWE : W ≤ normalizer E := hWH.trans hHE
  let : Finite E := Incident.secondFlagLayer_finite source geometry common.large_distance i p.delta0
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases he : color R p.middle <;> simp_all
  by_cases hWB : W ≤ B
  · have hone := middle_left_index_eq_one_of_Y_contained source geometry common.large_distance
      i p t e hWB
    exact hone.le.trans (by have hh := p.displacement; omega)
  · let : Finite (stabilizer R (alpha R)) := finite_stabilizer R _
    let : Finite H := Finite.of_injective
      (inclusion (hHP.trans (localFlagActor_le_stabilizer source (!i) p.delta0)))
      (inclusion_injective _)
    let : Finite W := Finite.of_injective (inclusion hWH) (inclusion_injective _)
    have hiH : B.relIndex H = 2 := by
      change B.relIndex (Q R (beta R)) = 2
      rw [← hkernel]
      exact incident_reverse_core_index source i p.delta0 p.delta0_neighbor
    have hi : B.relIndex W = 2 := by
      have hle := relIndex_le_of_le_right hWH (show B.relIndex H ≠ 0 from by omega)
      have hpos : B.relIndex W ≠ 0 := index_ne_zero_of_finite
      have hne : B.relIndex W ≠ 1 := fun h => hWB (relIndex_eq_one.mp h)
      omega
    apply commutator_index_le_of_actor_index_two E W B (Z R (alpha R)) (Q R p.middle)
      (Z_le_secondFlagLayer source i p.delta0)
      (hEV.trans ((geometry.V_local _ rfl common.large_distance).trans (Z_normalized R _)))
      hWN hWE ((commutator_mono hEV hEQ).trans (early.commutator_le_Z _ rfl)) hi
    · exact (commutator_mono le_rfl inf_le_right).trans
        (Incident.secondFlagLayer_commutator_le_Z source geometry common.large_distance i p.delta0)
    · have hWV : W ≤ V R p.middle :=
        (map_mono (Y_le_radius source i e)).trans_eq t.map_V_alpha
      have hcommE : ⁅E ⊓ Q R p.middle,W⁆ ≤ E :=
        (commutator_mono inf_le_left le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp hWE)
      have hcommZ : ⁅E ⊓ Q R p.middle,W⁆ ≤ Z R p.middle := by
        rw [commutator_comm]
        exact (commutator_mono hWV inf_le_right).trans (early.commutator_le_Z _ hcol)
      have hh := le_inf hcommZ hcommE
      rw [middle_intersection_eq_edge_Z source geometry early i p] at hh
      exact hh.trans (Early.edge_Z_le _ _ rfl (base_adjacent R))

/-- The left index is at most four before the final contained-branch argument. -/
theorem middle_left_index_le_four
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) (e : M) :
    (Z R (alpha R)).relIndex
      ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤ 4 := by
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases he : color R p.middle <;> simp_all
  have hi := early.edge_Q_index p.middle (beta R) hcol (adjacent_symm R p.middle_neighbor)
  apply (middle_left_index_le_core_index source geometry common early i hkernel p t e).trans
  have hEH : secondFlagLayer source i p.delta0 ≤ Q R (beta R) :=
    (secondFlagLayer_le_radius source i p.delta0).trans
      ((V_le_Q geometry common.large_distance _ rfl).trans
        (Q_le_adjacent_h R rfl (base_adjacent R)))
  exact (relIndex_le_of_le_right hEH (by omega : (Q R p.middle).relIndex (Q R (beta R)) ≠ 0)).trans_eq hi

/-- The source left bound holds when the original second layer has midpoint
core index two, independently of the transported second-layer containment. -/
theorem middle_left_index_le_two_of_core_index_two
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) (e : M)
    (hi : (Q R p.middle).relIndex (secondFlagLayer source i p.delta0) = 2) :
    (Z R (alpha R)).relIndex
      ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤ 2 :=
  (middle_left_index_le_core_index source geometry common early i hkernel p t e).trans_eq hi

/-- The source displacement is exactly two or four, using normality in the
finite common edge core. -/
theorem middle_second_core_index_eq_two_or_four
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (p : SourceFlagPreparatoryData source geometry i) :
    (Q R p.middle).relIndex (secondFlagLayer source i p.delta0) = 2 ∨
    (Q R p.middle).relIndex (secondFlagLayer source i p.delta0) = 4 := by
  let H := Q R (beta R)
  let E := secondFlagLayer source i p.delta0
  let K := (Q R p.middle).subgroupOf H
  have hEH : E ≤ H := (secondFlagLayer_le_radius source i p.delta0).trans
    ((V_le_Q geometry common.large_distance _ rfl).trans
      (Q_le_adjacent_h R rfl (base_adjacent R)))
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases he : color R p.middle <;> simp_all
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    ((show H ≤ stabilizer R p.middle from fun _ hx => hx.2 _ p.middle_neighbor).trans
      (Q_normalized R _))
  have hi : K.index = 4 :=
    early.edge_Q_index p.middle (beta R) hcol (adjacent_symm R p.middle_neighbor)
  have hd := K.relIndex_dvd_index_of_normal (E.subgroupOf H)
  rw [hi, relIndex_subgroupOf hEH] at hd
  have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1,2,4} : Finset ℕ) by decide] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  have hlo := p.displacement
  change (Q R p.middle).relIndex (secondFlagLayer source i p.delta0) = 1 ∨
    (Q R p.middle).relIndex (secondFlagLayer source i p.delta0) = 2 ∨
    (Q R p.middle).relIndex (secondFlagLayer source i p.delta0) = 4 at hm
  omega

/-- Only midpoint core index four can remain in the source left-bound problem. -/
theorem middle_left_index_le_two_of_core_index_ne_four
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) (e : M)
    (hi : (Q R p.middle).relIndex (secondFlagLayer source i p.delta0) ≠ 4) :
    (Z R (alpha R)).relIndex
      ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤ 2 :=
  middle_left_index_le_two_of_core_index_two source geometry common early i hkernel p t e
    ((middle_second_core_index_eq_two_or_four source geometry common early i p).resolve_right hi)


/-- An incident transported opposite core has index two in the original
second layer whenever that layer escapes it. -/
theorem middle_transported_core_index_eq_two
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (e : M) (he : flagIncident source i 1 e)
    (hescape : ¬ secondFlagLayer source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom) :
    ((localFlagKernel source (!i) e).map t.conjugation.toMonoidHom).relIndex
      (secondFlagLayer source i p.delta0) = 2 := by
  let K := (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom
  have hi : K.relIndex (Q R (beta R)) = 2 := by
    have hh := relIndex_map_map_of_injective (f := t.conjugation.toMonoidHom)
      (localFlagKernel source (!i) e) (Q R (beta R)) t.conjugation.injective
    rw [t.map_Q_beta] at hh
    exact hh.trans (hkernel ▸ incident_reverse_core_index source i e he)
  have hEH : secondFlagLayer source i p.delta0 ≤ Q R (beta R) :=
    (secondFlagLayer_le_radius source i p.delta0).trans
      ((V_le_Q geometry common.large_distance _ rfl).trans
        (Q_le_adjacent_h R rfl (base_adjacent R)))
  let := Incident.secondFlagLayer_finite source geometry common.large_distance i p.delta0
  have hup := relIndex_le_of_le_right hEH (by omega : K.relIndex (Q R (beta R)) ≠ 0)
  have hpos : K.relIndex (secondFlagLayer source i p.delta0) ≠ 0 := index_ne_zero_of_finite
  have hne : K.relIndex (secondFlagLayer source i p.delta0) ≠ 1 :=
    fun h => hescape (relIndex_eq_one.mp h)
  change K.relIndex (secondFlagLayer source i p.delta0) = 2
  omega

/-- The core-action calculation places the remaining commutator in the
intersection of the two actual second layers. -/
theorem middle_transported_core_commutator_le_intersection
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (e : M) :
    ⁅secondFlagLayer source i p.delta0 ⊓
        (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom,
      (Y source i e).map t.conjugation.toMonoidHom⁆ ≤
      secondFlagLayer source i p.delta0 ⊓
        (secondFlagLayer source i e).map t.conjugation.toMonoidHom := by
  apply le_inf
  · have hHE : Q R (beta R) ≤ normalizer (secondFlagLayer source i p.delta0) := by
      rw [← hkernel]
      exact (Incident.flagKernel_le_incidentActor source i p.delta0 p.delta0_neighbor).trans
        (Incident.secondFlagLayer_normalized source geometry common.large_distance i p.delta0)
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((transported_Y_le_edge_core source geometry common.large_distance i p t e).trans hHE))
  · rw [commutator_comm]
    have hh := map_mono (f := t.conjugation.toMonoidHom)
      (Y_core_le_second source geometry common early i hkernel e)
    rw [map_commutator] at hh
    exact (commutator_mono le_rfl inf_le_right).trans hh

/-- At midpoint core index four the intersection with the transported
opposite core still has midpoint core index two. This retains the extra
coset whose action must be controlled in the remaining branch. -/
theorem middle_transported_core_intersection_index_eq_two
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (e : M) (he : flagIncident source i 1 e)
    (hescape : ¬ secondFlagLayer source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom)
    (hfour : (Q R p.middle).relIndex (secondFlagLayer source i p.delta0) = 4) :
    (Q R p.middle).relIndex (secondFlagLayer source i p.delta0 ⊓
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom) = 2 := by
  have hQK : Q R p.middle ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom := by
    rw [← t.map_Q_alpha]
    exact map_mono (Q_alpha_le_localFlagKernel source (!i) e)
  have hi := middle_transported_core_index_eq_two source geometry common i hkernel p t e
    he hescape
  have hm := relIndex_inf_mul_relIndex (Q R p.middle)
    ((localFlagKernel source (!i) e).map t.conjugation.toMonoidHom)
    (secondFlagLayer source i p.delta0)
  rw [inf_eq_left.mpr hQK, hi, hfour, inf_comm] at hm
  omega

/-- Centralization by the transported opposite-core intersection suffices
for the source left bound. The additional containment is explicit; the
fixed-preimage argument needed to discharge it is not assumed proved. -/
theorem middle_left_index_le_two_of_transported_core_commutator
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (e : M) (he : flagIncident source i 1 e)
    (hescape : ¬ secondFlagLayer source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom)
    (hcomm : ⁅secondFlagLayer source i p.delta0 ⊓
        (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom,
      (Y source i e).map t.conjugation.toMonoidHom⁆ ≤ Z R (alpha R)) :
    (Z R (alpha R)).relIndex
      ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤ 2 := by
  let E := secondFlagLayer source i p.delta0
  let W := (Y source i e).map t.conjugation.toMonoidHom
  let H := Q R (beta R)
  let B := localFlagKernel source (!i) p.delta0
  let K := (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom
  have hWH : W ≤ H := transported_Y_le_edge_core source geometry common.large_distance i p t e
  have hEV : E ≤ V R (alpha R) := secondFlagLayer_le_radius source i p.delta0
  have hEQ : E ≤ Q R (alpha R) := hEV.trans (V_le_Q geometry common.large_distance _ rfl)
  have hHP : H ≤ localFlagActor source (!i) p.delta0 := by
    change Q R (beta R) ≤ _
    rw [← hkernel]
    exact Incident.flagKernel_le_incidentActor source i p.delta0 p.delta0_neighbor
  have hHE : H ≤ normalizer E := hHP.trans
    (Incident.secondFlagLayer_normalized source geometry common.large_distance i p.delta0)
  have hHN : H ≤ normalizer (Z R (alpha R)) :=
    hHP.trans ((localFlagActor_le_stabilizer source (!i) p.delta0).trans (Z_normalized R _))
  let : Finite E := Incident.secondFlagLayer_finite source geometry common.large_distance i p.delta0
  by_cases hWB : W ≤ B
  · exact (middle_left_index_eq_one_of_Y_contained source geometry common.large_distance
      i p t e hWB).le.trans (by decide)
  · let : Finite (stabilizer R (alpha R)) := finite_stabilizer R _
    let : Finite H := Finite.of_injective
      (inclusion (hHP.trans (localFlagActor_le_stabilizer source (!i) p.delta0)))
      (inclusion_injective _)
    let : Finite W := Finite.of_injective (inclusion hWH) (inclusion_injective _)
    have hiH : B.relIndex H = 2 := by
      change B.relIndex (Q R (beta R)) = 2
      rw [← hkernel]
      exact incident_reverse_core_index source i p.delta0 p.delta0_neighbor
    have hi : B.relIndex W = 2 := by
      have hle := relIndex_le_of_le_right hWH (show B.relIndex H ≠ 0 from by omega)
      have hpos : B.relIndex W ≠ 0 := index_ne_zero_of_finite
      have hne : B.relIndex W ≠ 1 := fun h => hWB (relIndex_eq_one.mp h)
      omega
    have hbound := commutator_index_le_of_actor_index_two E W B (Z R (alpha R)) K
      (Z_le_secondFlagLayer source i p.delta0)
      (hEV.trans ((geometry.V_local _ rfl common.large_distance).trans (Z_normalized R _)))
      (hWH.trans hHN) (hWH.trans hHE)
      ((commutator_mono hEV hEQ).trans (early.commutator_le_Z _ rfl)) hi
      ((commutator_mono le_rfl inf_le_right).trans
        (Incident.secondFlagLayer_commutator_le_Z source geometry common.large_distance i p.delta0))
      hcomm
    exact hbound.trans_eq
      (middle_transported_core_index_eq_two source geometry common i hkernel p t e he hescape)


private theorem commutator_join_right_le {G : Type*} [Group G]
    (X A B H N : Subgroup G) (hAH : A ≤ H) (hBH : B ≤ H)
    (hHN : H ≤ normalizer N) (hXA : ⁅X,A⁆ ≤ N) (hXB : ⁅X,B⁆ ≤ N) :
    ⁅X,A ⊔ B⁆ ≤ N := by
  have h : A ⊔ B ≤ commutatorPreimage H X N := sup_le
    (le_commutatorPreimage hAH (by rwa [commutator_comm]))
    (le_commutatorPreimage hBH (by rwa [commutator_comm]))
  rw [commutator_comm]
  exact (commutator_mono h le_rfl).trans (commutator_commutatorPreimage_le H X N hHN)

private theorem quadratic_of_core_supplement {G : Type*} [Group G]
    (E K W N H : Subgroup G) (hEH : E ≤ H) (hKH : K ≤ H)
    (hgen : E ⊔ K = H) (hNW : N ≤ W)
    (hWN : W ≤ normalizer N) (hHN : H ≤ normalizer N)
    (hHW : H ≤ normalizer W) (hWE : W ≤ normalizer E)
    (hEE : ⁅E,E⁆ ≤ N) (hWK : ⁅W,K⁆ ≤ N) : ⁅⁅W,H⁆,H⁆ ≤ N := by
  let C := commutatorPreimage W H N
  have hHC : H ≤ normalizer C :=
    commutatorPreimage_normalized W H N H hWN hHW H.le_normalizer hHN
  have hNC : N ≤ C := le_commutatorPreimage hNW
    (le_normalizer_iff_commutator_le_left.mp hHN)
  have hCE : ⁅W,E⁆ ≤ C := by
    apply le_commutatorPreimage
      (le_normalizer_iff_commutator_le_left.mp (hEH.trans hHW))
    rw [← hgen]
    apply commutator_join_right_le _ E K H N hEH hKH hHN
    · exact (commutator_mono
        (le_normalizer_iff_commutator_le_right.mp hWE) le_rfl).trans hEE
    · exact (commutator_mono
        (le_normalizer_iff_commutator_le_left.mp (hEH.trans hHW)) le_rfl).trans hWK
  have hWC : ⁅W,H⁆ ≤ C := by
    rw [← hgen]
    exact commutator_join_right_le W E K H C hEH hKH hHC hCE (hWK.trans hNC)
  exact (commutator_mono hWC le_rfl).trans (commutator_commutatorPreimage_le W H N hWN)

/-- If the selected layer's derived subgroup lies in Z_beta, midpoint core
index four would make the full first core act quadratically on every incident
transported auxiliary span. This is a conditional reduction, with the derived
containment explicit. -/
theorem middle_first_core_quadratic_of_index_four_of_derived
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (e : M) (he : flagIncident source i 1 e)
    (hderived : ⁅secondFlagLayer source i p.delta0,
      secondFlagLayer source i p.delta0⁆ ≤ Z R (beta R))
    (hfour : (Q R p.middle).relIndex (secondFlagLayer source i p.delta0) = 4) :
    ⁅⁅(Y source i e).map t.conjugation.toMonoidHom, Q R (beta R)⁆,
      Q R (beta R)⁆ ≤ Z R p.middle := by
  let E := secondFlagLayer source i p.delta0
  let W := (Y source i e).map t.conjugation.toMonoidHom
  let H := Q R (beta R)
  let c : FlagCriticalData source geometry i := {
    middle := p.middle
    endpoint := p.endpoint
    critical := p.critical
    middle_neighbor := p.middle_neighbor
    first_distance := p.first_distance
    second_distance := p.second_distance
    middle_triple := p.middle_triple }
  have hEH : E ≤ H := (secondFlagLayer_le_radius source i p.delta0).trans
    ((V_le_Q geometry common.large_distance _ rfl).trans
      (Q_le_adjacent_h R rfl (base_adjacent R)))
  have hKH : Q R p.middle ≤ H := Q_le_adjacent_h R rfl (adjacent_symm R p.middle_neighbor)
  have hgen : E ⊔ Q R p.middle = H :=
    c.sup_middle_kernel_of_displacement early E hEH (by
      change 2 < (Q R p.middle).relIndex (secondFlagLayer source i p.delta0)
      omega)
  have hHG : H ≤ stabilizer R p.middle := fun _ hx => hx.2 _ p.middle_neighbor
  have hWV : W ≤ V R p.middle :=
    (map_mono (Y_le_radius source i e)).trans_eq t.map_V_alpha
  have hNW : Z R p.middle ≤ W := by
    rw [← t.map_Z_alpha]
    exact map_mono ((Z_le_secondFlagLayer source i e).trans (second_le_Y source i e))
  have hHW : H ≤ normalizer W := by
    have hh := map_mono (f := t.conjugation.toMonoidHom)
      ((Incident.flagKernel_le_incidentActor source i e he).trans (Y_normalized source i e))
    rw [hkernel, t.map_Q_beta] at hh
    exact hh.trans (le_normalizer_map _)
  have hHE : H ≤ normalizer E := by
    change Q R (beta R) ≤ _
    rw [← hkernel]
    exact (Incident.flagKernel_le_incidentActor source i p.delta0 p.delta0_neighbor).trans
      (Incident.secondFlagLayer_normalized source geometry common.large_distance i p.delta0)
  apply quadratic_of_core_supplement E (Q R p.middle) W (Z R p.middle) H hEH hKH hgen hNW
    (hWV.trans ((V_le_Q geometry common.large_distance _ c.middle_color).trans
      ((show Q R p.middle ≤ stabilizer R p.middle from fun _ hx => hx.1).trans
        (Z_normalized R _))))
    (hHG.trans (Z_normalized R _)) hHW
    ((transported_Y_le_edge_core source geometry common.large_distance i p t e).trans hHE)
  · exact hderived.trans (Early.edge_Z_le _ _ c.middle_color (adjacent_symm R p.middle_neighbor))
  · exact (commutator_mono hWV le_rfl).trans (early.commutator_le_Z _ c.middle_color)

/-- A derived-subgroup bound and the actual first-core nonquadraticity exclude
midpoint core index four and give the requested left bound. Both local inputs
remain explicit pending their separate proofs. -/
theorem middle_left_index_le_two_of_derived_of_nonquadratic
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (e : M) (he : flagIncident source i 1 e)
    (hderived : ⁅secondFlagLayer source i p.delta0,
      secondFlagLayer source i p.delta0⁆ ≤ Z R (beta R))
    (hnonquadratic : ¬ ⁅⁅Y source i e, Q R (beta R)⁆, Q R (beta R)⁆ ≤ Z R (alpha R)) :
    (Z R (alpha R)).relIndex
      ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤ 2 := by
  apply middle_left_index_le_two_of_core_index_ne_four source geometry common early i hkernel p t e
  intro hfour
  apply hnonquadratic
  apply (map_le_map_iff_of_injective (f := t.conjugation.toMonoidHom)
    t.conjugation.injective).mp
  rw [map_commutator, map_commutator, t.map_Q_beta, t.map_Z_alpha]
  exact middle_first_core_quadratic_of_index_four_of_derived source geometry common early
    i hkernel p t e he hderived hfour

/-- The contained-second-layer branch of the source left-index comparison.
The derived edge bound and the nonzero source triple exclude midpoint index
four; the remaining index-two reduction gives the required bound. -/
theorem contained_middle_left_index_le_two
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i) (e : M)
    (he : flagIncident source i 1 e)
    (hactor : secondFlagLayer source i p.delta0 ≤
      (localFlagActor source (!i) e).map
        (middleTransport p).conjugation.toMonoidHom)
    (hescape : ¬ secondFlagLayer source i p.delta0 ≤
      (localFlagKernel source (!i) e).map
        (middleTransport p).conjugation.toMonoidHom)
    (hcontained : (secondFlagLayer source i e).map
      (middleTransport p).conjugation.toMonoidHom ≤
      localFlagKernel source (!i) p.delta0) :
    (Z R (alpha R)).relIndex
      ⁅secondFlagLayer source i p.delta0,
        (Y source i e).map (middleTransport p).conjugation.toMonoidHom⁆ ≤ 2 := by
  have _ := hb
  have _ := natural
  have _ := hactor
  have _ := hescape
  have _ := hcontained
  have htriple := Y_core_residual_triple_not_le source geometry i p e
  have hderived := secondFlagLayer_derived_le_edge_Z source geometry common early
    i hkernel p.delta0 p.delta0_neighbor
  have hnonquadratic := Y_first_core_not_quadratic source geometry common early
    i hkernel e he htriple
  exact middle_left_index_le_two_of_derived_of_nonquadratic source geometry common early
    i hkernel p (middleTransport p) e he hderived hnonquadratic

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
