module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusPaths
public import Theory.SpecificGroups.SymplecticFour.QuadraticFixedPlane

/-!
# Large actors fix the next original seed along equal movers

More than q images in a quadratic smaller mover have the same natural fixed
plane as that entire mover. The exact fixed-index marking transports this
equality to the full U-layer, and the whole-Z decomposition retains its
vertex-central attachment. Equal movers then put these fixed elements in the
neighboring X-layer. The smaller-mover bound on X, together with the full local
fixed part, puts them in the neighboring seed without asserting X equals Z.

This is the natural-module implication used in the last paragraph of MS93
(5.11), printed p.924. The commutator subgroup is an explicit input: its literal
seed containment and its commutation with the chosen actor are not inferred
from a critical-path replacement or a changed endpoint.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open scoped Pointwise IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem large_actor_moving_fixed
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAJ : A ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2))
    (hlarge : Nat.card F < (Q d.radical a).relIndex A) :
    U d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) =
      U d.radical a ⊓ centralizer (Subgroup.SmallMover.join
        (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set _) := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have hAS : A ≤ S := hAJ.trans hJS
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer _ a)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hJP,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic_contains_mover_of_four_lt d geometry hb ha hat
  let P := (CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype
  let A₀ := A.subgroupOf S
  let J₀ := J.subgroupOf S
  have hJf : J₀.map f ≤ P := (map_le_iff_le_comap).mpr hJP
  have hcard : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hbig : Nat.card E.Carrier < Nat.card (A₀.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker A₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hAS] at hh
    rw [←hh,hcard]
    exact hlarge
  have hfixed := large_quadratic_subactor_fixed_eq (A₀.map f) (J₀.map f)
    (map_mono (comap_mono hAJ))
    (fun x hx y hy v => CentralRootGeometry.SmallMovers.Degree.plane_radical_quadratic
      x (hJf hx) y (hJf hy) v) hbig
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
  have hfixed' : fixedSpace σ (A₀.map f)=fixedSpace σ (J₀.map f) := by
    have bridge (T : Subgroup (Sp E.Carrier)) :
        fixedSpace σ T=(TwoLocalCover.fixedSpace T).restrictScalars (ZMod 2) := by
      ext v
      exact ⟨fun hv x hx => hv ⟨x,hx⟩,fun hv x => hv x.val x.property⟩
    rw [bridge,bridge,hfixed]
  have hAi := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    ((U d.radical a).subgroupOf S) A₀
  rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hAS,hindex] at hAi
  have hJi := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    ((U d.radical a).subgroupOf S) J₀
  rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hJS,hindex] at hJi
  have hi : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
      (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [hAi,hJi]
    change 2 ^ fixedCodim σ (A₀.map f)=2 ^ fixedCodim σ (J₀.map f)
    unfold fixedCodim
    rw [hfixed']
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (U_le_Z a)) (inclusion_injective _)
  let CA := (centralizer (A : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)
  let CJ := (centralizer (J : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)
  have he : CJ=CA := by
    apply eq_of_le_of_card_ge (comap_mono (centralizer_le hAJ))
    have hCA := CA.card_mul_index
    have hCJ := CJ.card_mul_index
    change CA.index=CJ.index at hi
    rw [hi] at hCA
    exact (Nat.eq_of_mul_eq_mul_right (index_ne_zero_of_finite (H := CJ)).bot_lt
      (hCA.trans hCJ.symm)).le
  apply le_antisymm
  · intro u hu
    exact ⟨hu.1,show (⟨u,hu.1⟩ : U d.radical a) ∈ CJ from he.symm ▸ hu.2⟩
  · exact inf_le_inf_left _ (centralizer_le hAJ)

private theorem large_actor_seed_fixed
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAJ : A ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2))
    (hlarge : Nat.card F < (Q d.radical a).relIndex A) :
    Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) ≤
      centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let C := Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  have hJS : J ≤ stabilizer d.radical a := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have hCS : C ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans (Z_le_stabilizer _ a)).trans (U_normalized a)
  have hCJ : C ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hJS)
  have hCA : C ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    hCJ.trans (centralizer_le hAJ)
  intro z hz
  have hzprod : z ∈ (U d.radical a : Set (FreeAmalgam d.radical))*(C : Set _) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hCS]
    exact h.replacement_Z_eq_U_sup_fixed d geometry hb.le ha ▸ hz.1
  obtain ⟨u,hu,c,hc,rfl⟩ := hzprod
  have huA : u ∈ centralizer (A : Set (FreeAmalgam d.radical)) := by
    have hh := (centralizer (A : Set (FreeAmalgam d.radical))).mul_mem hz.2
      ((centralizer (A : Set (FreeAmalgam d.radical))).inv_mem (hCA hc))
    simpa only [mul_inv_cancel_right] using hh
  have huJ : u ∈ centralizer (J : Set (FreeAmalgam d.radical)) :=
    (large_actor_moving_fixed h d geometry hb ha hat A hAJ hlarge ▸
      (show u ∈ U d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) from ⟨hu,huA⟩)).2
  exact (centralizer (J : Set (FreeAmalgam d.radical))).mul_mem huJ (hCJ hc)

private theorem mover_fixed_X_le_seed
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    X d.radical a ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) ≤
      Z d.radical a := by
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel
    d.radical (h.replacement_two_group d) (h.replacement_core_le d) ha
  have hS : Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb.le,←MonoidHom.range_eq_map,hir]
  have hUX : U d.radical a ≤ X d.radical a := (U_le_Z a).trans
    (geometry.omega_bound a ha (by
      rw [geometry.distance_constant a ha]
      exact lt_of_lt_of_le (by decide : 0 < 4) hb.le))
  have hNU : fixedCore d.radical a ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (show fixedCore d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1.1).trans
      (U_normalized a)
  intro x hx
  have hxin := h.replacement_small_mover_X_centralizer d geometry hb.le ha hat hx
  have hxprod : x ∈ (U d.radical a : Set (FreeAmalgam d.radical))*
      (fixedCore d.radical a : Set _) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hNU]
    exact hxin
  obtain ⟨u,hu,c,hc,he⟩ := hxprod
  have hcX : c ∈ X d.radical a := by
    have hh := (X d.radical a).mul_mem ((X d.radical a).inv_mem (hUX hu)) hx.1
    simpa only [←he,inv_mul_cancel_left] using hh
  have hcS : c ∈ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hL : Ltilde d.radical a ≤ centralizer ({c} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hc.2 y hy)
    have hQ : Q d.radical a ≤ centralizer ({c} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr
        (Q_le_centralizer_X d.radical a hy c hcX).symm
    intro y hy
    exact mem_centralizer_singleton_iff.mp ((sup_le hL hQ) (hS.symm ▸ hy))
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases ht : color d.radical t <;> simp_all
  have hcZt : c ∈ Z d.radical t := by
    rw [Z,if_neg (by rw [ht]; decide)]
    obtain ⟨hcQ,hc2,_⟩ := mem_omegaCenter_iff.mp hcX
    exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h d.radical ht hat hcQ,hc2,
      fun y hy => hcS y (hy.2 a (adjacent_symm _ hat))⟩
  rw [←he]
  exact (Z d.radical a).mul_mem (U_le_Z a hu) (adjacent_Z_le _ ha hat hcZt)

omit [CharP F 2] in
private theorem core_le_small_mover
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
    (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
    (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
    (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)))
  rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh

/-- A large actor in equal smaller movers carries every fixed part of the
original seed into the neighboring seed, retaining its entire fixed kernel. -/
theorem Input.replacement_equal_mover_large_actor_fixed_le_seed
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (A : Subgroup (FreeAmalgam d.radical))
    (hAJ : A ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2))
    (hlarge : Nat.card F < (Q d.radical a).relIndex A)
    (D : Subgroup (FreeAmalgam d.radical)) (hDZ : D ≤ Z d.radical a)
    (hDA : ⁅D,A⁆=⊥) :
    D ≤ Z d.radical c ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hc : color d.radical c=false := by
    have ha' := adjacent_color_ne d.radical hat
    have hc' := adjacent_color_ne d.radical hct
    rw [ha] at ha'
    cases ht : color d.radical t <;> cases hc : color d.radical c <;> simp_all
  have hDJ : D ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    (le_inf hDZ (commutator_eq_bot_iff_le_centralizer.mp hDA)).trans
      (large_actor_seed_fixed h d geometry hb ha hat A hAJ hlarge)
  have hQcJ : Q d.radical c ≤ J := by
    dsimp only [J]
    rw [←hequal]
    exact core_le_small_mover h d hc hct
  have hZaQc : Z d.radical a ≤ Q d.radical c :=
    (le_sup_left.trans (neighbor_seed_join_le_radius hct hat)).trans
      (geometry.V_le_Q (by omega) c hc)
  have hDX : D ≤ X d.radical c := by
    let := geometry.Z_elementary (by omega) a ha
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hZaQc (hDZ hx),
      elemPow_eq_one_of_isElementaryAbelian x (hDZ hx),centralizer_le hQcJ (hDJ hx)⟩
  refine le_inf ?_ hDJ
  apply (le_inf hDX hDJ).trans
  simpa only [hequal] using mover_fixed_X_le_seed h d geometry hb hc hct

/-- On an actual critical path, the proved mover agreement supplies the
neighboring-seed conclusion without an additional equal-mover premise. -/
theorem Input.replacement_path_large_actor_fixed_le_next_seed
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAJ : A ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hlarge : Nat.card F < (Q d.radical a).relIndex A)
    (D : Subgroup (FreeAmalgam d.radical)) (hDZ : D ≤ Z d.radical a)
    (hDA : ⁅D,A⁆=⊥) :
    D ≤ Z d.radical (path.walk.getVert 2) ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
  have hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
      (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1))
      (Nat.card F^2) = Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) := by
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
      using h.replacement_mover_agreement_of_four_lt d ⟨a,z,path⟩ hb
  exact h.replacement_equal_mover_large_actor_fixed_le_seed d geometry hb
    path.start_color hat hct hequal A hAJ hlarge D hDZ hDA

/-- The entire kernel at the next same-color vertex is already inside the
equal mover. Thus its large intersection with any actor has the same next-seed
conclusion, including the literal radius kernel in the second source branch. -/
theorem Input.replacement_path_kernel_large_actor_fixed_le_next_seed
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (E : Subgroup (FreeAmalgam d.radical))
    (hlarge : Nat.card F < (Q d.radical a).relIndex
      (E ⊓ Q d.radical (path.walk.getVert 2)))
    (D : Subgroup (FreeAmalgam d.radical)) (hDZ : D ≤ Z d.radical a)
    (hDA : ⁅D,E ⊓ Q d.radical (path.walk.getVert 2)⁆=⊥) :
    D ≤ Z d.radical (path.walk.getVert 2) ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  have hc : color d.radical (path.walk.getVert 2)=false :=
    (path.vertex_color (by rw [path.length_eq_b]; omega : 2 ≤ path.walk.length)).mpr (by decide)
  have hct : Adjacent d.radical (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
  have hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
      (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1))
      (Nat.card F^2) = Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) := by
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
      using h.replacement_mover_agreement_of_four_lt d ⟨a,z,path⟩ hb
  apply h.replacement_path_large_actor_fixed_le_next_seed d path hb
    (E ⊓ Q d.radical (path.walk.getVert 2)) _ hlarge D hDZ hDA
  rw [←hequal]
  exact inf_le_right.trans (core_le_small_mover h d hc hct)

/-- The radius at the penultimate same-color vertex lies in the next
kernel. Its large image therefore gives the literal first source alternative. -/
theorem Input.replacement_path_penultimate_radius_large_actor_fixed_le_next_seed
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hlarge : Nat.card F < (Q d.radical a).relIndex
      (V d.radical (path.walk.getVert (geometry.b d.radical-2))))
    (D : Subgroup (FreeAmalgam d.radical)) (hDZ : D ≤ Z d.radical a)
    (hDA : ⁅D,V d.radical (path.walk.getVert (geometry.b d.radical-2))⁆=⊥) :
    D ≤ Z d.radical (path.walk.getVert 2) ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hp : color d.radical (path.walk.getVert (path.walk.length-2))=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.shortest,path.critical.1]
      exact geometry.even a path.start_color
    rw [Nat.even_iff] at he ⊢
    omega
  have hVQ : V d.radical (path.walk.getVert (geometry.b d.radical-2)) ≤
      Q d.radical (path.walk.getVert 2) := by
    rw [←path.length_eq_b]
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := geometry) hp
    rw [SimpleGraph.dist_comm]
    have hh := SimpleGraph.dist_le ((path.walk.drop 2).take (path.walk.length-4))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_getVert,
      show 2+(path.walk.length-4)=path.walk.length-2 by omega] at hh
    have hi := hh.trans (min_le_right _ _)
    change (cosetGraph d.radical).dist (path.walk.getVert 2)
      (path.walk.getVert (path.walk.length-2)) + 2 < geometry.b d.radical
    have hlength := path.length_eq_b
    omega
  have hh := h.replacement_path_kernel_large_actor_fixed_le_next_seed d path hb
    (V d.radical (path.walk.getVert (geometry.b d.radical-2)))
    (by simpa only [inf_eq_left.mpr hVQ] using hlarge) D hDZ
    (by simpa only [inf_eq_left.mpr hVQ] using hDA)
  exact hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
