module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.OriginalLayers

/-!
# Full-edge squares distinguish the paired fixed kernels

In the field-sized branch, every edge element is a product of the complete
fixed attachment and elements of the two elementary moving layers. Its square
is therefore a square of that attachment times one individual critical
commutator. When the two full fixed kernels differ, the fixed Frattini factor
is disjoint from the moving layer. A square lying in the common displacement
then has trivial fixed-factor contribution.

The nonidentity squares in the common displacement are exactly the elements
outside both full fixed kernels. An automorphism of the full edge preserving
that displacement must consequently permute the two kernels: a subgroup
contained in their union lies in one factor, and their equal orders give
equality. The original odd-index witness supplies the field-sized premise
in the proper nonsylow applications.

This is an intrinsic square-map constraint, retaining all fixed attachments
and arbitrary original field degree. It does not assert that the common
displacement is characteristic in the original radical or exclude exchange
of the kernels. Those steps and the field restriction remain necessary.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(4), printed p.875, together with the original-radical comparison
on pp.872--877. The square characterization refines the individual-commutator
comparison for use in that characteristic-subgroup argument.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- With unequal full kernels, individual critical commutators are precisely
identity and the elements outside both kernels in the common displacement. -/
theorem replacement_field_sized_commutator_values
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (x : FreeAmalgam d.radical) (hx : x ∈ ⁅Z d.radical a,Z d.radical z⁆) :
    (∃ b ∈ U d.radical z, ∃ u ∈ U d.radical a, ⁅b,u⁆=x) ↔
      x=1 ∨ (x ∉ U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ∧
        x ∉ U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) := by
  classical
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  constructor
  · rintro ⟨b,hbU,u,hu,rfl⟩
    by_cases he : ⁅b,u⁆=1
    · exact Or.inl he
    right
    constructor
    · intro hf
      exact he (replacement_field_sized_value_in_fixed_eq_one h d path hb hat hzt hsize
        b (U_le_Z z hbU) u hu hf.2)
    · intro hf
      have hi : ⁅u,b⁆ ∈ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
        rw [←commutatorElement_inv]
        exact inv_mem hf.2
      have hc := replacement_field_sized_value_in_fixed_eq_one h d rev hb hzt hat hsize
        u (U_le_Z a hu) b hbU hi
      exact he (commutatorElement_eq_one_iff_commute.mpr
        (commutatorElement_eq_one_iff_commute.mp hc).symm)
  · rintro (rfl | ⟨ha,hz⟩)
    · exact ⟨1,one_mem _,1,one_mem _,by simp⟩
    rcases replacement_field_sized_value_or_overlap h d path hb hat hzt hsize x hx ha with ho | hv
    · exact (hz ((replacement_field_sized_opposite_fixed_eq_overlap h d path hb hat hzt hsize hne).symm ▸ ho)).elim
    · exact hv

/-- Squares of the full edge retain the square of its complete fixed factor. -/
theorem replacement_field_sized_edge_square_values
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (x : FreeAmalgam d.radical) :
    (∃ y ∈ Q d.radical t, y^2=x) ↔
      ∃ c ∈ fixedCore d.radical a, ∃ b ∈ U d.radical z, ∃ u ∈ U d.radical a,
        c^2*⁅b,u⁆=x := by
  let G := FreeAmalgam d.radical
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hpow (v : Vertex d.radical) [IsElementaryAbelian 2 (Z d.radical v)]
      (u : G) (hu : u ∈ Z d.radical v) : u^2=1 :=
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Z d.radical v)) ⟨u,hu⟩)
  have hCa : fixedCore d.radical a ≤ centralizer (U d.radical a : Set G) :=
    le_centralizer_iff.mp (((U_le_Z a).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color))).trans
      (centralizer_le inf_le_left))
  have hCz : fixedCore d.radical a ≤ centralizer (Z d.radical z : Set G) :=
    replacement_field_sized_fixedCore_centralizes_opposite h d path hb hat hzt hsize
  have hnormal : Z d.radical z ≤ normalizer (Q d.radical a : Set G) := by
    apply (Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color) ?_).trans
      (Q_normalized d.radical a)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have htQ : Z d.radical t ≤ Q d.radical a :=
    (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat).trans
      ((g.omega_bound a path.start_color (by
        rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
        (omegaCenter_le _))
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hjoin : U d.radical z ⊔ Q d.radical a = Q d.radical t := by
    have hh := (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1
    rw [(replacement_field_sized_central_layers h d rev hb hzt hat hsize).2] at hh
    rwa [sup_left_comm, sup_of_le_left htQ] at hh
  have hsquare (c b u : G) (hc : c ∈ fixedCore d.radical a)
      (hbU : b ∈ U d.radical z) (hu : u ∈ U d.radical a) :
      (c*(b*u))^2=c^2*⁅b,u⁆ := by
    have hcb : Commute c b := (hCz hc b (U_le_Z z hbU)).symm
    have hcu : Commute c u := (hCa hc u hu).symm
    rw [(hcb.mul_right hcu).mul_pow]
    have hbInv : b⁻¹=b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hpow z b (U_le_Z z hbU))
    have huInv : u⁻¹=u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hpow a u (U_le_Z a hu))
    simp only [commutatorElement_def,hbInv,huInv,pow_two,mul_assoc]
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hprod : y ∈ U d.radical z ⊔ Q d.radical a := hjoin.symm ▸ hy
    rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
      ((U_le_Z z).trans hnormal)] at hprod
    obtain ⟨b,hbU,q,hq,rfl⟩ := hprod
    change q ∈ Q d.radical a at hq
    rw [replacement_field_sized_Q_decomposition h d path hb hat hzt hsize] at hq
    change q ∈ ((U d.radical a ⊔ fixedCore d.radical a : Subgroup G) : Set G) at hq
    rw [coe_mul_of_right_le_normalizer_left _ _
      (hCa.trans (Subgroup.centralizer_le_normalizer _))] at hq
    obtain ⟨u,hu,c,hc,rfl⟩ := hq
    have hcb : Commute c b := (hCz hc b (U_le_Z z hbU)).symm
    have hcu : Commute c u := (hCa hc u hu).symm
    refine ⟨c,hc,b,hbU,u,hu,?_⟩
    rw [←hsquare c b u hc hbU hu]
    congr 1
    rw [←mul_assoc,hcb.eq,mul_assoc,hcu.eq]
  · rintro ⟨c,hc,b,hbU,u,hu,rfl⟩
    refine ⟨c*(b*u),?_,hsquare c b u hc hbU hu⟩
    rw [←(replacement_field_sized_paired_edges h d path hb hat hzt hsize).1]
    exact mul_mem (mem_sup_left hc.1)
      (mul_mem (mem_sup_right (U_le_Z z hbU)) (mem_sup_left
        (((U_le_Z a).trans ((g.omega_bound a path.start_color (by
          rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
          (omegaCenter_le _))) hu)))

/-- A square in the common displacement cannot acquire a nontrivial square
from the retained fixed attachment. -/
theorem replacement_field_sized_squares_in_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (x : FreeAmalgam d.radical) (hx : x ∈ ⁅Z d.radical a,Z d.radical z⁆) :
    (∃ y ∈ Q d.radical t, y^2=x) ↔
      x=1 ∨ (x ∉ U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ∧
        x ∉ U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) := by
  rw [←replacement_field_sized_commutator_values h d path hb hat hzt hsize hne x hx,
    replacement_field_sized_edge_square_values h d path hb hat hzt hsize]
  constructor
  · rintro ⟨c,hc,b,hbU,u,hu,he⟩
    have hd : Disjoint (U d.radical a)
        ((frattini (Q d.radical a)).map (Q d.radical a).subtype) :=
      replacement_field_sized_frattini_disjoint_of_fixed_ne h d path hb hat hzt hsize hne
    let := finite_stabilizer d.radical a
    let : Finite (Q d.radical a) := Finite.of_injective
      (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
      (inclusion_injective _)
    let : Fact (IsPGroup 2 (Q d.radical a)) := ⟨Q_isPGroup d.radical
      (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color⟩
    have hcPhi : c^2 ∈ (frattini (Q d.radical a)).map (Q d.radical a).subtype :=
      mem_map_of_mem (Q d.radical a).subtype
        (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨c,hc.1⟩ : Q d.radical a))
    have hbu : ⁅b,u⁆ ∈ ⁅Z d.radical a,Z d.radical z⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator (U_le_Z z hbU) (U_le_Z a hu)
    have hcW : c^2 ∈ ⁅Z d.radical a,Z d.radical z⁆ := by
      have hh := mul_mem hx (inv_mem hbu)
      rwa [←he,mul_inv_cancel_right] at hh
    have hWU : ⁅Z d.radical a,Z d.radical z⁆ ≤ U d.radical a :=
      (replacement_field_sized_paired_fixed_layers h d path hb hat hzt hsize).2.2.1.trans inf_le_left
    have hc1 : c^2=1 := disjoint_iff_inf_le.mp hd ⟨hWU hcW,hcPhi⟩
    exact ⟨b,hbU,u,hu,by simpa only [hc1,one_mul] using he⟩
  · rintro ⟨b,hbU,u,hu,he⟩
    exact ⟨1,one_mem _,b,hbU,u,hu,by simpa using he⟩

/-- Every automorphism of the full edge preserving its common displacement
permutes the two complete fixed kernels. -/
theorem replacement_field_sized_square_kernel_pair
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (f : MulAut (Q d.radical t))
    (hW : ((⁅Z d.radical a,Z d.radical z⁆).subgroupOf (Q d.radical t)).map
      ((Q d.radical t).subtype.comp f.toMonoidHom)=⁅Z d.radical a,Z d.radical z⁆) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    let m := (Q d.radical t).subtype.comp f.toMonoidHom
    ((A.subgroupOf (Q d.radical t)).map m=A ∧ (A'.subgroupOf (Q d.radical t)).map m=A') ∨
      ((A.subgroupOf (Q d.radical t)).map m=A' ∧ (A'.subgroupOf (Q d.radical t)).map m=A) := by
  classical
  let G := FreeAmalgam d.radical
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set G)
  let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set G)
  let W := ⁅Z d.radical a,Z d.radical z⁆
  obtain ⟨hdis,hA,hA',hjoin⟩ :=
    (replacement_field_sized_fixed_kernels_dichotomy h d path hb hat hzt hsize).resolve_left hne
  have hAm : A ≤ W := le_sup_left.trans_eq hjoin
  have hA'm : A' ≤ W := le_sup_right.trans_eq hjoin
  let := finite_Z d.radical a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a)))
    (inclusion_injective _)
  let : Finite A' := Finite.of_injective
    (inclusion (hA'm.trans ((replacement_field_sized_paired_fixed_layers h d path hb hat hzt hsize).2.2.1.trans
      inf_le_left |>.trans (U_le_Z a)))) (inclusion_injective _)
  have hcard : Nat.card A=Nat.card A' := hA.trans hA'.symm
  let T := Q d.radical t
  let m := T.subtype.comp f.toMonoidHom
  have hm : Function.Injective m := T.subtype_injective.comp f.injective
  have hmW : (W.subgroupOf T).map m=W := hW
  have hWT : W ≤ T := by
    have hWU := (replacement_field_sized_paired_fixed_layers h d path hb hat hzt hsize).2.2.1.trans inf_le_left
    have ht : color d.radical t = true := by
      have hn := adjacent_color_ne d.radical hat
      cases ht : color d.radical t <;> simp_all [path.start_color]
    exact hWU.trans ((U_le_Z a).trans ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans (Q_le_adjacent_h d.radical ht hat))))
  have hAT : A ≤ T := hAm.trans hWT
  have hA'T : A' ≤ T := hA'm.trans hWT
  have hsquare (x : T) : (∃ y ∈ T, y^2=m x) ↔ ∃ y ∈ T, y^2=x.val := by
    constructor
    · rintro ⟨y,hy,he⟩
      let v : T := f.symm ⟨y,hy⟩
      have hv : m v=y := congrArg Subtype.val (f.apply_symm_apply ⟨y,hy⟩)
      refine ⟨v,v.property,?_⟩
      have hh : v^2=x := hm (by rw [map_pow,hv,he])
      exact congrArg Subtype.val hh
    · rintro ⟨y,hy,he⟩
      refine ⟨m ⟨y,hy⟩,(f ⟨y,hy⟩).property,?_⟩
      have hh : (⟨y,hy⟩ : T)^2=x := Subtype.ext he
      rw [←map_pow,hh]
  have himage (B : Subgroup G) (hBW : B ≤ W)
      (hB : B ≤ A ∨ B ≤ A') : (B.subgroupOf T).map m ≤ A ∨ (B.subgroupOf T).map m ≤ A' := by
    apply SubgroupClass.subset_union.mp
    rintro _ ⟨x,hx,rfl⟩
    by_cases hx1 : x=1
    · simp only [hx1,map_one]
      exact Or.inl (one_mem _)
    have hxval : x.val ≠ 1 := fun he => hx1 (Subtype.ext he)
    have hfxW : m x ∈ W := hmW ▸ mem_map_of_mem m (show x ∈ W.subgroupOf T from hBW hx)
    by_contra hh
    have hnot : m x ∉ A ∧ m x ∉ A' := not_or.mp hh
    have hsq := (replacement_field_sized_squares_in_displacement h d path hb hat hzt hsize hne
      (m x) hfxW).mpr (Or.inr hnot)
    have hxSq := (replacement_field_sized_squares_in_displacement h d path hb hat hzt hsize hne
      x.val (hBW hx)).mp ((hsquare x).mp hsq)
    rcases hxSq with he | ⟨ha,ha'⟩
    · exact hxval he
    · exact hB.elim (fun hBA => ha (hBA hx)) (fun hBA' => ha' (hBA' hx))
  have hca : Nat.card ((A.subgroupOf T).map m)=Nat.card A := by
    rw [card_map_of_injective hm]
    exact Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv
  have hcz : Nat.card ((A'.subgroupOf T).map m)=Nat.card A' := by
    rw [card_map_of_injective hm]
    exact Nat.card_congr (subgroupOfEquivOfLe hA'T).toEquiv
  have hfirst : (A.subgroupOf T).map m=A ∨ (A.subgroupOf T).map m=A' := by
    rcases himage A hAm (Or.inl le_rfl) with hle | hle
    · exact Or.inl (eq_of_le_of_card_ge hle hca.ge)
    · exact Or.inr (eq_of_le_of_card_ge hle (hca.trans hcard).ge)
  have hsecond : (A'.subgroupOf T).map m=A ∨ (A'.subgroupOf T).map m=A' := by
    rcases himage A' hA'm (Or.inr le_rfl) with hle | hle
    · exact Or.inl (eq_of_le_of_card_ge hle (hcz.trans hcard.symm).ge)
    · exact Or.inr (eq_of_le_of_card_ge hle hcz.ge)
  have hdistinct : (A.subgroupOf T).map m ≠ (A'.subgroupOf T).map m := by
    intro he
    have hh := congrArg (fun B : Subgroup T => B.map T.subtype) (map_injective hm he)
    rw [map_subgroupOf_eq_of_le hAT,map_subgroupOf_eq_of_le hA'T] at hh
    exact hne hh
  rcases hfirst with hfa | hfa <;> rcases hsecond with hfz | hfz
  · exact (hdistinct (hfa.trans hfz.symm)).elim
  · exact Or.inl ⟨hfa,hfz⟩
  · exact Or.inr ⟨hfa,hfz⟩
  · exact (hdistinct (hfa.trans hfz.symm)).elim

/-- The original odd-index witness supplies the square criterion on the full
edge group; both complete kernels and its fixed attachment are retained. -/
theorem replacement_proper_nonsylow_squares_in_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h))
    (hk : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (x : FreeAmalgam d.radical) (hx : x ∈ ⁅Z d.radical a,Z d.radical z⁆) :
    (∃ y ∈ Q d.radical t, y^2=x) ↔
      x=1 ∨ (x ∉ U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ∧
        x ∉ U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :=
  replacement_field_sized_squares_in_displacement h d path hb hat hzt
    (replacement_proper_nonsylow_card h d g hb hnsyl hne) hk x hx

/-- Original-witness application of the intrinsic edge-automorphism constraint.
The common displacement must still be preserved; this does not assert that
it is characteristic in the full original radical. -/
theorem replacement_proper_nonsylow_square_kernel_pair
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h))
    (hk : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (f : MulAut (Q d.radical t))
    (hW : ((⁅Z d.radical a,Z d.radical z⁆).subgroupOf (Q d.radical t)).map
      ((Q d.radical t).subtype.comp f.toMonoidHom)=⁅Z d.radical a,Z d.radical z⁆) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    let m := (Q d.radical t).subtype.comp f.toMonoidHom
    ((A.subgroupOf (Q d.radical t)).map m=A ∧ (A'.subgroupOf (Q d.radical t)).map m=A') ∨
      ((A.subgroupOf (Q d.radical t)).map m=A' ∧ (A'.subgroupOf (Q d.radical t)).map m=A) :=
  replacement_field_sized_square_kernel_pair h d path hb hat hzt
    (replacement_proper_nonsylow_card h d g hb hnsyl hne) hk f hW

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
