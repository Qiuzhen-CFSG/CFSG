module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedCoreTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.KernelDichotomy
public import Theory.Frattini.InvolutorySupplement

/-!
# The complete paired Frattini factors at distance two

In the field-sized branch Q_a = U_a C_{Q_a}(L_a), with U_a central
and elementary in Q_a. Every square of Q_a is consequently a square of
its full fixed part. That part lies in Q_z, and the reverse transfer gives
identical square sets, derived subgroups and embedded Frattini subgroups
for Q_a and Q_z. The common Frattini subgroup belongs to both fixed parts.
If the two moving-layer fixed kernels differ, their established disjointness
makes this Frattini subgroup disjoint from both moving layers.

The edge factorization T = Q_a Z_z now gives the exact formula
Phi(T) = Phi(Q_a)[Z_a,Z_z]. In the unequal-kernel case these two factors
are disjoint. Transporting the actual involutory supplement through the
free-amalgam embedding gives Phi(d.radical) = Phi(O_2(d.overgroup))
[O_2(d.overgroup),d.radical], with the complete fixed contribution retained.

The proper nonsylow applications derive the field-sized premise from the
ORIGINAL odd-index witness. These results do not eliminate the unequal
fixed kernels or prove original-radical saturation, the Sylow branch, or
n = 2. Those remain required for the final distance-two block recognition.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7), especially the fixed-part comparisons on printed pp.874--876.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition

private theorem square_values_of_central_supplement {G : Type*} [Group G]
    (Q U D : Subgroup G) (hQ : Q=U⊔D)
    (hU : U ≤ centralizer (Q : Set G)) (hpow : ∀ u ∈ U, u^2=1) :
    ∀ x ∈ Q, ∃ c ∈ D, x^2=c^2 := by
  have hDQ : D ≤ Q := hQ ▸ le_sup_right
  have hUD : U ≤ centralizer (D : Set G) := hU.trans (centralizer_le hDQ)
  intro x hx
  rw [hQ,←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    (hUD.trans (Subgroup.centralizer_le_normalizer _))] at hx
  obtain ⟨u,hu,c,hc,rfl⟩ := hx
  refine ⟨c,hc,?_⟩
  have huc : Commute u c := (hUD hu c hc).symm
  rw [huc.mul_pow,hpow u hu,one_mul]

private theorem derived_eq_of_central_supplement {G : Type*} [Group G]
    (Q U D : Subgroup G) (hQ : Q=U⊔D)
    (hU : U ≤ centralizer (Q : Set G)) : ⁅Q,Q⁆=⁅D,D⁆ := by
  have hDQ : D ≤ Q := hQ ▸ le_sup_right
  have hQD : Q ≤ D ⊔ centralizer (Q : Set G) := by
    calc
      Q = U ⊔ D := hQ
      _ ≤ D ⊔ centralizer (Q : Set G) := sup_le (hU.trans le_sup_right) le_sup_left
  have hDU : U ≤ centralizer (D : Set G) := hU.trans (centralizer_le hDQ)
  have hnD : D ≤ normalizer (Q : Set G) := hDQ.trans Q.le_normalizer
  have hnQ : D ≤ normalizer (D : Set G) := D.le_normalizer
  apply le_antisymm _ (commutator_mono hDQ hDQ)
  apply (commutator_le_moving_of_inner_mod_centralizer Q D Q hnD hQD).trans
  rw [commutator_comm Q D]
  apply commutator_le_moving_of_inner_mod_centralizer D D Q hnQ
  calc
    Q = U ⊔ D := hQ
    _ ≤ D ⊔ centralizer (D : Set G) := sup_le (hDU.trans le_sup_right) le_sup_left


variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Every square of the full kernel is already a square of its complete
component-fixed part. -/
theorem replacement_field_sized_fixedCore_squares
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ∀ x ∈ Q d.radical a, ∃ c ∈ fixedCore d.radical a, x^2=c^2 := by
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  apply square_values_of_central_supplement (Q d.radical a) (U d.radical a)
    (fixedCore d.radical a) (replacement_field_sized_Q_decomposition h d path hb hat hzt hsize)
    ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a path.start_color)))
  intro u hu
  exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (Z d.radical a)) ⟨u,U_le_Z a hu⟩)

/-- The paired full local two-cores have exactly the same squares, before
any fixed attachment or central layer is factored out. -/
theorem replacement_field_sized_paired_square_values
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    Set.range (fun x : Q d.radical a => (x : FreeAmalgam d.radical)^2) =
      Set.range (fun x : Q d.radical z => (x : FreeAmalgam d.radical)^2) := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  apply Set.Subset.antisymm
  · rintro _ ⟨x,rfl⟩
    obtain ⟨c,hc,he⟩ := replacement_field_sized_fixedCore_squares h d path hb hat hzt hsize x x.property
    exact ⟨⟨c,replacement_field_sized_fixedCore_le_opposite h d path hb hat hzt hsize hc⟩,he.symm⟩
  · rintro _ ⟨x,rfl⟩
    obtain ⟨c,hc,he⟩ := replacement_field_sized_fixedCore_squares h d rev hb hzt hat hsize x x.property
    exact ⟨⟨c,replacement_field_sized_fixedCore_le_opposite h d rev hb hzt hat hsize hc⟩,he.symm⟩

/-- Derived subgroups also agree, using both complete fixed-part transfers. -/
theorem replacement_field_sized_paired_derived
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ⁅Q d.radical a,Q d.radical a⁆ = ⁅Q d.radical z,Q d.radical z⁆ := by
  have heq (a z t : Vertex d.radical) (p : CriticalPath d.radical g a z)
      (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
      ⁅Q d.radical a,Q d.radical a⁆ = ⁅fixedCore d.radical a,fixedCore d.radical a⁆ :=
    derived_eq_of_central_supplement _ _ _
      (replacement_field_sized_Q_decomposition h d p hb hat hzt hsize)
      ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  apply le_antisymm
  · rw [heq a z t path hat hzt]
    exact commutator_mono
      (replacement_field_sized_fixedCore_le_opposite h d path hb hat hzt hsize)
      (replacement_field_sized_fixedCore_le_opposite h d path hb hat hzt hsize)
  · rw [heq z a t rev hzt hat]
    exact commutator_mono
      (replacement_field_sized_fixedCore_le_opposite h d rev hb hzt hat hsize)
      (replacement_field_sized_fixedCore_le_opposite h d rev hb hzt hat hsize)


omit h in
private theorem frattini_image_eq_square_closure {G : Type*} [Group G]
    (A : Subgroup G) [Finite A] (hp : IsPGroup 2 A) :
    (frattini A).map A.subtype = closure (Set.range (fun x : A => (x:G)^2)) := by
  rw [hp.frattini_eq_closure_squares,MonoidHom.map_closure,←Set.range_comp]
  rfl

/-- The full Frattini subgroup lies in the full fixed part, because its
square generators can all be chosen there. -/
theorem replacement_field_sized_frattini_le_fixedCore
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    (frattini (Q d.radical a)).map (Q d.radical a).subtype ≤ fixedCore d.radical a := by
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  rw [frattini_image_eq_square_closure _
    (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color)]
  apply (closure_le _).mpr
  rintro _ ⟨x,rfl⟩
  obtain ⟨c,hc,he⟩ := replacement_field_sized_fixedCore_squares h d path hb hat hzt hsize x x.property
  change (x : FreeAmalgam d.radical)^2 ∈ fixedCore d.radical a
  rw [he]
  exact (fixedCore d.radical a).pow_mem hc 2

/-- The actual paired Frattini images agree and belong to both complete
fixed parts. No quotient or elementary hypothesis on those parts is imposed. -/
theorem replacement_field_sized_paired_frattini
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    (frattini (Q d.radical a)).map (Q d.radical a).subtype =
        (frattini (Q d.radical z)).map (Q d.radical z).subtype ∧
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ≤
        fixedCore d.radical a ⊓ fixedCore d.radical z := by
  let := finite_stabilizer d.radical a
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Finite (Q d.radical z) := Finite.of_injective
    (inclusion (show Q d.radical z ≤ stabilizer d.radical z from fun _ hx => hx.1))
    (inclusion_injective _)
  have heq : (frattini (Q d.radical a)).map (Q d.radical a).subtype =
      (frattini (Q d.radical z)).map (Q d.radical z).subtype := by
    rw [frattini_image_eq_square_closure _
        (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color),
      frattini_image_eq_square_closure _
        (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) z path.end_color),
      replacement_field_sized_paired_square_values h d path hb hat hzt hsize]
  refine ⟨heq,le_inf (replacement_field_sized_frattini_le_fixedCore h d path hb hat hzt hsize) ?_⟩
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  rw [heq]
  exact replacement_field_sized_frattini_le_fixedCore h d rev hb hzt hat hsize

/-- In the unequal-kernel case the full moving core meets the actual
Frattini subgroup trivially. This retains the Frattini subgroup itself. -/
theorem replacement_field_sized_frattini_disjoint_of_fixed_ne
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    Disjoint (U d.radical a) ((frattini (Q d.radical a)).map (Q d.radical a).subtype) := by
  have hd := (replacement_field_sized_fixed_kernels_eq_or_disjoint h d path hb hat hzt hsize).resolve_left hne
  have hphi := (replacement_field_sized_paired_frattini h d path hb hat hzt hsize).2
  obtain ⟨_,hAW,hWU,_,_⟩ := replacement_field_sized_paired_fixed_layers h d path hb hat hzt hsize
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hxA : x ∈ U d.radical a ⊓
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :=
    ⟨hx.1,(hphi hx.2).1.2⟩
  exact disjoint_iff_inf_le.mp hd ⟨hxA,⟨(hWU (hAW (mem_sup_left hxA))).2,(hphi hx.2).2.2⟩⟩

/-- The ORIGINAL odd-index witness supplies the field-sized premise for
both full Frattini images and the moving-core disjointness alternative. -/
theorem replacement_proper_nonsylow_paired_frattini_control
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let P := (frattini (Q d.radical a)).map (Q d.radical a).subtype
    let P' := (frattini (Q d.radical z)).map (Q d.radical z).subtype
    P=P' ∧ P ≤ fixedCore d.radical a ⊓ fixedCore d.radical z ∧
      (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
        U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ∨
        Disjoint (U d.radical a) P ∧ Disjoint (U d.radical z) P') := by
  classical
  have hs := replacement_proper_nonsylow_card h d g hb hnsyl hne
  obtain ⟨he,hf⟩ := replacement_field_sized_paired_frattini h d path hb hat hzt hs
  refine ⟨he,hf,?_⟩
  by_cases hk : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  · exact Or.inl hk
  right
  refine ⟨replacement_field_sized_frattini_disjoint_of_fixed_ne h d path hb hat hzt hs hk,?_⟩
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  exact replacement_field_sized_frattini_disjoint_of_fixed_ne h d rev hb hzt hat hs (Ne.symm hk)


/-- The full edge Frattini subgroup is the critical displacement times the
common kernel Frattini subgroup. The latter factor is retained verbatim. -/
theorem replacement_field_sized_edge_frattini
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    (frattini (Q d.radical t)).map (Q d.radical t).subtype =
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔
        ⁅Z d.radical a,Z d.radical z⁆ := by
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  let := finite_stabilizer d.radical t
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (Q_le_adjacent_h d.radical ht hat)) (inclusion_injective _)
  have hpT : IsPGroup 2 (Q d.radical t) := by
    have he : ∃ v, t = hVertex d.radical v := by
      cases t with
      | inl q => cases ht
      | inr q =>
        induction q using Quotient.inductionOn
        exact ⟨_,rfl⟩
    obtain ⟨v,rfl⟩ := he
    have hm := Q_act d.radical v (beta d.radical)
    simp only [beta,act_hVertex,one_mul] at hm
    rw [hm]
    change IsPGroup 2 ((Q d.radical (beta d.radical)).map _)
    rw [Q_beta]
    exact ((replacement_isPGroup h d).map (embedM d.radical)).map _
  have hZt : Z d.radical z ≤ Q d.radical t := by
    rw [←(replacement_field_sized_paired_edges h d path hb hat hzt hsize).1]
    exact le_sup_right
  have hn : Z d.radical z ≤ normalizer (Q d.radical a : Set (FreeAmalgam d.radical)) := by
    apply (hZt.trans ?_).trans (Q_normalized d.radical a)
    rw [Q_h_eq_edge d.radical ht hat]
    exact inf_le_left
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have he := frattini_map_eq_of_involutory_supplement (Q d.radical t) (Q d.radical a)
    (Z d.radical z) hpT
    (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color)
    (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1 hn
    (fun x hx => congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Z d.radical z)) ⟨x,hx⟩))
  rwa [replacement_field_sized_whole_kernel_commutator h d path hb hat hzt hsize] at he

/-- With unequal fixed kernels, the retained Frattini factor and the
critical displacement are disjoint factors of the full edge Frattini subgroup. -/
theorem replacement_proper_nonsylow_edge_frattini
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let P := (frattini (Q d.radical a)).map (Q d.radical a).subtype
    let W := ⁅Z d.radical a,Z d.radical z⁆
    (frattini (Q d.radical t)).map (Q d.radical t).subtype = P ⊔ W ∧
      (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
        U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ∨
        Disjoint W P) := by
  have hs := replacement_proper_nonsylow_card h d g hb hnsyl hne
  refine ⟨replacement_field_sized_edge_frattini h d path hb hat hzt hs,?_⟩
  rcases (replacement_proper_nonsylow_paired_frattini_control h d path hb hat hzt hnsyl hne).2.2 with he | hd
  · exact Or.inl he
  · right
    have hWU := (replacement_field_sized_paired_fixed_layers h d path hb hat hzt hs).2.2.1
    exact hd.1.mono_left (hWU.trans inf_le_left)

/-- Exact Frattini control on the literal replacement radical and two-core.
The formula keeps the entire core Frattini subgroup. -/
theorem replacement_field_sized_radical_frattini
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    (frattini d.radical).map d.radical.subtype =
      (frattini (pCore 2 d.overgroup)).map (pCore 2 d.overgroup).subtype ⊔
        ⁅pCore 2 d.overgroup,d.radical⁆ := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := alpha d.radical) rfl
  have hd : (cosetGraph d.radical).dist (alpha d.radical) z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) z hd
  have hab : Adjacent d.radical (alpha d.radical) (beta d.radical) :=
    (adjacent_iff_exists_common d.radical _ _).mpr ⟨1,Or.inl ⟨rfl,rfl⟩⟩
  obtain ⟨v,hv,hvt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hab hat
  let f := (MulAut.conj v⁻¹).toMonoidHom.comp (embedM d.radical)
  have hf : Function.Injective f := (MulAut.conj v⁻¹).injective.comp (embedM_injective d.radical)
  have hmT : d.radical.map f = Q d.radical t := by
    dsimp only [f]
    rw [←Subgroup.map_map,←Q_beta,←Q_act,hvt]
  have hmQ : (pCore 2 d.overgroup).map f = Q d.radical (alpha d.radical) := by
    dsimp only [f]
    rw [←Subgroup.map_map,←Q_alpha d.radical (replacement_isPGroup h d) (replacement_core_le h d),
      ←Q_act,hv]
  let E := (Z d.radical z).comap f
  have hZT : Z d.radical z ≤ Q d.radical t := by
    rw [←(replacement_field_sized_paired_edges h d path hb hat hzt hsize).1]
    exact le_sup_right
  have hmE : E.map f=Z d.radical z := by
    change ((Z d.radical z).comap f).map f=Z d.radical z
    rw [map_comap_eq]
    exact inf_eq_right.mpr (hZT.trans (hmT ▸ map_le_range f d.radical))
  have hgen : pCore 2 d.overgroup ⊔ E=d.radical := by
    apply map_injective hf
    rw [Subgroup.map_sup,hmQ,hmE,hmT]
    exact (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hE : ∀ e ∈ E, e^2=1 := by
    intro e he
    apply hf
    rw [map_pow,map_one]
    exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Z d.radical z)) ⟨f e,he⟩)
  exact frattini_map_eq_commutator_sup_of_involutory_supplement _ _ _ (replacement_isPGroup h d) pCore_isPGroup
    hgen (by rw [normalizer_eq_top]; exact le_top) hE

/-- Apply the literal Frattini formula using the ORIGINAL odd-index witness. -/
theorem replacement_proper_nonsylow_radical_frattini
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    (frattini d.radical).map d.radical.subtype =
      (frattini (pCore 2 d.overgroup)).map (pCore 2 d.overgroup).subtype ⊔
        ⁅pCore 2 d.overgroup,d.radical⁆ :=
  replacement_field_sized_radical_frattini h d g hb
    (replacement_proper_nonsylow_card h d g hb hnsyl hne)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
