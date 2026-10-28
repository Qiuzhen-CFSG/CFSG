module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SharedCenter


/-!
# Faithful action on the full replacement center

The full natural cover lifts every vector fixed by the field-sized root.
The symplectic hyperplane-fixer theorem therefore identifies the centralizer
of the WHOLE edge center inside either endpoint group with the edge group
itself. This keeps the complete fixed attachment and the original field degree.
Transport through the literal replacement gives C_M(Z(T)) = T. Thus the
original radical restricted to M acts on Z(T) with kernel T and image of
order q squared, using its original odd-index witness.

When the paired full fixed kernels differ, the two normalizer cores move the
same center into complementary factors of the common displacement. They
centralize that displacement, so their joint action is elementary abelian
and their two action images are disjoint. Their intersection centralizes the
whole edge center. These are restrictions on the exchanged-kernel branch;
they do not exclude it or assert radical saturation or degree two.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7), printed pp.872--877;
in particular the shared-layer action in the kernel comparison on p.875.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition

private theorem joint_displacement {G : Type*} [Group G]
    (E B B' W : Subgroup G) (hB : B ≤ centralizer (W : Set G))
    (hB' : B' ≤ centralizer (W : Set G))
    (he : ⁅E,B⁆ ⊔ ⁅E,B'⁆=W) :
    ⁅E,B ⊔ B'⁆=W ∧ B ⊔ B' ≤ centralizer (W : Set G) := by
  have hc := sup_le hB hB'
  refine ⟨le_antisymm ?_ ?_,hc⟩
  · rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal (B ⊔ B') B B' E W
      (hc.trans (Subgroup.centralizer_le_normalizer _)) le_sup_left le_sup_right
    · rw [commutator_comm]; exact le_sup_left.trans_eq he
    · rw [commutator_comm]; exact le_sup_right.trans_eq he
  · rw [←he]
    exact sup_le (commutator_mono le_rfl le_sup_left) (commutator_mono le_rfl le_sup_right)

private theorem square_centralizes_of_quadratic {G : Type*} [Group G]
    (E B W : Subgroup G) (hm : ⁅E,B⁆ ≤ W)
    (hc : B ≤ centralizer (W : Set G)) (hp : ∀ w ∈ W, w^2=1)
    (b : G) (hb : b ∈ B) : b^2 ∈ centralizer (E : Set G) := by
  intro e he
  apply (commutatorElement_eq_one_iff_commute.mp ?_).symm.eq
  have hw : ⁅b,e⁆ ∈ W := hm (commutator_comm B E ▸ commutator_mem_commutator hb he)
  have hcomm : Commute b ⁅b,e⁆ := (hc hb ⁅b,e⁆ hw).symm
  rw [pow_two,commutatorElement_mul_left_eq_conj_mul,hcomm.eq,mul_inv_cancel_right,←pow_two,hp _ hw]

private theorem center_normalized {G : Type*} [Group G]
    (T B : Subgroup G) (hn : B ≤ normalizer (T : Set G)) :
    B ≤ normalizer ((T ⊓ centralizer (T : Set G) : Subgroup G) : Set G) := by
  intro b hb
  rw [mem_normalizer_iff_map_conj_eq,
    ←map_inf_centralizer_of_injective _ (MulAut.conj b).injective,
    mem_normalizer_iff_map_conj_eq.mp (hn hb)]

private theorem paired_action {G : Type*} [Group G]
    (E B B' W : Subgroup G)
    (hn : B ⊔ B' ≤ normalizer (E : Set G))
    (hm : ⁅E,B ⊔ B'⁆ ≤ W) (hc : B ⊔ B' ≤ centralizer (W : Set G))
    (hp : ∀ w ∈ W, w^2=1) (hd : Disjoint ⁅E,B⁆ ⁅E,B'⁆) :
    ∃ θ : ↥(B ⊔ B') →* MulAut E,
      (∀ (b : ↥(B ⊔ B')) (e : E), (θ b e : G)= (b:G)*(e:G)*(b:G)⁻¹) ∧
      IsElementaryAbelian 2 θ.range ∧
      Disjoint ((B.subgroupOf (B ⊔ B')).map θ) ((B'.subgroupOf (B ⊔ B')).map θ) := by
  let θ := E.normalizerMonoidHom.comp (inclusion hn)
  have hact (b : ↥(B ⊔ B')) (e : E) : (θ b e : G)= (b:G)*(e:G)*(b:G)⁻¹ := rfl
  refine ⟨θ,hact,?_,?_⟩
  · have hs : ∀ x : θ.range, x^2=1 := by
      rintro ⟨x,⟨b,rfl⟩⟩
      apply Subtype.ext
      change (θ b)^2=1
      rw [←map_pow]
      apply MulEquiv.ext
      intro e
      apply Subtype.ext
      change (θ (b^2) e : G)=(e:G)
      rw [hact]
      have hfix := square_centralizes_of_quadratic E (B ⊔ B') W hm hc hp b b.property
      change (b:G)^2*(e:G)*((b:G)^2)⁻¹=(e:G)
      rw [←hfix e e.property,mul_inv_cancel_right]
    have hi (x : θ.range) : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs x)
    let : IsMulCommutative θ.range := ⟨⟨fun x y => by
      calc
        x*y=(x*y)⁻¹ := (hi (x*y)).symm
        _=y*x := by rw [mul_inv_rev,hi x,hi y]⟩⟩
    exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs⟩
  · apply disjoint_iff_inf_le.mpr
    rintro x ⟨⟨b,hb,hbx⟩,⟨b',hb',hb'x⟩⟩
    have heq : θ b=θ b' := hbx.trans hb'x.symm
    change x=1
    rw [←hbx]
    apply MulEquiv.ext
    intro e
    apply Subtype.ext
    change (θ b e : G)=(e:G)
    have hval : ⁅(e:G),(b:G)⁆=⁅(e:G),(b':G)⁆ := by
      have hh := congrArg (fun f : MulAut E => (f e : G)) heq
      rw [hact,hact] at hh
      have hh' : ⁅(b:G),(e:G)⁆=⁅(b':G),(e:G)⁆ := by
        simpa only [commutatorElement_def,mul_assoc] using congrArg (fun z : G => z*(e:G)⁻¹) hh
      simpa only [commutatorElement_inv] using congrArg Inv.inv hh'
    have h1 : ⁅(e:G),(b:G)⁆=1 := disjoint_iff_inf_le.mp hd
      ⟨commutator_mem_commutator e.property hb,
        hval ▸ commutator_mem_commutator e.property hb'⟩
    rw [hact,←(commutatorElement_eq_one_iff_commute.mp h1).eq,mul_inv_cancel_right]

open Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour

private theorem embedded_root_center_centralizer
    {F G V : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [Group G] [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) (L (K := F)) V}
    (U T : Subgroup G) (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative V →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (γ : G →* L (K := F))
    (hact : ∀ (g : G) (v : V), j (Multiplicative.ofAdd (σ (γ g) v))=
      g*j (Multiplicative.ofAdd v)*g⁻¹)
    (hkT : γ.ker ≤ T) (hUT : U ≤ T)
    (hc : Nat.card (T.map γ)=Nat.card F)
    (hd : Module.finrank F (displacementSpace ((T.map γ).map (commutator (Sp F)).subtype))=1) :
    centralizer ((T ⊓ centralizer (T : Set G) : Subgroup G) : Set G)=T := by
  let ψ := (commutator (Sp F)).subtype.comp γ
  let A := T.map ψ
  have hker : ψ.ker=γ.ker := by
    ext x
    change (γ x).val=1 ↔ γ x=1
    exact ⟨fun hh => Subtype.ext hh,fun hh => congrArg Subtype.val hh⟩
  have hA : A=(T.map γ).map (commutator (Sp F)).subtype := (Subgroup.map_map ..).symm
  have hfix := root_fixedSpace_fixer_eq A (by rw [hA]; exact hd)
    (by rw [hA,card_map_of_injective (commutator (Sp F)).subtype_injective,hc])
  apply le_antisymm _ (le_centralizer_iff.mp inf_le_right)
  intro x hx
  have hxA : ψ x ∈ A := by
    rw [←hfix]
    apply (mem_fixingSubgroup_iff _).mpr
    intro v hv
    obtain ⟨w,rfl⟩ := hp.1 v
    have hjc : j (Multiplicative.ofAdd w) ∈ centralizer (T : Set G) := by
      intro t ht
      have hf : binaryNatural (γ t) (p w)=p w := hv (ψ t) (mem_map_of_mem ψ ht)
      have he := congrArg (fun u => j (Multiplicative.ofAdd u))
        (cover_fixed_of_projection_fixed p hp (γ t) w hf)
      rw [hact,mul_inv_eq_iff_eq_mul] at he
      exact he
    have hjT := hUT (hjr ▸ (show j (Multiplicative.ofAdd w) ∈ j.range from ⟨_,rfl⟩))
    have he : σ (γ x) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact,←hx _ ⟨hjT,hjc⟩,mul_inv_cancel_right]
    change binaryNatural (γ x) (p w)=p w
    rw [←p.isIntertwining,he]
  exact (show (T.map ψ).comap ψ=T from comap_map_eq_self (hker.trans_le hkT)) ▸ hxA

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

open ChapterB.QuasisimpleSource


/-- The full edge center has precisely the edge as its centralizer inside
an endpoint stabilizer. The proof lifts every root-fixed vector through the
complete natural cover before applying the literal hyperplane-fixer theorem. -/
theorem replacement_field_sized_center_centralizer
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let S := stabilizer d.radical a
    let T := (Q d.radical t).subgroupOf S
    centralizer ((T ⊓ centralizer (T : Set S) : Subgroup S) : Set S)=T := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have hγker : γ.ker=κ.ker := by
    ext x
    change e.groupEquiv (κC x)=1 ↔ κ x=1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have haq := (replacement_field_sized_edge_factorization h d rev hb hzt hat hsize).1
  have hzq := (replacement_field_sized_edge_factorization h d path hb hat hzt hsize).1
  have hZS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZS)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZS κ hκQ).trans (hzq.trans hFc.symm)
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ (fun x v => hconj (inclusion hZS x) v) hδcard (haq.trans hFc.symm)
  let S := stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hjoin := (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1
  have hTS : Q d.radical t ≤ S := by rw [←hjoin]; exact sup_le hQS hZS
  let U₀ := (U d.radical a).subgroupOf S
  let T₀ := (Q d.radical t).subgroupOf S
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjSr : jS.range=U₀ := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      change j w ∈ U d.radical a
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  have haction (x : S) (w : s.space.toSubmodule) :
      jS (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x*jS (Multiplicative.ofAdd w)*x⁻¹ := by
    apply Subtype.ext
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hγβ (x : Z d.radical z) : γ (inclusion hZS x)=β x := by
    exact (congrArg e.groupEquiv
      (show κC (inclusion hZS x)=e.groupEquiv.symm (β x) from
        Subtype.ext (hβmark x).symm)).trans (e.groupEquiv.apply_symm_apply _)
  have hQker : (Q d.radical a).subgroupOf S = γ.ker := by
    rw [hγker,←hκQ,subgroupOf_map_subtype_eq]
  have hZimage : ((Z d.radical z).subgroupOf S).map γ=β.range := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,hγβ ⟨x.val,hx⟩ |>.symm⟩
    · rintro _ ⟨x,rfl⟩
      exact ⟨inclusion hZS x,x.property,hγβ x⟩
  have hTimage : T₀.map γ=β.range := by
    change ((Q d.radical t).subgroupOf S).map γ=β.range
    rw [←hjoin,subgroupOf_sup hQS hZS,Subgroup.map_sup,hQker,
      show γ.ker.map γ=⊥ from (Subgroup.map_eq_bot_iff _).mpr le_rfl,bot_sup_eq,hZimage]
  let := finite_stabilizer d.radical a
  have hγT : γ.ker ≤ T₀ := by
    rw [←hQker]
    intro x hx
    exact (le_sup_left.trans_eq hjoin) hx
  apply embedded_root_center_centralizer U₀ T₀ (MovedSection.coverProjection s e) he jS
    (fun x y hh => hj (congrArg Subtype.val hh)) hjSr γ haction hγT
  · intro x hx
    exact (le_sup_left.trans_eq hjoin) ((U_le_Z a).trans
      (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; exact (by omega : 0<g.b d.radical)) |>.trans (omegaCenter_le _)) hx)
  · rw [hTimage]; exact hβcard
  · rw [hTimage]; exact hβdim

/-- The two normalizer cores together move the whole common displacement,
fix that displacement pointwise, and have an elementary abelian action on
the full edge center. The retained central attachment is included in the action. -/
theorem replacement_field_sized_joint_normalizer_action
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    let C := Q d.radical t ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical))
    let B := fun v : Vertex d.radical =>
      ((normalizer ((Q d.radical t).subgroupOf (stabilizer d.radical v) :
        Set (stabilizer d.radical v))).pCoreIn 2).map (stabilizer d.radical v).subtype
    let J := B a ⊔ B z
    let W := ⁅Z d.radical a,Z d.radical z⁆
    ⁅C,J⁆=W ∧ J ≤ centralizer (W : Set (FreeAmalgam d.radical)) ∧
      B a ⊓ B z ≤ centralizer (C : Set (FreeAmalgam d.radical)) ∧
      ∃ θ : J →* MulAut C,
        (∀ (b : J) (c : C), (θ b c : FreeAmalgam d.radical)= (b:FreeAmalgam d.radical)*(c:FreeAmalgam d.radical)*(b:FreeAmalgam d.radical)⁻¹) ∧
        IsElementaryAbelian 2 θ.range ∧
        Disjoint (((B a).subgroupOf J).map θ) (((B z).subgroupOf J).map θ) := by
  let C := Q d.radical t ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical))
  let B := fun v : Vertex d.radical =>
    ((normalizer ((Q d.radical t).subgroupOf (stabilizer d.radical v) :
      Set (stabilizer d.radical v))).pCoreIn 2).map (stabilizer d.radical v).subtype
  let W := ⁅Z d.radical a,Z d.radical z⁆
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hBa : B a ≤ centralizer (W : Set (FreeAmalgam d.radical)) :=
    replacement_field_sized_two_normalizer_centralizes h d path hb hat hzt hsize _
      (isPGroup_pCoreIn 2 _) (pCoreIn_le 2 _)
  have hBz : B z ≤ centralizer (W : Set (FreeAmalgam d.radical)) := by
    have hh := replacement_field_sized_two_normalizer_centralizes h d rev hb hzt hat hsize _
      (isPGroup_pCoreIn 2 _) (pCoreIn_le 2 _)
    rwa [commutator_comm (Z d.radical z) (Z d.radical a)] at hh
  have hn (v : Vertex d.radical) (hvt : Adjacent d.radical v t) :
      B v ≤ normalizer (C : Set (FreeAmalgam d.radical)) := by
    apply center_normalized (Q d.radical t)
    have hTS : Q d.radical t ≤ stabilizer d.radical v :=
      fun x hx => hx.2 v (adjacent_symm d.radical hvt)
    have hh := (map_mono (f := (stabilizer d.radical v).subtype)
      (pCoreIn_le 2 (normalizer ((Q d.radical t).subgroupOf (stabilizer d.radical v) :
        Set (stabilizer d.radical v))))).trans
      (((Q d.radical t).subgroupOf (stabilizer d.radical v)).le_normalizer_map
        (stabilizer d.radical v).subtype)
    rwa [map_subgroupOf_eq_of_le hTS] at hh
  obtain ⟨_,_,hdis,hjoin⟩ :=
    replacement_field_sized_unequal_shared_center_actions h d path hb hat hzt hsize hne
  obtain ⟨hm,hc⟩ := joint_displacement C (B a) (B z) W hBa hBz hjoin
  change ⁅C,B a ⊔ B z⁆=W ∧ _
  refine ⟨hm,hc,?_,?_⟩
  · apply le_centralizer_iff.mpr
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply (le_inf (commutator_mono le_rfl inf_le_left)
      (commutator_mono le_rfl inf_le_right)).trans
    exact disjoint_iff_inf_le.mp hdis
  · have hp := (replacement_field_sized_edge_displacement h d path hb hat hzt hsize).2
    rw [replacement_field_sized_whole_kernel_commutator h d path hb hat hzt hsize] at hp
    exact paired_action C (B a) (B z) W (sup_le (hn a hat) (hn z hzt)) hm.le hc hp hdis

/-- The ORIGINAL odd-index witness discharges the field-sized premise for
the joint action; its two normalizer cores retain their literal definitions. -/
theorem replacement_proper_nonsylow_joint_normalizer_action
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h))
    (hk : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    let C := Q d.radical t ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical))
    let B := fun v : Vertex d.radical =>
      ((normalizer ((Q d.radical t).subgroupOf (stabilizer d.radical v) :
        Set (stabilizer d.radical v))).pCoreIn 2).map (stabilizer d.radical v).subtype
    let J := B a ⊔ B z
    let W := ⁅Z d.radical a,Z d.radical z⁆
    ⁅C,J⁆=W ∧ J ≤ centralizer (W : Set (FreeAmalgam d.radical)) ∧
      B a ⊓ B z ≤ centralizer (C : Set (FreeAmalgam d.radical)) ∧
      ∃ θ : J →* MulAut C,
        (∀ (b : J) (c : C), (θ b c : FreeAmalgam d.radical)= (b:FreeAmalgam d.radical)*(c:FreeAmalgam d.radical)*(b:FreeAmalgam d.radical)⁻¹) ∧
        IsElementaryAbelian 2 θ.range ∧
        Disjoint (((B a).subgroupOf J).map θ) (((B z).subgroupOf J).map θ) :=
  replacement_field_sized_joint_normalizer_action h d path hb hat hzt
    (replacement_proper_nonsylow_card h d g hb hnsyl hne) hk

/-- Faithfulness on the full center, transported to the literal replacement
radical without identifying it with an original odd-index radical. -/
theorem replacement_field_sized_radical_center_centralizer
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    centralizer ((d.radical ⊓ centralizer (d.radical : Set d.overgroup) :
      Subgroup d.overgroup) : Set d.overgroup)=d.radical := by
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
  have hmT : d.radical.map f=Q d.radical t := by
    dsimp only [f]
    rw [←Subgroup.map_map,←Q_beta,←Q_act,hvt]
  let S := stabilizer d.radical (alpha d.radical)
  have hfr : f.range=S := by
    dsimp only [f,S]
    rw [MonoidHom.range_comp,show (embedM d.radical).range=stabilizer d.radical (alpha d.radical)
      from (stabilizer_m_base d.radical).symm,←stabilizer_act,hv]
  let fS := f.codRestrict S (fun x => hfr ▸ ⟨x,rfl⟩)
  have hfSi : Function.Injective fS := fun x y he => hf (congrArg Subtype.val he)
  have hfSs : Function.Surjective fS := by
    intro x
    obtain ⟨y,hy⟩ := (show x.val ∈ f.range from hfr.symm ▸ x.property)
    exact ⟨y,Subtype.ext hy⟩
  let e := MulEquiv.ofBijective fS ⟨hfSi,hfSs⟩
  have hTS : Q d.radical t ≤ S := hmT ▸ hfr ▸ map_le_range f d.radical
  have heT : d.radical.map e.toMonoidHom=(Q d.radical t).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_map,map_subgroupOf_eq_of_le hTS]
    exact hmT
  apply map_injective (show Function.Injective e.toMonoidHom from e.injective)
  rw [Theory.GroupTheory.map_centralizer_equiv]
  change centralizer ((d.radical ⊓ centralizer (d.radical : Set d.overgroup)).map e.toMonoidHom : Set S)=d.radical.map e.toMonoidHom
  rw [←map_inf_centralizer_of_injective e.toMonoidHom e.injective,heT]
  exact replacement_field_sized_center_centralizer h d path hb hat hzt hsize

/-- The actual original radical acts on the entire replacement center with
kernel precisely the replacement radical and image of order q squared. -/
theorem replacement_proper_nonsylow_center_action_order
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let C := d.radical ⊓ centralizer (d.radical : Set d.overgroup)
    let B := R.subgroupOf d.overgroup
    ∃ θ : B →* MulAut C,
      (∀ (b : B) (c : C), (θ b c : d.overgroup)=(b:d.overgroup)*(c:d.overgroup)*(b:d.overgroup)⁻¹) ∧
      θ.ker=d.radical.subgroupOf B ∧ Nat.card θ.range=2^(2*n) := by
  let C := d.radical ⊓ centralizer (d.radical : Set d.overgroup)
  let B := R.subgroupOf d.overgroup
  have hc : centralizer (C : Set d.overgroup)=d.radical :=
    replacement_field_sized_radical_center_centralizer h d g hb
      (replacement_proper_nonsylow_card h d g hb hnsyl hne)
  have hnT : B ≤ normalizer (d.radical : Set d.overgroup) := by
    dsimp only [B]
    rw [←replacement_normalizer_core_eq_original_restriction h d g hb hnsyl]
    exact pCoreIn_le 2 _
  have hnC := center_normalized d.radical B hnT
  let θ := C.normalizerMonoidHom.comp (inclusion hnC)
  have hk : θ.ker=d.radical.subgroupOf B := by
    change (C.normalizerMonoidHom.comp (inclusion hnC)).ker=_
    rw [←MonoidHom.comap_ker,Subgroup.normalizerMonoidHom_ker]
    ext b
    change (b:d.overgroup) ∈ centralizer (C : Set d.overgroup) ↔ (b:d.overgroup) ∈ d.radical
    rw [hc]
  refine ⟨θ,fun b c => rfl,hk,?_⟩
  rw [←index_ker,hk]
  exact replacement_proper_nonsylow_index h d g hb hnsyl hne

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
