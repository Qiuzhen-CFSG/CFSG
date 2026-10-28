module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NeighborEdgeFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NaturalLower
public import Theory.SpecificGroups.SymplecticFour.PointPairGeneration

/-!
# Simultaneous centralizer generation in the strict-index countercase

A natural vector stabilizer and any two-group moving that vector generate
Sp₄. Conjugate the vector to the standard point: a proper overgroup of its
point local still fixes that point, and a two-group fixing the point fixes
the vector. Fixed-vector lifting gives the same generation statement on
the full central cover, with the whole quotient kernel retained.

Source (5.3) puts the complete edge seed in U times the subgroup fixed by
the whole vertex. The preceding argument therefore applies to every moved
edge element, including all central attachments. At the actual two-step
vertex in (5.9), the already selected escaping element now satisfies both
clauses of (*), on the same conjugator and with the same centralizer T₀.
The original full terminal subgroup and penultimate-radius escape are kept.

Every nonkernel actor has full-Z fixed index greater than two at the
original nonbinary degree. This excludes the exceptional hatted-endpoint
case in (5.0); the full endpoint in (*) is the source endpoint.

The subsequent orbit-span argument proving H <= D, the central-H branch,
the strict index and terminal distance exclusions remain to be proved.
No distance-two witness or characteristic preservation is asserted here.

Source: Meierfrankenfeld--Stellmacher, "Pushing up weak BN-pairs of rank two"
(1993), (5.0), (5.3) and (5.9)(*), printed pp.912, 915 and 920.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover

private theorem two_group_point_local
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hcard : Nat.card F=2^n) (hn : 1<n)
    (A : Subgroup (Sp F)) (hAP : A ≤ pointParabolic) (hA : IsPGroup 2 A) :
    A ≤ pointLocal := by
  let S : Sylow 2 (pointParabolic (F := F)) := (unipotentSylow hcard (by omega)).subtype
    (unipotent_le_borel.trans inf_le_left)
  have hSN : (S : Subgroup (pointParabolic (F := F))) ≤ pointLocal.subgroupOf pointParabolic :=
    comap_mono (show unipotent ≤ pointLocal (F := F) from inf_le_left)
  have hle := hA.comap_subtype.le_normalClosure_sylow S
  have hle' : A.subgroupOf pointParabolic ≤ pointLocal.subgroupOf pointParabolic :=
    hle.trans (normalClosure_le_normal hSN)
  intro x hx
  exact hle' (show (⟨x,hAP hx⟩ : pointParabolic) ∈ A.subgroupOf pointParabolic from hx)

private theorem vector_stabilizer_generate
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hcard : Nat.card F=2^n) (hn : 1<n)
    (v : Vector F) (A : Subgroup (Sp F)) (hA : IsPGroup 2 A)
    (hmove : ¬ ∀ a ∈ A, a • v = v) :
    MulAction.stabilizer (Sp F) v ⊔ A = ⊤ := by
  have hv : v ≠ 0 := by
    rintro rfl
    exact hmove (fun _ _ => smul_zero _)
  have he : e (F := F) 0 ≠ 0 := by
    intro hh
    have hx := congrFun hh (.inl 0)
    simp [Theory.SpecificGroups.SymplecticFour.e] at hx
  obtain ⟨k,hk⟩ := TwoLocalCover.nonzero_vector_transitive hv he
  let N := (MulAction.stabilizer (Sp F) v ⊔ A).map (MulAut.conj k).toMonoidHom
  have hLN : pointLocal ≤ N := by
    intro l hl
    have hfix := (mem_pointLocal_iff_fixed l).mp hl
    have hm : k⁻¹*l*k ∈ MulAction.stabilizer (Sp F) v := by
      change (k⁻¹*l*k) • v=v
      rw [mul_smul,mul_smul,hk,hfix,←hk,inv_smul_smul]
    exact ⟨k⁻¹*l*k,mem_sup_left hm,by change k*(k⁻¹*l*k)*k⁻¹=l; group⟩
  have hN : N=⊤ := by
    by_contra hN
    have hP := PointPairGeneration.overgroup_pointLocal N hLN hN
    have hAP : A.map (MulAut.conj k).toMonoidHom ≤ pointParabolic :=
      (map_mono (show A ≤ MulAction.stabilizer (Sp F) v ⊔ A from le_sup_right)).trans hP
    have hAL := two_group_point_local hcard hn _ hAP (hA.map (MulAut.conj k).toMonoidHom)
    apply hmove
    intro a ha
    have hf := (mem_pointLocal_iff_fixed _).mp (hAL (mem_map_of_mem _ ha))
    change (k*a*k⁻¹) • e 0=e 0 at hf
    rw [←hk,mul_smul,mul_smul,inv_smul_smul] at hf
    exact (MulAction.injective k) hf
  apply (Subgroup.map_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective)
  rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective (MulAut.conj k).toMonoidHom (MulAut.conj k).surjective]
  exact hN

private theorem covered_element_centralizer_generate
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (β : G →* L (K := F)) (hβ : Function.Surjective β)
    (hact : ∀ (g : G) (w : W), j (Multiplicative.ofAdd (σ (β g) w)) =
      g*j (Multiplicative.ofAdd w)*g⁻¹)
    (A : Subgroup G) (hA : IsPGroup 2 A) (w : W)
    (hmove : j (Multiplicative.ofAdd w) ∉ centralizer (A : Set G)) :
    centralizer ({j (Multiplicative.ofAdd w)} : Set G) ⊔ A=⊤ := by
  let f := (commutator (Sp F)).subtype.comp β
  have hlarge : 2 < Nat.card F := by
    rw [hcard]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) hn)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g,hg⟩ := hβ ⟨x,by rw [SymplecticFour.LargeField.commutator_eq_top hlarge]; trivial⟩
    exact ⟨g,congrArg Subtype.val hg⟩
  have hfix (g : G) : g ∈ centralizer ({j (Multiplicative.ofAdd w)} : Set G) ↔
      f g • p w=p w := by
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have hw : σ (β g) w=w := by
        apply Multiplicative.ofAdd.injective
        apply hj
        rw [hact,hg,mul_inv_cancel_right]
      exact (LinearMap.congr_fun (p.isIntertwining' (β g)) w).symm.trans (congrArg p hw)
    · intro hg
      have hw := cover_fixed_of_projection_fixed p hp (β g) w hg
      have hh := congrArg (fun v => j (Multiplicative.ofAdd v)) hw
      rw [hact,mul_inv_eq_iff_eq_mul] at hh
      exact hh
  have hmap : (centralizer ({j (Multiplicative.ofAdd w)} : Set G)).map f =
      MulAction.stabilizer (Sp F) (p w) := by
    ext x
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact (hfix g).mp hg
    · intro hx
      obtain ⟨g,rfl⟩ := hf x
      exact ⟨g,(hfix g).mpr hx,rfl⟩
  have hker : f.ker ≤ centralizer ({j (Multiplicative.ofAdd w)} : Set G) := by
    intro g hg
    apply (hfix g).mpr
    rw [show f g=1 from hg,one_smul]
  have hm : ¬ ∀ a ∈ A.map f, a • p w=p w := by
    intro hm
    apply hmove
    intro a ha
    exact (mem_centralizer_singleton_iff.mp ((hfix a).mpr
      (hm (f a) (mem_map_of_mem f ha))))
  have hgen := vector_stabilizer_generate hcard hn (p w) (A.map f) (hA.map f) hm
  rw [←hmap,←Subgroup.map_sup] at hgen
  have heq := congrArg (Subgroup.comap f) hgen
  simpa only [comap_map_eq,comap_top,sup_eq_left.mpr (hker.trans le_sup_left)] using heq

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A two-group moving an element of the full U-cover generates the vertex
with that element's whole centralizer. The complete quotient kernel is retained. -/
theorem Input.replacement_U_element_centralizer_generation
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ stabilizer d.radical a)
    (hA : IsPGroup 2 A) (u : FreeAmalgam d.radical) (hu : u ∈ U d.radical a)
    (hm : u ∉ centralizer (A : Set (FreeAmalgam d.radical))) :
    (stabilizer d.radical a ⊓ centralizer ({u} : Set (FreeAmalgam d.radical))) ⊔ A =
      stabilizer d.radical a := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d ha
  have hCtop : C=⊤ := by
    have hpre : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,
        comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hpre]
    rw [←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have hκC : Function.Surjective κC := by
    intro x
    obtain ⟨g,hg⟩ := hκ x
    exact ⟨g,Subtype.ext hg⟩
  have hγ : Function.Surjective γ := e.groupEquiv.surjective.comp hκC
  let S := stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjS : Function.Injective jS := fun v w hvw => hj (congrArg Subtype.val hvw)
  let σ := MovedSection.coverAction s e
  have haction (x : S) (w : s.space.toSubmodule) :
      jS (Multiplicative.ofAdd (σ (γ x) w)) = x*jS (Multiplicative.ofAdd w)*x⁻¹ := by
    apply Subtype.ext
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  obtain ⟨w,hw⟩ := (show u ∈ j.range from hjr.symm ▸ hu)
  have hmS : jS (Multiplicative.ofAdd w.toAdd) ∉ centralizer (A.subgroupOf S : Set S) := by
    intro hh
    apply hm
    intro x hx
    have hh' := congrArg Subtype.val (hh (⟨x,hAS hx⟩ : S) hx)
    change x*j w=j w*x at hh'
    rwa [hw] at hh'
  have hgen := covered_element_centralizer_generate (E.card_eq.trans (congrArg (2^·) hE))
    h.nonbinary (MovedSection.coverProjection s e) he jS hjS γ hγ haction
    (A.subgroupOf S) hA.comap_subtype w.toAdd hmS
  have hCeq : (centralizer ({jS (Multiplicative.ofAdd w.toAdd)} : Set S)).map S.subtype =
      S ⊓ centralizer ({u} : Set (FreeAmalgam d.radical)) := by
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x.property,?_⟩
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)
      change x.val*j w=j w*x.val at hh
      rwa [hw] at hh
    · rintro ⟨hx,hc⟩
      refine ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr ?_,rfl⟩
      apply Subtype.ext
      change x*j w=j w*x
      rw [hw]
      exact mem_centralizer_singleton_iff.mp hc
  have hh := congrArg (Subgroup.map S.subtype) hgen
  rw [Subgroup.map_sup,hCeq,map_subgroupOf_eq_of_le hAS,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh

/-- The complete source edge seed lies in U times the subgroup fixed by the
whole vertex. This statement keeps every central attachment. -/
theorem Input.replacement_edge_seed_le_U_sup_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false) (hat : Adjacent d.radical a t) :
    Z d.radical t ≤ U d.radical a ⊔
      (Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have ht : color d.radical t ≠ false := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    exact Ne.symm hh
  have htZ := adjacent_Z_le d.radical ha hat
  have htJ : Z d.radical t ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    intro v hv y hy
    rw [Z,if_neg ht] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2 y ((Subgroup.SmallMover.join_le _ _ _ _) hy)
  have hZX : Z d.radical a ≤ X d.radical a := Z_le_X_of_positive d.radical a ha
    (geometry.exists_critical a ha) (by rw [geometry.distance_constant a ha]; change 0 < geometry.b d.radical; omega)
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha
  have hS : Ltilde d.radical a ⊔ Q d.radical a=S := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have hN : fixedCore d.radical a ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (show fixedCore d.radical a ≤ S from fun _ hx => hx.1.1).trans (U_normalized a)
  intro z hz
  have hzUD := h.replacement_small_mover_X_centralizer d geometry hb ha hat ⟨hZX (htZ hz),htJ hz⟩
  have hzprod : z ∈ (U d.radical a : Set (FreeAmalgam d.radical)) *
      (fixedCore d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hN]
    exact hzUD
  obtain ⟨u,hu,c,hc,he⟩ := hzprod
  have hcZ : c ∈ Z d.radical a := by
    have hh := (Z d.radical a).mul_mem ((Z d.radical a).inv_mem (U_le_Z a hu)) (htZ hz)
    simpa only [←he,inv_mul_cancel_left] using hh
  have hcS : c ∈ centralizer (S : Set (FreeAmalgam d.radical)) := by
    have hSL : Ltilde d.radical a ≤ centralizer ({c} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hc.2 y hy)
    have hSQ : Q d.radical a ≤ centralizer ({c} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr
        ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha)) hcZ y hy)
    intro y hy
    exact mem_centralizer_singleton_iff.mp ((sup_le hSL hSQ) (hS.symm ▸ hy))
  rw [←he]
  exact mul_mem (mem_sup_left hu) (mem_sup_right ⟨hcZ,hcS⟩)

/-- A moved element of the whole edge seed has centralizer generating the
vertex with its moving two-group, without choosing a central complement. -/
theorem Input.replacement_edge_element_centralizer_generation
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false) (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ stabilizer d.radical a)
    (hA : IsPGroup 2 A) (z : FreeAmalgam d.radical) (hz : z ∈ Z d.radical t)
    (hm : z ∉ centralizer (A : Set (FreeAmalgam d.radical))) :
    (stabilizer d.radical a ⊓ centralizer ({z} : Set (FreeAmalgam d.radical))) ⊔ A =
      stabilizer d.radical a := by
  let S := stabilizer d.radical a
  let D := Z d.radical a ⊓ centralizer (S : Set (FreeAmalgam d.radical))
  have hD : D ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  have hzprod : z ∈ (U d.radical a : Set (FreeAmalgam d.radical)) * (D : Set _) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hD]
    exact h.replacement_edge_seed_le_U_sup_fixed d geometry hb ha hat hz
  obtain ⟨u,hu,c,hc,rfl⟩ := hzprod
  have hmU : u ∉ centralizer (A : Set (FreeAmalgam d.radical)) := by
    intro huA
    exact hm ((centralizer (A : Set (FreeAmalgam d.radical))).mul_mem huA (centralizer_le hAS hc.2))
  have hgen := h.replacement_U_element_centralizer_generation d geometry hb ha A hAS hA u hu hmU
  have hC : S ⊓ centralizer ({u} : Set (FreeAmalgam d.radical)) ≤
      S ⊓ centralizer ({u*c} : Set (FreeAmalgam d.radical)) := by
    rintro x ⟨hx,hxu⟩
    refine ⟨hx,mem_centralizer_singleton_iff.mpr ?_⟩
    have h₁ := mem_centralizer_singleton_iff.mp hxu
    have h₂ := hc.2 x hx
    calc
      x*(u*c) = u*(x*c) := by rw [←mul_assoc,h₁,mul_assoc]
      _ = u*c*x := by rw [h₂,←mul_assoc]
  apply le_antisymm (sup_le inf_le_left hAS)
  calc
    S = (S ⊓ centralizer ({u} : Set (FreeAmalgam d.radical))) ⊔ A := hgen.symm
    _ ≤ _ := sup_le_sup_right hC A

/-- The nonbinary natural quotient excludes the index-two transvection
exception in source (5.0), on the whole Z-layer rather than just U. -/
theorem Input.replacement_full_seed_fixed_index_gt_two
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ stabilizer d.radical a)
    (hne : ¬ A ≤ Q d.radical a) :
    2 < (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) := by
  let := finite_Z d.radical a
  have hq : 2 < Nat.card F := by
    rw [h.field_card]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  exact hq.trans_le ((h.replacement_natural_fixed_index_lower d geometry hb ha A hAS hne).trans
    (relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite))

/-- In the actual critical endpoint every nonkernel element has full-Z
fixed index greater than two. Thus the exceptional index-two branch in
source (5.0)'s definition of the hatted endpoint cannot occur. -/
theorem Input.replacement_critical_endpoint_no_index_two
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (y : FreeAmalgam d.radical) (hy : y ∈ Z d.radical z) (hyQ : y ∉ Q d.radical a) :
    2 < (centralizer (Subgroup.zpowers y : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a) := by
  exact h.replacement_full_seed_fixed_index_gt_two d geometry hb path.start_color
    (Subgroup.zpowers y) (zpowers_le.mpr ((path.endpoint_Z_le_start_stabilizer (by omega)) hy))
    (fun hle => hyQ (hle (mem_zpowers y)))

/-- Source (5.9)(*) on the same escaping conjugate: its full centralizer
and the original endpoint generate the vertex, while that element still
moves the endpoint and escapes the complete penultimate radius. -/
theorem Input.replacement_field_index_kernel_generation_escape
    {geometry : Geometry d.radical} {a z c t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F)
    (hD : ¬ kernelCommutator geometry a c ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ g ∈ stabilizer d.radical a, ∃ x ∈ kernelCommutator geometry a c,
      let c₁ := act d.radical g⁻¹ c
      let t₁ := act d.radical g⁻¹ t
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      (kernelCommutator geometry a c).map (MulAut.conj g).toMonoidHom =
        ⁅U d.radical c₁,kernelCentralizer geometry a c⁆ ∧
      ⁅U d.radical c₁,kernelCentralizer geometry a c⁆ ≤ Z d.radical t₁ ∧
      g*x*g⁻¹ ∈ ⁅U d.radical c₁,kernelCentralizer geometry a c⁆ ∧
      g*x*g⁻¹ ∉ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
      g*x*g⁻¹ ∉ V d.radical (path.walk.getVert (path.walk.length-2)) ∧
      (stabilizer d.radical a ⊓ centralizer ({g*x*g⁻¹} : Set (FreeAmalgam d.radical))) ⊔
        Z d.radical z = stabilizer d.radical a := by
  obtain ⟨g,hg,x,hx,hat₁,hct₁,he,hH₁,hxH,hm,hescape⟩ :=
    h.replacement_field_index_kernel_escape d path hb hat hct hsmall hD
  refine ⟨g,hg,x,hx,hat₁,hct₁,he,hH₁,hxH,hm,hescape,?_⟩
  let : IsElementaryAbelian 2 (Z d.radical z) := geometry.Z_elementary (by omega) z path.end_color
  exact h.replacement_edge_element_centralizer_generation d geometry hb.le path.start_color hat₁
    (Z d.radical z) (path.endpoint_Z_le_start_stabilizer (by omega))
    (IsElementaryAbelian.isPGroup 2 (Z d.radical z)) (g*x*g⁻¹) (hH₁ hxH) hm

/-- The literal two-step countercase of (5.9) supplies simultaneous
centralizer generation and escape, with the same T₀ and its complete
terminal subgroup. The noncentrality premise is the source case split. -/
theorem Input.replacement_strict_index_noncentral_selection
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hD : ¬ kernelCommutator geometry a (path.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    let c := path.walk.getVert 2
    let t := path.walk.getVert 1
    let T₀ := kernelCentralizer geometry a c
    stabilizer d.radical a ≤ normalizer (T₀ : Set _) ∧
      V d.radical a ≤ T₀ ∧
      Z d.radical (path.walk.getVert (path.walk.length-2)) ⊔
        (Z d.radical z ⊓ Q d.radical a) ≤ T₀ ∧
      ∃ g ∈ stabilizer d.radical a, ∃ x ∈ kernelCommutator geometry a c,
        let c₁ := act d.radical g⁻¹ c
        let t₁ := act d.radical g⁻¹ t
        Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
        kernelCentralizer geometry a c₁ = T₀ ∧
        (kernelCommutator geometry a c).map (MulAut.conj g).toMonoidHom = ⁅U d.radical c₁,T₀⁆ ∧
        ⁅U d.radical c₁,T₀⁆ ≤ Z d.radical t₁ ∧
        g*x*g⁻¹ ∈ ⁅U d.radical c₁,T₀⁆ ∧
        (stabilizer d.radical a ⊓ centralizer ({g*x*g⁻¹} : Set (FreeAmalgam d.radical))) ⊔
          Z d.radical z = stabilizer d.radical a ∧
        g*x*g⁻¹ ∉ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        g*x*g⁻¹ ∉ V d.radical (path.walk.getVert (path.walk.length-2)) := by
  dsimp only
  have hlen : 2 ≤ path.walk.length := by rw [path.length_eq_b]; omega
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm _ ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  obtain ⟨hn,hV,htail,_,_⟩ := h.replacement_strict_index_kernel_at_two_step d path hb hsmall
  obtain ⟨g,hg,x,hx,hat₁,hct₁,he,hH₁,hxH,hm,hescape,hgen⟩ :=
    h.replacement_field_index_kernel_generation_escape d path hb hat hct hsmall hD
  have hT := (h.replacement_kernel_conjugate_at_edge d geometry (by omega)
    path.start_color hat hct g⁻¹ ((stabilizer d.radical a).inv_mem hg)).1
  exact ⟨hn,hV,htail,g,hg,x,hx,hat₁,hct₁,hT,he,hH₁,hxH,hgen,hm,hescape⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
