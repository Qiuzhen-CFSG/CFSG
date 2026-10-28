module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoPointDisplacement
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.ArbitraryOrthogonalActors
public import Theory.Representation.BinaryConjugationSection.CommutatorFixedExtension

/-!
# Full fixed-core indices in the point-radical branch

In the large-movement branch, the full fixed-core displacement is disjoint
from the opposite covering kernel. Its escaping kernel supplies an invariant
quadratic refinement. Inside the actual point radical, quadratic actors
preserving that refinement have at most q elements: the radical coordinates
are determined by one field parameter. The cubic radical index forces both
|DQ′/Q′| = q and [T : T₀D] = q.

The critical centralizer modulo the entire opposite fixed core embeds into
the fixed space of a nonidentity actor on the natural four-space. This gives
[D ∩ Q′ : D ∩ D′] ≤ q³ and [D : D ∩ D′] ≤ q⁴. The first complete fixed
attachment has order q and is disjoint from D′, so T₁ = T₀D′ satisfies
[D : D ∩ T₁] ≤ q³ and [T : T₁] ≤ q⁴. The companion
`SourceTwoIndexContradiction` proves the reverse inequality and excludes
large movement.

Every application uses the original saturation premise, quotient marking,
critical pair and both complete fixed cores.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.7)(2), printed pp.873--874.
-/

public noncomputable section
open Subgroup Matrix Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
open scoped IsMulCommutative commutatorElement

private theorem point_quadratic_orthogonal_card
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup (Sp F)) (hAP : A ≤ pointRadicalAmbient)
    (hquad : ∀ x ∈ A, ∀ y ∈ A, ∀ w : Vector F, x • (y • w-w)=y • w-w)
    (c : Vector F) (hc : ∀ x : A, ∀ w, refinement c (x.val • w)=refinement c w) :
    Nat.card A ≤ Nat.card F := by
  let u (x : A) := x.val.val (.inl 1) (.inr 0)
  let v (x : A) := x.val.val (.inr 1) (.inr 0)
  let z (x : A) := x.val.val (.inl 0) (.inr 0)
  have he (x : A) : x.val=(pointRadicalElement (u x) (v x) (z x)).val := by
    obtain ⟨q,hq,heq⟩ := hAP x.property
    have hh := congrArg Subtype.val (pointRadical_eq_element q hq)
    change q.val=x.val at heq
    simpa only [heq] using hh
  have hinj (x y : A) (hu : u x=u y) (hv : v x=v y) (hz : z x=z y) : x=y := by
    apply Subtype.ext
    rw [he x,he y,hu,hv,hz]
  by_cases hall : ∀ x : A, u x=0 ∧ v x=0
  · apply Nat.card_le_card_of_injective z
    intro x y hz
    exact hinj x y ((hall x).1.trans (hall y).1.symm)
      ((hall x).2.trans (hall y).2.symm) hz
  obtain ⟨y,hy⟩ := not_forall.mp hall
  have hpair (x y : A) : v x * u y + u x * v y=0 := by
    have hh := congrFun (hquad x.val x.property y.val y.property (Pi.single (.inr 0) 1)) (.inl 0)
    rw [he x,he y] at hh
    simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,Pi.single_apply] at hh
    linear_combination hh
  have hcoeff : c (.inl 0)=0 := by
    have h1 := hc y (Pi.single (.inl 1) 1)
    have h2 := hc y (Pi.single (.inr 1) 1)
    rw [he y] at h1 h2
    simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec_single,
      refinement_apply,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,Pi.single_apply] at h1 h2
    by_cases hu : u y=0
    · have hv : v y≠0 := fun hv => hy ⟨hu,hv⟩
      exact h1.resolve_right hv
    · exact h2.resolve_right hu
  have hz (x : A) : z x + u x * v x + c (.inl 1) * u x^2 + c (.inr 1) * v x^2=0 := by
    have hh := hc x (Pi.single (.inr 0) 1)
    rw [he x] at hh
    simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec_single,
      refinement_apply,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,Pi.single_apply,hcoeff] at hh
    linear_combination hh
  have hzeq (x x' : A) (hu : u x=u x') (hv : v x=v x') : z x=z x' := by
    have h := hz x
    rw [hu,hv] at h
    linear_combination h - hz x'
  by_cases huy : u y=0
  · have hvy : v y≠0 := fun hv => hy ⟨huy,hv⟩
    apply Nat.card_le_card_of_injective v
    intro x x' hv
    have hu : u x=u x' := by
      apply mul_right_cancel₀ hvy
      have h1 := hpair x y
      have h2 := hpair x' y
      rw [huy,mul_zero,zero_add] at h1 h2
      exact h1.trans h2.symm
    exact hinj x x' hu hv (hzeq x x' hu hv)
  · apply Nat.card_le_card_of_injective u
    intro x x' hu
    have hv : v x=v x' := by
      apply mul_right_cancel₀ huy
      have h1 := hpair x y
      have h2 := hpair x' y
      rw [hu] at h1
      exact add_right_cancel (h1.trans h2.symm)
    exact hinj x x' hu hv (hzeq x x' hu hv)

private theorem conjugate_point_quadratic_orthogonal_card
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (P A : Subgroup (Sp F)) (hAP : A ≤ P)
    (hquad : ∀ x ∈ A, ∀ y ∈ A, ∀ w : Vector F, x • (y • w-w)=y • w-w)
    (c : Vector F) (hc : ∀ x : A, ∀ w, refinement c (x.val • w)=refinement c w)
    (g : Sp F) (hP : P.map (MulAut.conj g).toMonoidHom=pointRadicalAmbient) :
    Nat.card A ≤ Nat.card F := by
  let A' := A.map (MulAut.conj g).toMonoidHom
  have hcard : Nat.card A=Nat.card A' :=
    Nat.card_congr ((MulAut.conj g).subgroupMap A).toEquiv
  obtain ⟨d,hd⟩ := refinement_comp_symplectic c g⁻¹
  rw [hcard]
  apply point_quadratic_orthogonal_card A' (hP ▸ map_mono hAP) ?_ d ?_
  · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ w
    change (g*x*g⁻¹) • ((g*y*g⁻¹) • w-w)=(g*y*g⁻¹) • w-w
    have hh := congrArg (fun v => g • v) (hquad x hx y hy (g⁻¹ • w))
    simpa only [mul_smul,smul_sub,inv_smul_smul,smul_inv_smul] using hh
  · rintro ⟨_,⟨x,hx,rfl⟩⟩ w
    rw [←hd,←hd]
    change refinement c (g⁻¹ • ((g*x*g⁻¹) • w))=refinement c (g⁻¹ • w)
    simp only [mul_smul,inv_smul_smul]
    exact hc ⟨x,hx⟩ _

private theorem embedded_point_quadratic_actor_card
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hquad : ⁅⁅U,A⁆,A⁆=⊥)
    (hescape : ¬ p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j ≤ ⁅A,U⁆)
    (P : Subgroup (Sp F)) (hAP : (((commutator (Sp F)).subtype.comp β).range) ≤ P)
    (g : Sp F) (hP : P.map (MulAut.conj g).toMonoidHom=pointRadicalAmbient) :
    Nat.card (((commutator (Sp F)).subtype.comp β).range) ≤ Nat.card F := by
  let α := (commutator (Sp F)).subtype.comp β
  have hq : ∀ x ∈ α.range, ∀ y ∈ α.range, ∀ v : Vector F,
      x • (y • v-v)=y • v-v := by
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ v
    obtain ⟨w,rfl⟩ := hp.1 v
    have hval : j (Multiplicative.ofAdd (σ (β b) w-w)) =
        ⁅b.val,j (Multiplicative.ofAdd w)⁆ := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
    have hcomm : ⁅b.val,j (Multiplicative.ofAdd w)⁆ ∈ ⁅U,A⁆ := by
      rw [commutator_comm U]
      exact commutator_mem_commutator b.property (hjr ▸ ⟨_,rfl⟩)
    have hc := commutator_eq_bot_iff_le_centralizer.mp hquad hcomm a.val a.property
    have he : σ (β a) (σ (β b) w-w)=σ (β b) w-w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact,hval,hc,mul_inv_cancel_right]
    have hh := congrArg p he
    rw [p.isIntertwining,map_sub,p.isIntertwining] at hh
    exact hh
  obtain ⟨c,hc⟩ := embedded_cover_preserves_refinement_of_kernel_escape ⁅A,U⁆ A σ p hp j β
    hact (by rw [hjr]) hescape
  apply conjugate_point_quadratic_orthogonal_card P α.range hAP hq c ?_ g hP
  rintro ⟨_,⟨a,rfl⟩⟩ v
  exact hc a v

private theorem index_le_three_factors
    {G : Type*} [Group G] [Finite G] (A B N : Subgroup G) [A.Normal] [N.Normal] :
    N.index ≤ (A ⊔ B).index * (N.relIndex A * N.relIndex B) := by
  let q := QuotientGroup.mk' N
  let : (A.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (A.map q) (B.map q)
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hp : 0 < Nat.card (A.map q ⊓ B.map q : Subgroup (G ⧸ N)) := Nat.card_pos
  have hs : N.relIndex (A ⊔ B) ≤ N.relIndex A * N.relIndex B := by
    rw [←QuotientGroup.ker_mk' N,relIndex_ker,relIndex_ker,relIndex_ker,Subgroup.map_sup]
    dsimp only [q] at hc hp
    nlinarith
  have ht : N.index ≤ (N ⊓ (A ⊔ B)).index := by
    have hh := relIndex_le_of_le_left (L := ⊤) (show N ⊓ (A ⊔ B) ≤ N from inf_le_left)
      (show (N ⊓ (A ⊔ B)).relIndex ⊤ ≠ 0 from index_ne_zero_of_finite)
    simpa only [relIndex_top_right] using hh
  have hm := relIndex_mul_index (H := N ⊓ (A ⊔ B)) (K := A ⊔ B) inf_le_right
  rw [inf_relIndex_right] at hm
  calc
    N.index ≤ (N ⊓ (A ⊔ B)).index := ht
    _ = N.relIndex (A ⊔ B) * (A ⊔ B).index := hm.symm
    _ ≤ (N.relIndex A * N.relIndex B) * (A ⊔ B).index := Nat.mul_le_mul_right _ hs
    _ = _ := Nat.mul_comm _ _

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

theorem source_two_large_fixedCore_actor_index_le_field
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    (Q d.radical z).relIndex (fixedCore d.radical a) ≤ 2^n := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨pc⟩ := source_two_large_radical_point_cover h d g hb hsat path hat hzt c c' hlarge
  let E := pc.field
  let α := (commutator (Sp E.Carrier)).subtype.comp pc.actor
  have hDT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  let β := pc.actor.comp (inclusion hDT)
  let δ := (commutator (Sp E.Carrier)).subtype.comp β
  have hk : (MovedSection.coverProjection s pc.equiv).toLinearMap.ker.toAddSubgroup.toSubgroup.map
      pc.embedding = U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨pc.range_eq ▸ ⟨w,rfl⟩,(pc.kernel w.toAdd).mp hw⟩
    · intro x hx
      obtain ⟨w,rfl⟩ := (pc.range_eq.symm ▸ hx.1 : x ∈ pc.embedding.range)
      exact ⟨w,(pc.kernel w.toAdd).mpr hx.2,rfl⟩
  have hmove : ⁅fixedCore d.radical a,U d.radical z⁆ = ⁅Z d.radical z,fixedCore d.radical a⁆ := by
    rw [commutator_comm]
    exact (fixedCore_displacement_eq_moving h d g hb path hat hzt c c').symm
  have hquad : ⁅⁅U d.radical z,fixedCore d.radical a⁆,fixedCore d.radical a⁆=⊥ :=
    le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      (source_two_fixedCore_quadratic h d g hb hsat path hat hzt c c').le) bot_le
  have hescape : ¬ (MovedSection.coverProjection s pc.equiv).toLinearMap.ker.toAddSubgroup.toSubgroup.map
      pc.embedding ≤ ⁅fixedCore d.radical a,U d.radical z⁆ := by
    rw [hk,hmove]
    intro hle
    have hdis := (source_two_large_displacement_disjoint_opposite_fixedCore
      h d g hb hsat path hat hzt c c' hlarge).1
    have hUQ : U d.radical z ≤ Q d.radical z := (U_le_Z z).trans
      ((g.omega_bound z path.end_color (by
        rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans
        (omegaCenter_le _))
    have he : U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) = ⊥ := by
      apply bot_unique
      rw [←hdis.eq_bot]
      exact le_inf hle (inf_le_inf_right _ hUQ)
    have hh := (source_two_large_fixed_attachment_displacement_card
      h d g hb hsat path hat hzt c c' hlarge).2.1
    rw [he,card_bot] at hh
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    omega
  obtain ⟨v,hv⟩ := pc.point_image
  have hbound := embedded_point_quadratic_actor_card
    (MovedSection.coverAction s pc.equiv) (MovedSection.coverProjection s pc.equiv) pc.cover
    (U d.radical z) (fixedCore d.radical a) pc.embedding pc.injective pc.range_eq β
    (fun x => pc.actor_conjugation (inclusion hDT x)) hquad hescape α.range
    (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion hDT x,rfl⟩) v hv
  have hδker : δ.ker=(Q d.radical z).subgroupOf (fixedCore d.radical a) := by
    change (α.comp (inclusion hDT)).ker=_
    rw [←MonoidHom.comap_ker,pc.actor_kernel,comap_inclusion_subgroupOf]
  have hi : (Q d.radical z).relIndex (fixedCore d.radical a)=Nat.card δ.range := by
    rw [relIndex,←hδker,index_ker]
  rw [hi]
  simpa only [E,pc.field.card_eq,pc.degree] using hbound

/-- Both index bounds in the original full-radical product are attained. -/
theorem source_two_large_fixedCore_exact_indices
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    (Q d.radical z).relIndex (fixedCore d.radical a) = 2^n ∧
      (componentRadical d a t ⊔ fixedCore d.radical a).relIndex (Q d.radical t) = 2^n := by
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  let : ((componentRadical d a t).subgroupOf (Q d.radical t)).Normal :=
    normal_subgroupOf_of_le_normalizer c.componentRadical_normalized
  let : ((Q d.radical z).subgroupOf (Q d.radical t)).Normal := c'.core_normal
  have hAT : componentRadical d a t ≤ Q d.radical t := inf_le_left
  have hDT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  have hi := index_le_three_factors
    ((componentRadical d a t).subgroupOf (Q d.radical t))
    ((fixedCore d.radical a).subgroupOf (Q d.radical t))
    ((Q d.radical z).subgroupOf (Q d.radical t))
  rw [←subgroupOf_sup hAT hDT,relIndex_subgroupOf hAT,relIndex_subgroupOf hDT] at hi
  change (Q d.radical z).relIndex (Q d.radical t) ≤
    (componentRadical d a t ⊔ fixedCore d.radical a).relIndex (Q d.radical t) *
      ((Q d.radical z).relIndex (componentRadical d a t) *
        (Q d.radical z).relIndex (fixedCore d.radical a)) at hi
  rw [source_two_large_full_radical_card h d g hb hsat path hat hzt c c' hlarge,
    (source_two_large_movement_images h d g hb hsat path hat hzt c c' hlarge).1] at hi
  have hD := source_two_large_fixedCore_actor_index_le_field h d g hb hsat path hat hzt c c' hlarge
  have hT := (componentRadical_fixedCore_relIndex h d g hb path.start_color c).2
  have hq : 0 < 2^n := by positivity
  have hDge : 2^n ≤ (Q d.radical z).relIndex (fixedCore d.radical a) := by
    have hh := hi.trans (Nat.mul_le_mul_right _ hT)
    have hh' : (2^n)^2 * 2^n ≤ (2^n)^2 * (Q d.radical z).relIndex (fixedCore d.radical a) := by
      nlinarith only [hh]
    exact Nat.le_of_mul_le_mul_left hh' (by positivity)
  have hDeq := le_antisymm hD hDge
  rw [hDeq] at hi
  have hTge : 2^n ≤ (componentRadical d a t ⊔ fixedCore d.radical a).relIndex (Q d.radical t) := by
    have hh' : 2^n * (2^n)^2 ≤
        (componentRadical d a t ⊔ fixedCore d.radical a).relIndex (Q d.radical t) * (2^n)^2 := by
      nlinarith only [hi]
    exact Nat.le_of_mul_le_mul_right hh' (by positivity)
  exact ⟨hDeq,le_antisymm hT hTge⟩

/-- The critical centralizer has at most three natural field dimensions after
factoring by the entire opposite fixed core. -/
theorem critical_core_centralizer_fixedCore_index_le_cube
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2) :
    (fixedCore d.radical z).relIndex
      (Q d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))) ≤ (2^n)^3 := by
  classical
  obtain ⟨E,hE,s,γ,hγ,i,hi,hd,hrange,_⟩ := wholeKernel_natural_dualCover h d g hb path.end_color
  have hCtop : replacementComponent d=⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q=⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hγonto : Function.Surjective γ := MonoidHom.range_eq_top.mp (hγ.trans hCtop)
  let C := Q d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))
  let B := s.sectionData.imageSpace C
  have hUQ : U d.radical z ≤ Q d.radical z := (U_le_Z z).trans
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _))
  have himage : s.sectionData.imageSpace (U d.radical z) = i.toLinearMap.range := by
    ext w
    rw [hrange,s.sectionData.mem_imageSpace_iff]
  have hB : B ≤ i.toLinearMap.range := by
    have hh := s.sectionData.imageSpace_mono
      (critical_core_centralizer_le_moving_sup_fixed h d path hb)
    change B ≤ s.sectionData.imageSpace (U d.radical z ⊔
      (Q d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))) at hh
    rw [s.sectionData.imageSpace_sup_kernel _ hUQ,himage] at hh
    exact hh
  have hZaS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  obtain ⟨x,hx,hxQ⟩ := SetLike.not_le_iff_exists.mp path.critical.2
  let xS : stabilizer d.radical z := ⟨x,hZaS hx⟩
  obtain ⟨b,hb'⟩ := hγonto (s.quotient xS)
  have hbne : b.val ≠ 1 := by
    intro he
    have hb1 : b=1 := Subtype.ext he
    have hxker : xS ∈ s.quotient.ker := by
      change s.quotient xS=1
      rw [←hb',hb1,map_one]
    apply hxQ
    have hh := mem_map_of_mem (stabilizer d.radical z).subtype hxker
    rw [s.quotient_kernel] at hh
    exact hh
  let P : Submodule E.Carrier (Vector E.Carrier) :=
    ((symplecticNatural 2 b.val)-LinearMap.id).ker
  have hPne : P ≠ ⊤ := by
    intro he
    apply hbne
    apply Subtype.ext
    ext k l
    have hf : (Pi.single l 1 : Vector E.Carrier) ∈ P := he ▸ Submodule.mem_top
    change (symplecticNatural 2 b.val (Pi.single l 1))-Pi.single l 1=0 at hf
    rw [symplecticNatural_apply] at hf
    have heq := congrFun (sub_eq_zero.mp hf) k
    simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Matrix.mulVec_single,
      Pi.single_apply,Matrix.one_apply] using heq
  have hdim : Module.finrank E.Carrier P ≤ 3 := by
    have hh := Submodule.finrank_lt hPne
    have hV : Module.finrank E.Carrier (Vector E.Carrier)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hV] at hh
    omega
  have hfix (v : B) : s.action (γ b) v.val=v.val := by
    rw [hb']
    exact s.sectionData.fixed_on_imageSpace_of_commutator_le (Z d.radical a) C
      ((commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mpr (show C ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) from inf_le_right))).le.trans bot_le)
      xS hx v.val v.property
  have hex (v : B) : ∃ w : Vector E.Carrier, i w=v.val := hB v.property
  choose f hf using hex
  let fP : B → P := fun v => ⟨f v,by
    change b.val • f v-f v=0
    apply sub_eq_zero.mpr
    apply hi
    change i (binaryNatural b (f v))=i (f v)
    rw [i.isIntertwining,hf]
    exact hfix v⟩
  have hfi : Function.Injective fP := by
    intro v w he
    apply Subtype.ext
    rw [←hf v,←hf w]
    exact congrArg i (congrArg Subtype.val he)
  have hcard : Nat.card B ≤ Nat.card E.Carrier^3 :=
    (Nat.card_le_card_of_injective fP hfi).trans (by
      rw [Module.natCard_eq_pow_finrank (K := E.Carrier)]
      exact Nat.pow_le_pow_right Nat.card_pos hdim)
  rw [s.sectionData.imageSpace_card_eq_relIndex C inf_le_left,E.card_eq,hE] at hcard
  exact hcard

/-- The first full fixed-core comparison on printed p.874. -/
theorem source_two_large_fixedCore_overlap_index_le
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    (fixedCore d.radical z).relIndex (fixedCore d.radical a ⊓ Q d.radical z) ≤ (2^n)^3 ∧
      (fixedCore d.radical z).relIndex (fixedCore d.radical a) ≤ (2^n)^4 := by
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  let : Finite (fixedCore d.radical a) := Finite.of_injective
    (inclusion (inf_le_left.trans c.core_le_edge)) (inclusion_injective _)
  let C := Q d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))
  let : Finite C := Finite.of_injective
    (inclusion (inf_le_left.trans c'.core_le_edge)) (inclusion_injective _)
  have hsub : fixedCore d.radical a ⊓ Q d.radical z ≤ C := by
    refine le_inf inf_le_right ?_
    apply (inf_le_left.trans (show fixedCore d.radical a ≤ Q d.radical a from inf_le_left)).trans
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a path.start_color))
  have hcube := (relIndex_le_of_le_right hsub index_ne_zero_of_finite).trans
    (critical_core_centralizer_fixedCore_index_le_cube h d path hb)
  refine ⟨hcube,?_⟩
  have hh := relIndex_inf_mul_relIndex (fixedCore d.radical z) (Q d.radical z) (fixedCore d.radical a)
  rw [inf_eq_left.mpr (show fixedCore d.radical z ≤ Q d.radical z from inf_le_left),
    inf_comm (Q d.radical z) (fixedCore d.radical a),
    (source_two_large_fixedCore_exact_indices h d g hb hsat path hat hzt c c' hlarge).1] at hh
  rw [←hh]
  calc
    _ ≤ (2^n)^3 * 2^n := Nat.mul_le_mul_right _ hcube
    _ = (2^n)^4 := (pow_succ _ 3).symm

/-- The source subgroup T₁ = T₀D′ has index at most q⁴; its intersection
with D has index at most q³. Both complete fixed cores remain in the formula. -/
theorem source_two_large_component_fixedCore_index_upper
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    let T₁ := componentRadical d a t ⊔ fixedCore d.radical z
    T₁.relIndex (fixedCore d.radical a) ≤ (2^n)^3 ∧
      T₁.relIndex (Q d.radical t) ≤ (2^n)^4 := by
  let T₁ := componentRadical d a t ⊔ fixedCore d.radical z
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  change T₁.relIndex (fixedCore d.radical a) ≤ (2^n)^3 ∧ T₁.relIndex (Q d.radical t) ≤ (2^n)^4
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  have hBT : componentRadical d a t ≤ Q d.radical t := inf_le_left
  have hDT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  have hD'T : fixedCore d.radical z ≤ Q d.radical t := inf_le_left.trans c'.core_le_edge
  have hT₁T : T₁ ≤ Q d.radical t := sup_le hBT hD'T
  let : Finite (fixedCore d.radical a) := Finite.of_injective
    (inclusion hDT) (inclusion_injective _)
  let : Finite (T₁ ⊓ fixedCore d.radical a : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion (show T₁ ⊓ fixedCore d.radical a ≤ fixedCore d.radical a from inf_le_right))
    (inclusion_injective _)
  have hUAQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _))
  have hAD : A ≤ fixedCore d.radical a := inf_le_inf_right _ hUAQ
  have hAB : A ≤ componentRadical d a t :=
    inf_le_left.trans ((c.componentRadical_inf_core g hb path.start_color).symm.le.trans inf_le_left)
  have hAinside : A ≤ T₁ ⊓ fixedCore d.radical a := le_inf (hAB.trans le_sup_left) hAD
  have hdis := (source_two_large_displacement_disjoint_opposite_fixedCore
    h d g hb hsat path hat hzt c c' hlarge).2
  have hAcard := (source_two_large_fixed_attachment_displacement_card
    h d g hb hsat path hat hzt c c' hlarge).1
  have hAi : (fixedCore d.radical z).relIndex A=2^n := by
    rw [←inf_relIndex_right,inf_comm]
    change (A ⊓ fixedCore d.radical z).relIndex A=2^n
    rw [hdis.eq_bot,relIndex_bot_left]
    exact hAcard
  have hlow := relIndex_le_of_le_right (H := fixedCore d.radical z)
    hAinside (show (fixedCore d.radical z).relIndex (T₁ ⊓ fixedCore d.radical a) ≠ 0 from
      index_ne_zero_of_finite)
  rw [hAi] at hlow
  have hmul := relIndex_inf_mul_relIndex (fixedCore d.radical z) T₁ (fixedCore d.radical a)
  rw [inf_eq_left.mpr (show fixedCore d.radical z ≤ T₁ from le_sup_right)] at hmul
  have hupper := (source_two_large_fixedCore_overlap_index_le
    h d g hb hsat path hat hzt c c' hlarge).2
  have hD : T₁.relIndex (fixedCore d.radical a) ≤ (2^n)^3 := by
    have hh := (Nat.mul_le_mul_right (T₁.relIndex (fixedCore d.radical a)) hlow).trans
      (hmul.trans_le hupper)
    have hh' : 2^n * T₁.relIndex (fixedCore d.radical a) ≤ 2^n * (2^n)^3 := by
      nlinarith only [hh]
    exact Nat.le_of_mul_le_mul_left hh' (by positivity)
  refine ⟨hD,?_⟩
  let : ((componentRadical d a t).subgroupOf (Q d.radical t)).Normal :=
    normal_subgroupOf_of_le_normalizer c.componentRadical_normalized
  have hnorm : Q d.radical t ≤ normalizer (T₁ : Set (FreeAmalgam d.radical)) :=
    (le_inf c.componentRadical_normalized c'.fixedCore_normalized).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : (T₁.subgroupOf (Q d.radical t)).Normal := normal_subgroupOf_of_le_normalizer hnorm
  have hi := index_le_three_factors
    ((componentRadical d a t).subgroupOf (Q d.radical t))
    ((fixedCore d.radical a).subgroupOf (Q d.radical t))
    (T₁.subgroupOf (Q d.radical t))
  rw [←subgroupOf_sup hBT hDT,relIndex_subgroupOf hBT,relIndex_subgroupOf hDT] at hi
  change T₁.relIndex (Q d.radical t) ≤
    (componentRadical d a t ⊔ fixedCore d.radical a).relIndex (Q d.radical t) *
      (T₁.relIndex (componentRadical d a t) * T₁.relIndex (fixedCore d.radical a)) at hi
  rw [relIndex_eq_one.mpr (show componentRadical d a t ≤ T₁ from le_sup_left),one_mul] at hi
  have hr := (componentRadical_fixedCore_relIndex h d g hb path.start_color c).2
  calc
    _ ≤ (componentRadical d a t ⊔ fixedCore d.radical a).relIndex (Q d.radical t) *
        T₁.relIndex (fixedCore d.radical a) := hi
    _ ≤ 2^n * (2^n)^3 := Nat.mul_le_mul hr hD
    _ = (2^n)^4 := by ring

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
