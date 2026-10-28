module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourEscapeComparison

/-!
# Full-size hyperplane intersections in source (4)

When the complete attachment has field order, the universal orthogonal-cover
quotient is injective: its restriction to the central field line maps onto a
kernel of the same order. Composing with the original embedding realizes the
whole moving group as the five-dimensional field module, with its existing
actor and projection. No change of plane marking or kernel quotient is made.

Fixed spaces and their movements are field subspaces under that embedding.
Consequently the intersection of [X,Z_a] and H = [Z_z,C_T(X)] has field-power
order in the escaping case. For unequal attachments both movements have order
q squared. Their join lies in the full common-radical fixed layer, of order
q cubed; they are distinct by the preceding escape comparison. Their
intersection therefore has exactly order q.

The last theorem constructs the actual source hyperplane and retains its
section centralizer, field-sized complement and both complete attachments.
The Chapter11 application uses the literal intrinsic MS input. Identification
of this intersection with the attachments, the nonescaping branch, source
(5)/(6), and the terminal field restriction remain to be proved.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(4), printed p.875. The private full-cover construction uses the
project's universal orthogonal-cover quotient; the central-supplement and
finite subgroup-product calculations follow the existing checked interfaces.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement IsMulCommutative

private theorem full_cover_quotient
    {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hc : Nat.card p.toLinearMap.ker=Nat.card F) :
    ∃ f : binaryAction.IntertwiningMap σ, Function.Bijective f ∧
      ∀ v, p (f v)=binaryProjection v := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  let k : F → p.toLinearMap.ker := fun t => ⟨f (0,t),hpf (0,t)⟩
  have hs : Function.Surjective k := by
    intro w
    obtain ⟨v,hv⟩ := hf w.val
    have hv1 : v.1=0 := (hpf v).symm.trans (by rw [hv]; exact w.property)
    exact ⟨v.2,Subtype.ext (by change f (0,v.2)=w.val; rw [←hv1,hv])⟩
  have hi : Function.Injective k := (Nat.bijective_iff_surjective_and_card _).mpr ⟨hs,hc.symm⟩ |>.1
  refine ⟨f,⟨?_,hf⟩,hpf⟩
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro v hv
  have hv1 : v.1=0 := (hpf v).symm.trans (by rw [show f v=0 from hv,map_zero])
  have hz : k v.2=k 0 := Subtype.ext (by
    change f (0,v.2)=f (0,0)
    rw [show (0,v.2)=v from Prod.ext hv1.symm rfl,show f v=0 from hv]
    exact (map_zero f).symm)
  exact Prod.ext hv1 (hi hz)

private theorem embedded_linear_movement
    {F V G J : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Group G] [Group J] (ρ : Representation F J V)
    (j : Multiplicative V →* G) (B X : Subgroup G)
    (β : B →* J) (hact : ∀ b : B, ∀ v : V,
      j (Multiplicative.ofAdd (ρ (β b) v))=b.val*j (Multiplicative.ofAdd v)*b.val⁻¹)
    (D : Submodule F V) (hX : D.toAddSubgroup.toSubgroup.map j=X) :
    ∃ E : Submodule F V, E.toAddSubgroup.toSubgroup.map j=⁅B,X⁆ := by
  let E : Submodule F V := ⨆ b : B, D.map (ρ (β b)-LinearMap.id)
  refine ⟨E,le_antisymm ?_ ?_⟩
  · rintro x ⟨v,hv,rfl⟩
    change v.toAdd ∈ E at hv
    change j (Multiplicative.ofAdd v.toAdd) ∈ _
    refine Submodule.iSup_induction _ (motive := fun w => j (Multiplicative.ofAdd w) ∈ ⁅B,X⁆) hv ?_ ?_ ?_
    · intro b v hv
      obtain ⟨w,hw,rfl⟩ := hv
      change j (Multiplicative.ofAdd (ρ (β b) w-w)) ∈ _
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      exact commutator_mem_commutator b.property (hX ▸ ⟨_,hw,rfl⟩)
    · exact (map_one j).symm ▸ one_mem _
    · intro u v hu hv
      simpa only [ofAdd_add,map_mul] using (⁅B,X⁆).mul_mem hu hv
  · apply commutator_le.mpr
    intro b hb x hx
    obtain ⟨v,hv,rfl⟩ := hX.symm ▸ hx
    refine ⟨Multiplicative.ofAdd (ρ (β ⟨b,hb⟩) v.toAdd-v.toAdd),?_,?_⟩
    · change ρ (β ⟨b,hb⟩) v.toAdd-v.toAdd ∈ E
      exact (le_iSup (fun b : B => D.map (ρ (β b)-LinearMap.id)) ⟨b,hb⟩) ⟨v.toAdd,hv,rfl⟩
    · rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl


private theorem embedded_linear_fixed
    {F V G J : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Group G] [Group J] (ρ : Representation F J V)
    (j : Multiplicative V →* G) (hj : Function.Injective j) (B : Subgroup G)
    (β : B →* J) (hact : ∀ b : B, ∀ v : V,
      j (Multiplicative.ofAdd (ρ (β b) v))=b.val*j (Multiplicative.ofAdd v)*b.val⁻¹) :
    ∃ D : Submodule F V, D.toAddSubgroup.toSubgroup.map j=
      j.range ⊓ centralizer (B : Set G) := by
  let D : Submodule F V := ⨅ b : B, LinearMap.ker (ρ (β b)-LinearMap.id)
  refine ⟨D,le_antisymm ?_ ?_⟩
  · rintro x ⟨v,hv,rfl⟩
    change v.toAdd ∈ D at hv
    refine ⟨⟨v,rfl⟩,fun b hb => ?_⟩
    have he : ρ (β ⟨b,hb⟩) v.toAdd=v.toAdd :=
      sub_eq_zero.mp ((iInf_le (fun b : B => LinearMap.ker (ρ (β b)-LinearMap.id)) ⟨b,hb⟩) hv)
    have hh := congrArg (fun w => j (Multiplicative.ofAdd w)) he
    rw [hact,mul_inv_eq_iff_eq_mul] at hh
    exact hh
  · rintro x ⟨⟨v,rfl⟩,hv⟩
    refine ⟨v,?_,rfl⟩
    change v.toAdd ∈ D
    simp only [D,Submodule.mem_iInf]
    intro b
    change ρ (β b) v.toAdd-v.toAdd=0
    apply sub_eq_zero.mpr
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hact,ofAdd_toAdd,hv b.val b.property,mul_inv_cancel_right]

private theorem embedded_subspace_card
    {F V G : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Group G]
    (j : Multiplicative V →* G) (hj : Function.Injective j) (D : Submodule F V) :
    Nat.card (D.toAddSubgroup.toSubgroup.map j)=Nat.card F^Module.finrank F D := by
  rw [card_map_of_injective hj]
  let e : D.toAddSubgroup.toSubgroup ≃ D :=
    { toFun := fun x => ⟨x.val.toAdd,x.property⟩
      invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := F)]

private theorem full_cover_embedding
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hc : Nat.card p.toLinearMap.ker=Nat.card F)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (U X Z : Subgroup G)
    (hjr : j.range=U) (β : X →* L (K := F)) (γ : Z →* L (K := F))
    (hβ : ∀ x : X, ∀ w : W, j (Multiplicative.ofAdd (σ (β x) w))=
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹)
    (hγ : ∀ z : Z, ∀ w : W, j (Multiplicative.ofAdd (σ (γ z) w))=
      z.val*j (Multiplicative.ofAdd w)*z.val⁻¹) :
    ∃ j₀ : Multiplicative (Space (K := F)) →* G,
      Function.Injective j₀ ∧ j₀.range=U ∧
      (∀ x : X, ∀ v : Space (K := F), j₀ (Multiplicative.ofAdd (action (β x) v))=
        x.val*j₀ (Multiplicative.ofAdd v)*x.val⁻¹) ∧
      (∀ z : Z, ∀ v : Space (K := F), j₀ (Multiplicative.ofAdd (action (γ z) v))=
        z.val*j₀ (Multiplicative.ofAdd v)*z.val⁻¹) := by
  obtain ⟨f,hf,hpf⟩ := full_cover_quotient p hp hc
  let j₀ : Multiplicative (Space (K := F)) →* G := j.comp f.toLinearMap.toAddMonoidHom.toMultiplicative
  have hj₀ : Function.Injective j₀ := by
    intro v w he
    exact Multiplicative.toAdd.injective (hf.1 (congrArg Multiplicative.toAdd (hj he)))
  have hr : j₀.range=U := by
    apply le_antisymm
    · rintro x ⟨v,rfl⟩
      exact hjr ▸ ⟨_,rfl⟩
    · intro x hx
      obtain ⟨w,rfl⟩ := hjr.symm ▸ hx
      obtain ⟨v,hv⟩ := hf.2 w.toAdd
      exact ⟨Multiplicative.ofAdd v,congrArg j (congrArg Multiplicative.ofAdd hv)⟩
  have hβ₀ (x : X) (v : Space (K := F)) :
      j₀ (Multiplicative.ofAdd (action (β x) v))=
        x.val*j₀ (Multiplicative.ofAdd v)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (f (binaryAction (β x) v)))=_
    rw [f.isIntertwining,hβ]
    rfl
  have hγ₀ (z : Z) (v : Space (K := F)) :
      j₀ (Multiplicative.ofAdd (action (γ z) v))=
        z.val*j₀ (Multiplicative.ofAdd v)*z.val⁻¹ := by
    change j (Multiplicative.ofAdd (f (binaryAction (γ z) v)))=_
    rw [f.isIntertwining,hγ]
    rfl
  exact ⟨j₀,hj₀,hr,hβ₀,hγ₀⟩

private theorem full_cover_fixed_movement_intersection
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hc : Nat.card p.toLinearMap.ker=Nat.card F)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (U X Z : Subgroup G)
    (hjr : j.range=U) (β : X →* L (K := F)) (γ : Z →* L (K := F))
    (hβ : ∀ x : X, ∀ w : W, j (Multiplicative.ofAdd (σ (β x) w))=
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹)
    (hγ : ∀ z : Z, ∀ w : W, j (Multiplicative.ofAdd (σ (γ z) w))=
      z.val*j (Multiplicative.ofAdd w)*z.val⁻¹) :
    Nat.card U=Nat.card F^5 ∧ ∃ r : ℕ,
      Nat.card (⁅X,U⁆ ⊓ ⁅Z,U ⊓ centralizer (X : Set G)⁆ : Subgroup G)=Nat.card F^r := by
  obtain ⟨j₀,hj₀,hr,hβ₀,hγ₀⟩ := full_cover_embedding p hp hc j hj U X Z hjr β γ hβ hγ
  have htop : (⊤ : Submodule F (Space (K := F))).toAddSubgroup.toSubgroup.map j₀=U := by
    exact j₀.range_eq_map.symm.trans hr
  obtain ⟨M,hM⟩ := embedded_linear_movement action j₀ X U β hβ₀ ⊤ htop
  obtain ⟨D,hD⟩ := embedded_linear_fixed action j₀ hj₀ X β hβ₀
  rw [hr] at hD
  obtain ⟨N,hN⟩ := embedded_linear_movement action j₀ Z
    (U ⊓ centralizer (X : Set G)) γ hγ₀ D hD
  constructor
  · rw [←htop,embedded_subspace_card j₀ hj₀,finrank_top,space_finrank]
  · refine ⟨Module.finrank F (M ⊓ N : Submodule F (Space (K := F))),?_⟩
    rw [←hM,←hN,←Subgroup.map_inf _ _ j₀ hj₀]
    exact embedded_subspace_card j₀ hj₀ (M ⊓ N)

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem full_plane_fixed_movement_intersection
    {a t : Vertex d.radical}
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n a t)
    (hfull : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n)
    (X Z : Subgroup (FreeAmalgam d.radical)) (hX : X ≤ Q d.radical t) (hZ : Z ≤ Q d.radical t) :
    Nat.card (U d.radical a)=(2^n)^5 ∧ ∃ r : ℕ,
      Nat.card (⁅X,U d.radical a⁆ ⊓ ⁅Z,U d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))⁆ :
        Subgroup (FreeAmalgam d.radical))=(2^n)^r := by
  let p := MovedSection.coverProjection (replacementMovedSection h d) cv.equiv
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=
      U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hv
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  have hFc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hc : Nat.card p.toLinearMap.ker=Nat.card cv.field.Carrier := by
    rw [←embedded_cover_kernel_card p cv.embedding cv.injective,hk,hfull,hFc]
  simpa only [hFc] using full_cover_fixed_movement_intersection p cv.cover hc
    cv.embedding cv.injective (U d.radical a) X Z cv.range_eq
    (cv.actor.comp (inclusion hX)) (cv.actor.comp (inclusion hZ))
    (fun x w => cv.actor_conjugation (inclusion hX x) w)
    (fun z w => cv.actor_conjugation (inclusion hZ z) w)

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem movement_central_supplement
    {G : Type*} [Group G] (U C Y A : Subgroup G)
    (hCU : C ≤ normalizer (U : Set G)) (hCY : C ≤ centralizer (Y : Set G))
    (hAY : A ≤ Y) : ⁅A,U ⊔ C⁆=⁅A,U⁆ := by
  apply le_antisymm ?_ (commutator_mono le_rfl le_sup_left)
  apply commutator_le.mpr
  intro b hb x hx
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hx
  obtain ⟨u,hu,c,hc,rfl⟩ := hx
  have hbc : Commute b c := hCY hc b (hAY hb)
  rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hbc]
  simpa only [mul_one,mul_inv_cancel_right] using commutator_mem_commutator hb hu

omit [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem midpoint_centralizes_radical
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t) :
    Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (hz.trans he.symm)
  rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
  exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2

/-- The full-size escape intersection has field-power order. The proof realizes
both movements as field subspaces while retaining the original full cover. -/
theorem source_four_large_full_intersection_power
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z)
    (hfull : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n) :
    Nat.card (U d.radical a)=(2^n)^5 ∧ ∃ r : ℕ,
      Nat.card (⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ⊓
        ⁅Z d.radical z,P⁆ : Subgroup (FreeAmalgam d.radical))=(2^n)^r := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y₀ := U d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))
  let C := Z d.radical t
  have geom := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  let cv := Classical.choice geom.1
  have hzQ : Z d.radical z ≤ Q d.radical z :=
    (g.omega_bound z path.end_color (by rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hZT := hzQ.trans c'.core_le_edge
  have hXT : X ≤ Q d.radical t := inf_le_left.trans hZT
  have hCT : C ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    midpoint_centralizes_radical d path.end_color hzt
  have hCA : C ≤ Z d.radical a := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have hCU : C ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (hCA.trans ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCY : C ≤ normalizer (Y₀ : Set (FreeAmalgam d.radical)) :=
    (hCA.trans ((Z d.radical a).le_centralizer.trans (centralizer_le
      (inf_le_left.trans (U_le_Z a))))).trans (Subgroup.centralizer_le_normalizer _)
  have hY : Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))=Y₀ ⊔ C := by
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat,
      sup_comm (U d.radical a),inf_centralizer_sup_of_centralizing C (U d.radical a) X
        hCU (hCT.trans (centralizer_le hXT)),sup_comm]
  have hM : ⁅X,Z d.radical a⁆=⁅X,U d.radical a⁆ := by
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat]
    exact movement_central_supplement (U d.radical a) C (Q d.radical t) X hCU hCT hXT
  have hH : ⁅Z d.radical z,P⁆=⁅Z d.radical z,Y₀⁆ := by
    rw [(source_four_large_escaping_hyperplane h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).2.2.2,hY]
    exact movement_central_supplement Y₀ C (Q d.radical t) (Z d.radical z) hCY hCT hZT
  obtain ⟨hU,r,hr⟩ := full_plane_fixed_movement_intersection h d cv hfull X (Z d.radical z) hXT hZT
  exact ⟨hU,r,by rw [hM,hH]; exact hr⟩

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem subgroup_product_card {G : Type*} [Group G]
    (B C : Subgroup G) (hn : C ≤ normalizer (B : Set G)) :
    Nat.card B * Nat.card C = Nat.card (B ⊓ C : Subgroup G) * Nat.card (B ⊔ C : Subgroup G) := by
  let V := B ⊔ C
  let _ : (B.subgroupOf V).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hindex := relIndex_sup_left (C.subgroupOf V) (B.subgroupOf V)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf le_sup_right] at hindex
  have hindex' : B.relIndex V = (B ⊓ C).relIndex C :=
    hindex.trans (inf_relIndex_right B C).symm
  have hcardV := relIndex_mul_relIndex (⊥ : Subgroup G) B V bot_le le_sup_left
  have hcardC := relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ C) C bot_le inf_le_right
  simp only [relIndex_bot_left] at hcardV hcardC
  rw [hindex'] at hcardV
  rw [←hcardC,←hcardV]
  ac_rfl

private theorem escaping_full_intersection_card
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z)
    (hfull : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n)
    (hHcard : Nat.card (⁅Z d.radical z,P⁆ : Subgroup (FreeAmalgam d.radical))=(2^n)^2)
    (hMnot : ¬ ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ≤ ⁅Z d.radical z,P⁆) :
    Nat.card (⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ⊓
      ⁅Z d.radical z,P⁆ : Subgroup (FreeAmalgam d.radical))=2^n := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let M := ⁅X,Z d.radical a⁆
  let N := ⁅Z d.radical z,P⁆
  let D := U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical))
  let C := Z d.radical t
  let q := 2^n
  have hq : 1 < q := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  obtain ⟨hU,r,hr⟩ := source_four_large_full_intersection_power h d g hb hsat path hat hzt c c'
    hcritical P hP hpoint hi hescape hfull
  have hMcard : Nat.card M=q^2 := by
    have hh := (source_four_large_escaping_movement h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).2.2
    simpa only [hfull,pow_two] using hh
  have geom := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have haQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hRcent : ⁅Z d.radical a,Z d.radical z⁆ ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [commutator_comm]
    exact ((commutator_mono le_rfl haQ).trans
      (source_two_midpoint_containment h d g hb hsat path hat hzt c c')).trans
        (midpoint_centralizes_radical d path.start_color hat)
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hCU : C ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    ((Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat).trans
      ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hRmoving : ⁅Z d.radical a,Z d.radical z⁆=⁅Q d.radical t,U d.radical a⁆ := by
    rw [←geom.2.2.2.2.1,commutator_comm,
      Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat]
    exact movement_central_supplement (U d.radical a) C (Q d.radical t) (Q d.radical t)
      hCU (midpoint_centralizes_radical d path.start_color hat) le_rfl
  have hRD : ⁅Z d.radical a,Z d.radical z⁆ ≤ D := le_inf (by
    rw [hRmoving]
    exact le_normalizer_iff_commutator_le_right.mp (c.edge_le.trans (U_normalized a))) hRcent
  have hMD : M ≤ D := by
    apply le_trans (show M ≤ ⁅Z d.radical a,Z d.radical z⁆ from ?_) hRD
    exact (commutator_mono (show X ≤ Z d.radical z from inf_le_left) le_rfl).trans_eq
      (commutator_comm (Z d.radical z) (Z d.radical a))
  have hND : N ≤ D := by
    dsimp only [N]
    rw [(source_four_large_escaping_hyperplane h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).2.2.2,commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans hRD
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hreverse : q^2 ≤ (Q d.radical a).relIndex (Z d.radical z) := by
    rw [(source_four_large_midpoint_kernels h d g hb hsat path hat hzt c c' hcritical).2.2.2]
  have hindex : D.relIndex (U d.radical a)=q^2 := by
    rw [inf_relIndex_left]
    exact (source_four_large_plane_cover h d g hb hsat rev hzt hat c' c hreverse).2.2.1
  have hDcard : Nat.card D=q^3 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) D (U d.radical a) bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hindex,hU] at hh
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < q^2)
    calc
      Nat.card D*q^2 = q^5 := hh
      _ = q^3*q^2 := by ring
  let : Finite D := Finite.of_injective (inclusion (show D ≤ U d.radical a from inf_le_left)) (inclusion_injective _)
  let : Finite M := Finite.of_injective (inclusion hMD) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion hND) (inclusion_injective _)
  let : Finite (M ⊓ N : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (show M ⊓ N ≤ M from inf_le_left)) (inclusion_injective _)
  have hbound : Nat.card (M ⊓ N : Subgroup (FreeAmalgam d.radical)) < q^2 := by
    have hh := Nat.card_le_card_of_injective (inclusion (show M ⊓ N ≤ M from inf_le_left)) (inclusion_injective _)
    rw [hMcard] at hh
    apply lt_of_le_of_ne hh
    intro he
    have heq : M ⊓ N=M := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [he,hMcard])
    exact hMnot (heq.ge.trans inf_le_right)
  have hrle : r ≤ 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 2 ≤ r)
    change Nat.card (M ⊓ N : Subgroup (FreeAmalgam d.radical))=q^r at hr
    omega
  have hnorm : N ≤ normalizer (M : Set (FreeAmalgam d.radical)) :=
    (hND.trans inf_le_left |>.trans (U_le_Z a)).trans
      ((Z d.radical a).le_centralizer.trans (centralizer_le
        (hMD.trans inf_le_left |>.trans (U_le_Z a)))) |>.trans (Subgroup.centralizer_le_normalizer _)
  have hprod := subgroup_product_card M N hnorm
  have hsup : Nat.card (M ⊔ N : Subgroup (FreeAmalgam d.radical)) ≤ q^3 := by
    have hh := Nat.card_le_card_of_injective (inclusion (sup_le hMD hND)) (inclusion_injective _)
    rwa [hDcard] at hh
  have hrpos : r ≠ 0 := by
    intro he
    change Nat.card (M ⊓ N : Subgroup (FreeAmalgam d.radical))=q^r at hr
    rw [he,pow_zero] at hr
    rw [hMcard,hHcard,hr,one_mul] at hprod
    have hbig : q^3 < q^2*q^2 := by
      calc
        q^3 < q^4 := Nat.pow_lt_pow_right hq (by decide)
        _ = q^2*q^2 := by ring
    exact hbig.not_ge (hprod.trans_le hsup)
  have he : r=1 := by omega
  simpa only [he,pow_one] using hr

/-- The actual hyperplane of source (4) has a field-sized movement intersection
in the unequal-attachment escape case. Its full section-centralizer complement
and both full attachments are retained. -/
theorem source_four_large_unequal_intersection
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      let A₁ := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=2^n ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      (¬ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z →
        ¬ ⁅X,Z d.radical a⁆ ≤ H₀ ∧
        Nat.card A₁=2^n ∧ Nat.card A₀=2^n ∧
        Nat.card (⁅X,Z d.radical a⁆ ⊓ H₀ : Subgroup (FreeAmalgam d.radical))=2^n) := by
  obtain ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hesc⟩ :=
    source_four_large_unequal_hyperplane h d g hb hsat path hat hzt c c' hcritical hne
  refine ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,?_⟩
  intro hescape
  obtain ⟨hn,hfull,hfull'⟩ := hesc hescape
  refine ⟨hn,hfull,hfull',?_⟩
  apply escaping_full_intersection_card h d g hb hsat path hat hzt c c' hcritical
    P hP hpoint hi hescape hfull ?_ hn
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let A := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hHZ : ⁅Z d.radical z,P⁆ ≤ Z d.radical z := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((hP.trans c'.edge_le).trans (Z_normalized d.radical z))
  have hXZ : ⁅X,B⁆ ≤ Z d.radical z := (le_sup_left.trans hjoin.ge).trans hHZ
  have hnorm : A ≤ normalizer ((⁅X,B⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans (U_le_Z z)).trans
      ((Z d.radical z).le_centralizer.trans (centralizer_le hXZ)) |>.trans
        (Subgroup.centralizer_le_normalizer _)
  rw [hjoin,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hnorm hdis,hcard,hfull',pow_two]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
