module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourFullIntersection

/-!
# The opposite section centralizer in the full-attachment escape case

In MS93 (3.7)(4), let X be the selected Z-hyperplane and H its root
movement. In the escaping unequal-attachment branch, the opposite full
attachment has order q and the pointwise centralizer of X has index q in
the opposite Z. We prove that centralizing X/H gives exactly the same
subgroup as centralizing X, with the original section centralizer retained.

The full universal orthogonal cover identifies the original moving module
with a five-dimensional space over its own field. Both the fixed space of
X and H = [Z, C_U(X)] are field subspaces. The vectors whose displacements
under X lie in H therefore form a field subspace containing the fixed
hyperplane. Strict enlargement would fill the entire moving module,
contradicting the previously proved noncontainment of its movement in H.
Adjoining the central midpoint supplement gives the assertion on the full
opposite Z. The Chapter11 application uses its literal quotient and action.

This establishes the section-centralizer index used in the middle of
printed p.875. The ensuing complement comparison and root-element selection,
the nonescaping branch, source (5)/(6), and the final field restriction remain.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(4), printed p.875. The private full-cover transports reuse the
checked constructions of SourceFourFullIntersection and SourceFourFullSaturation.
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

private theorem embedded_section_centralizer
    {F V G J : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Group G] [Group J]
    (ρ : Representation F J V) (j : Multiplicative V →* G) (hj : Function.Injective j)
    (X B : Subgroup G) (β : X →* J) (γ : B →* J)
    (hβ : ∀ x : X, ∀ v : V,
      j (Multiplicative.ofAdd (ρ (β x) v))=x.val*j (Multiplicative.ofAdd v)*x.val⁻¹)
    (hγ : ∀ b : B, ∀ v : V,
      j (Multiplicative.ofAdd (ρ (γ b) v))=b.val*j (Multiplicative.ofAdd v)*b.val⁻¹)
    (hi : (centralizer (X : Set G)).relIndex j.range=Nat.card F)
    (hn : ¬ ⁅X,j.range⁆ ≤ ⁅B,j.range ⊓ centralizer (X : Set G)⁆)
    (u : G) (hu : u ∈ j.range) :
    (∀ x ∈ X, ⁅x,u⁆ ∈ ⁅B,j.range ⊓ centralizer (X : Set G)⁆) ↔
      u ∈ centralizer (X : Set G) := by
  obtain ⟨D,hD⟩ := embedded_linear_fixed ρ j hj X β hβ
  obtain ⟨N,hN⟩ := embedded_linear_movement ρ j B
    (j.range ⊓ centralizer (X : Set G)) γ hγ D hD
  have mem_image (S : Submodule F V) (v : V) :
      j (Multiplicative.ofAdd v) ∈ S.toAddSubgroup.toSubgroup.map j ↔ v ∈ S := by
    constructor
    · rintro ⟨w,hw,he⟩
      change w.toAdd ∈ S at hw
      have he' : w.toAdd=v := congrArg Multiplicative.toAdd (hj he)
      exact he' ▸ hw
    · intro hv
      exact ⟨_,hv,rfl⟩
  let E : Submodule F V := ⨅ x : X, N.comap (ρ (β x)-LinearMap.id)
  have hDE : D ≤ E := by
    intro v hv
    simp only [E,Submodule.mem_iInf,Submodule.mem_comap]
    intro x
    have hh := hD ▸ (mem_image D v).mpr hv
    have he : ρ (β x) v=v := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hβ,hh.2 x.val x.property,mul_inv_cancel_right]
    change ρ (β x) v-v ∈ N
    rw [he,sub_self]
    exact N.zero_mem
  have hEtop : E ≠ ⊤ := by
    intro he
    apply hn
    apply commutator_le.mpr
    intro x hx v hv
    obtain ⟨w,rfl⟩ := hv
    have hw : w.toAdd ∈ E := he.symm ▸ Submodule.mem_top
    have hmove : ρ (β ⟨x,hx⟩) w.toAdd-w.toAdd ∈ N :=
      (iInf_le (fun x : X => N.comap (ρ (β x)-LinearMap.id)) ⟨x,hx⟩) hw
    have hh := hN ▸ (mem_image N _).mpr hmove
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hβ] at hh
    exact hh
  have htop : (⊤ : Submodule F V).toAddSubgroup.toSubgroup.map j=j.range :=
    j.range_eq_map.symm
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup G)
    (D.toAddSubgroup.toSubgroup.map j) j.range bot_le (by rw [hD]; exact inf_le_left)
  rw [relIndex_bot_left,relIndex_bot_left,hD,inf_relIndex_left,hi,←hD,
    ←htop,embedded_subspace_card j hj D,embedded_subspace_card j hj ⊤,
    finrank_top,←pow_succ] at hprod
  have hq : 1 < Nat.card F := by
    classical
    let := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hd : Module.finrank F D+1=Module.finrank F V := Nat.pow_right_injective hq hprod
  have hdim := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hEtop)
  rw [finrank_top] at hdim
  have hED : E=D := (Submodule.eq_of_le_of_finrank_le hDE (by omega)).symm
  constructor
  · intro hm
    obtain ⟨v,rfl⟩ := hu
    have hvE : v.toAdd ∈ E := by
      simp only [E,Submodule.mem_iInf,Submodule.mem_comap]
      intro x
      apply (mem_image N _).mp
      rw [hN]
      change j (Multiplicative.ofAdd (ρ (β x) v.toAdd-v.toAdd)) ∈ _
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hβ]
      exact hm x.val x.property
    exact (hD ▸ (mem_image D v.toAdd).mpr (hED ▸ hvE)).2
  · intro hc x hx
    rw [commutatorElement_eq_one_iff_commute.mpr (hc x hx)]
    exact one_mem _

private theorem central_supplement_fixed_index {G : Type*} [Group G]
    (V C D A : Subgroup G) [Finite D] [IsMulCommutative D]
    (hVD : V ≤ D) (hCD : C ≤ D) (hgen : D=V ⊔ C)
    (hCA : C ≤ centralizer (A : Set G)) :
    (centralizer (A : Set G)).relIndex D=(centralizer (A : Set G)).relIndex V := by
  let X := D ⊓ centralizer (A : Set G)
  have hCX : C ≤ X := le_inf hCD hCA
  have hVX : V ⊔ X=D := le_antisymm (sup_le hVD inf_le_left)
    (hgen.le.trans (sup_le le_sup_left (hCX.trans le_sup_right)))
  have hXU : X ≤ normalizer (V : Set G) :=
    (inf_le_left.trans (D.le_centralizer.trans (centralizer_le hVD))).trans
      (Subgroup.centralizer_le_normalizer _)
  let : Finite X := Finite.of_injective (inclusion (show X ≤ D from inf_le_left))
    (inclusion_injective _)
  have he : X ⊓ V=V ⊓ centralizer (A : Set G) := by
    ext x
    exact ⟨fun hx => ⟨hx.2,hx.1.2⟩,fun hx => ⟨⟨hVD hx.1,hx.2⟩,hx.1⟩⟩
  calc
    _ = X.relIndex D := (inf_relIndex_left _ _).symm
    _ = X.relIndex (V ⊔ X) := congrArg (X.relIndex ·) hVX.symm
    _ = X.relIndex V := relIndex_sup_of_normalizes V X hXU
    _ = _ := by rw [←inf_relIndex_right,he,inf_relIndex_left]

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h


private theorem full_plane_section_centralizer
    {a t : Vertex d.radical}
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n a t)
    (hfull : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n)
    (X B : Subgroup (FreeAmalgam d.radical)) (hX : X ≤ Q d.radical t) (hB : B ≤ Q d.radical t)
    (hi : (centralizer (X : Set (FreeAmalgam d.radical))).relIndex (U d.radical a)=2^n)
    (hn : ¬ ⁅X,U d.radical a⁆ ≤
      ⁅B,U d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))⁆)
    (u : FreeAmalgam d.radical) (hu : u ∈ U d.radical a) :
    (∀ x ∈ X, ⁅x,u⁆ ∈ ⁅B,U d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))⁆) ↔
      u ∈ centralizer (X : Set (FreeAmalgam d.radical)) := by
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
  obtain ⟨j,hj,hr,hβ,hγ⟩ := full_cover_embedding p cv.cover hc
    cv.embedding cv.injective (U d.radical a) X B cv.range_eq
    (cv.actor.comp (inclusion hX)) (cv.actor.comp (inclusion hB))
    (fun x w => cv.actor_conjugation (inclusion hX x) w)
    (fun b w => cv.actor_conjugation (inclusion hB b) w)
  have hi' : (centralizer (X : Set (FreeAmalgam d.radical))).relIndex j.range=Nat.card cv.field.Carrier := by
    rwa [hr,hFc]
  have hh := embedded_section_centralizer action j hj X B _ _ hβ hγ hi'
    (by rwa [hr]) u (by rwa [hr])
  rwa [hr] at hh
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


/-- On the full opposite Z, centralizing the selected hyperplane modulo
its root movement is equivalent to centralizing that hyperplane pointwise.
The arbitrary endpoint markings and entire fixed attachment are retained. -/
theorem source_four_large_full_section_centralizer
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
    (hMnot : ¬ ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ≤
      ⁅Z d.radical z,P⁆)
    (u : FreeAmalgam d.radical) (hu : u ∈ Z d.radical a) :
    (∀ x ∈ Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),
      ⁅x,u⁆ ∈ ⁅Z d.radical z,P⁆) ↔
      u ∈ centralizer (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y₀ := U d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))
  let C := Z d.radical t
  have geom := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  let cv := Classical.choice geom.1
  have hzQ : Z d.radical z ≤ Q d.radical z :=
    (g.omega_bound z path.end_color (by rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hZT : Z d.radical z ≤ Q d.radical t := hzQ.trans c'.core_le_edge
  have hXT : X ≤ Q d.radical t := inf_le_left.trans hZT
  have hCT : C ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    midpoint_centralizes_radical d path.end_color hzt
  have hCA : C ≤ Z d.radical a := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  let := finite_Z d.radical a
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
  have hYindex : Y₀.relIndex (U d.radical a)=2^n := by
    rw [inf_relIndex_left]
    rw [←central_supplement_fixed_index (U d.radical a) C (Z d.radical a) X
      (U_le_Z a) hCA (Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat)
      (hCT.trans (centralizer_le hXT))]
    rw [←inf_relIndex_left]
    exact (source_four_large_escaping_hyperplane h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).1
  have hu' : u ∈ U d.radical a ⊔ C := by
    rwa [←Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat]
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hu'
  obtain ⟨v,hv,w,hw,rfl⟩ := hu'
  have hval (x : FreeAmalgam d.radical) (hx : x ∈ X) : ⁅x,v*w⁆=⁅x,v⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_commute.mpr (hCT hw x (hXT hx))]
    simp only [mul_one,mul_inv_cancel_right]
  have hfix : v*w ∈ centralizer (X : Set (FreeAmalgam d.radical)) ↔
      v ∈ centralizer (X : Set (FreeAmalgam d.radical)) := by
    constructor
    · intro hc x hx
      apply commutatorElement_eq_one_iff_commute.mp
      rw [←hval x hx,commutatorElement_eq_one_iff_commute.mpr (hc x hx)]
    · intro hc x hx
      apply commutatorElement_eq_one_iff_commute.mp
      rw [hval x hx,commutatorElement_eq_one_iff_commute.mpr (hc x hx)]
  change (∀ x ∈ X, ⁅x,v*w⁆ ∈ ⁅Z d.radical z,P⁆) ↔
    v*w ∈ centralizer (X : Set (FreeAmalgam d.radical))
  rw [hfix]
  have hh := full_plane_section_centralizer h d cv hfull X (Z d.radical z) hXT hZT
    (by rwa [inf_relIndex_left] at hYindex) (by rwa [←hM,←hH]) v hv
  rw [←hH] at hh
  exact (forall₂_congr fun x hx => by rw [hval x hx]).trans hh


/-- The source hyperplane in the unequal-attachment branch has the same
opposite section and pointwise centralizers in the escaping case, and their
index is the field order. No extra full-kernel or index premise remains. -/
theorem source_four_large_unequal_section_centralizer
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
        Nat.card (⁅X,Z d.radical a⁆ ⊓ H₀ : Subgroup (FreeAmalgam d.radical))=2^n ∧
        Z d.radical a ⊓ B=Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
        (Z d.radical a ⊓ B).relIndex (Z d.radical a)=2^n) := by
  obtain ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hesc⟩ :=
    source_four_large_unequal_intersection h d g hb hsat path hat hzt c c' hcritical hne
  refine ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,?_⟩
  intro hescape
  obtain ⟨hn,hfull,hfull',hIcard⟩ := hesc hescape
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  have hZaT : Z d.radical a ≤ Q d.radical t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]
      change 0 < g.b d.radical
      omega)).trans ((omegaCenter_le _).trans c.core_le_edge)
  have he : Z d.radical a ⊓ B=Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro u ⟨hu,hbB⟩
      refine ⟨hu,?_⟩
      apply (source_four_large_full_section_centralizer h d g hb hsat path hat hzt c c'
        hcritical P hP hpoint hi hescape hfull hn u hu).mp
      intro x hx
      rw [←commutatorElement_inv]
      exact inv_mem (((hmem u).mp hbB).2 x hx)
    · rintro u ⟨hu,hc⟩
      refine ⟨hu,(hmem u).mpr ⟨hZaT hu,?_⟩⟩
      intro x hx
      rw [commutatorElement_eq_one_iff_commute.mpr (hc x hx).symm]
      exact one_mem _
  refine ⟨hn,hfull,hfull',hIcard,he,?_⟩
  rw [he]
  exact (source_four_large_escaping_hyperplane h d g hb hsat path hat hzt c c'
    hcritical P hP hpoint hi hescape).1

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
