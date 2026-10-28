module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourFullIntersection

/-!
# Field-span obstruction in the full-attachment escape case

In MS93 (3.7)(4), the escaping opposite centralizer is a hyperplane whose
quotient by the common-radical fixed layer has dimension one over its own
field. At full attachment order, the universal orthogonal cover maps
bijectively onto the original moving module. Both its fixed spaces and
movements therefore retain this field structure through the actual embedding.

The vectors whose individual displacements lie in the opposite root
movement form a field subspace containing the full fixed layer. A single
nontrivially moving vector in this subspace fills the one-dimensional
quotient, forcing containment of the entire hyperplane movement. The two
movements have equal order q squared, so containment contradicts their
previously proved inequality in the unequal-attachment branch. Thus every
nontrivially moving element of that centralizer has a value outside the
opposite movement. The literal Chapter11 consumer retains the original
quotient/action maps and both complete attachments.

This proves the second-field obstruction in the middle of printed p.875.
Selecting the root element whose displacement is the intersection, completing
the nonescaping branch, source (5)/(6) and the field restriction remain.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(4), printed p.875. The private full-cover transports are the
checked constructions used in SourceFourFullIntersection.
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

private theorem embedded_fixed_hyperplane_saturation
    {F V G J : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Group G] [Group J]
    (ρ : Representation F J V) (j : Multiplicative V →* G) (hj : Function.Injective j)
    (T X B : Subgroup G) (hX : X ≤ T) (hB : B ≤ T) (γ : T →* J)
    (hact : ∀ t : T, ∀ v : V,
      j (Multiplicative.ofAdd (ρ (γ t) v))=t.val*j (Multiplicative.ofAdd v)*t.val⁻¹)
    (hi : (centralizer (T : Set G)).relIndex
      (j.range ⊓ centralizer (X : Set G))=Nat.card F)
    (y : G) (hy : y ∈ j.range ⊓ centralizer (X : Set G))
    (hyn : ∃ b ∈ B, ⁅b,y⁆ ≠ 1)
    (hym : ∀ b ∈ B, ⁅b,y⁆ ∈ ⁅X,j.range⁆) :
    ⁅B,j.range ⊓ centralizer (X : Set G)⁆ ≤ ⁅X,j.range⁆ := by
  let β := γ.comp (inclusion hX)
  let δ := γ.comp (inclusion hB)
  have hβact (x : X) (v : V) :
      j (Multiplicative.ofAdd (ρ (β x) v))=x.val*j (Multiplicative.ofAdd v)*x.val⁻¹ :=
    hact (inclusion hX x) v
  have hδact (b : B) (v : V) :
      j (Multiplicative.ofAdd (ρ (δ b) v))=b.val*j (Multiplicative.ofAdd v)*b.val⁻¹ :=
    hact (inclusion hB b) v
  obtain ⟨Y,hY⟩ := embedded_linear_fixed ρ j hj X β hβact
  obtain ⟨D,hD⟩ := embedded_linear_fixed ρ j hj T γ hact
  have htop : (⊤ : Submodule F V).toAddSubgroup.toSubgroup.map j=j.range :=
    j.range_eq_map.symm
  obtain ⟨M,hM⟩ := embedded_linear_movement ρ j X j.range β hβact ⊤ htop
  have mem_image (S : Submodule F V) (v : V) :
      j (Multiplicative.ofAdd v) ∈ S.toAddSubgroup.toSubgroup.map j ↔ v ∈ S := by
    constructor
    · rintro ⟨w,hw,he⟩
      have he' := hj he
      change w.toAdd ∈ S at hw
      have hwv : w.toAdd=v := congrArg Multiplicative.toAdd he'
      exact hwv ▸ hw
    · intro hv
      exact ⟨_,hv,rfl⟩
  have hDY : D ≤ Y := by
    intro v hv
    apply (mem_image Y v).mp
    rw [hY]
    have hh := hD ▸ (mem_image D v).mpr hv
    exact ⟨hh.1,(centralizer_le hX) hh.2⟩
  have hDgroup : D.toAddSubgroup.toSubgroup.map j ≤ Y.toAddSubgroup.toSubgroup.map j := by
    rw [hD,hY]
    exact inf_le_inf_left _ (centralizer_le hX)
  have hidx : (D.toAddSubgroup.toSubgroup.map j).relIndex
      (Y.toAddSubgroup.toSubgroup.map j)=Nat.card F := by
    rw [hD,hY]
    have he : (j.range ⊓ centralizer (X : Set G)) ⊓ centralizer (T : Set G)=
        j.range ⊓ centralizer (T : Set G) := by
      ext v
      exact ⟨fun hv => ⟨hv.1.1,hv.2⟩,fun hv => ⟨⟨hv.1,(centralizer_le hX) hv.2⟩,hv.2⟩⟩
    rw [←he,inf_relIndex_left]
    exact hi
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup G)
    (D.toAddSubgroup.toSubgroup.map j) (Y.toAddSubgroup.toSubgroup.map j) bot_le hDgroup
  rw [relIndex_bot_left,relIndex_bot_left,hidx,
    embedded_subspace_card j hj D,embedded_subspace_card j hj Y,←pow_succ] at hprod
  have hq : 1 < Nat.card F := by
    classical
    let := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hd : Module.finrank F D+1=Module.finrank F Y :=
    Nat.pow_right_injective hq hprod
  let E : Submodule F V := Y ⊓ ⨅ b : B, M.comap (ρ (δ b)-LinearMap.id)
  have hDE : D ≤ E := by
    intro v hv
    refine ⟨hDY hv,?_⟩
    change v ∈ ⨅ b : B, M.comap (ρ (δ b)-LinearMap.id)
    simp only [Submodule.mem_iInf,Submodule.mem_comap]
    intro b
    have hh := hD ▸ (mem_image D v).mpr hv
    have he : ρ (δ b) v=v := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hδact,hh.2 b.val (hB b.property),mul_inv_cancel_right]
    change ρ (δ b) v-v ∈ M
    rw [he,sub_self]
    exact M.zero_mem
  obtain ⟨v,rfl⟩ := hy.1
  have hvY : v.toAdd ∈ Y := (mem_image Y v.toAdd).mp (hY.symm ▸ hy)
  have hvE : v.toAdd ∈ E := by
    refine ⟨hvY,?_⟩
    change v.toAdd ∈ ⨅ b : B, M.comap (ρ (δ b)-LinearMap.id)
    simp only [Submodule.mem_iInf,Submodule.mem_comap]
    intro b
    apply (mem_image M _).mp
    rw [hM]
    change j (Multiplicative.ofAdd (ρ (δ b) v.toAdd-v.toAdd)) ∈ _
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hδact]
    exact hym b.val b.property
  have hvD : v.toAdd ∉ D := by
    intro hv
    have hh := hD ▸ (mem_image D v.toAdd).mpr hv
    obtain ⟨b,hb,hn⟩ := hyn
    exact hn (commutatorElement_eq_one_iff_commute.mpr (hh.2 b (hB hb)))
  have hstrict : D < E := lt_of_le_of_ne hDE (by intro he; exact hvD (he ▸ hvE))
  have hdim := Submodule.finrank_lt_finrank_of_lt hstrict
  have hEY : E=Y := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  apply commutator_le.mpr
  intro b hb u hu
  obtain ⟨w,hw,rfl⟩ := hY.symm ▸ hu
  have hwE : w.toAdd ∈ E := hEY.symm ▸ hw
  have hm : ρ (δ ⟨b,hb⟩) w.toAdd-w.toAdd ∈ M :=
    (iInf_le (fun b : B => M.comap (ρ (δ b)-LinearMap.id)) ⟨b,hb⟩) hwE.2
  have hh := hM ▸ (mem_image M _).mpr hm
  rw [ofAdd_sub,map_div,div_eq_mul_inv,hδact] at hh
  exact hh
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


private theorem full_plane_fixed_hyperplane_saturation
    {a t : Vertex d.radical}
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n a t)
    (hfull : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n)
    (X B : Subgroup (FreeAmalgam d.radical)) (hX : X ≤ Q d.radical t) (hB : B ≤ Q d.radical t)
    (hi : (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)))=2^n)
    (y : FreeAmalgam d.radical) (hy : y ∈ U d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)))
    (hyn : ∃ b ∈ B, ⁅b,y⁆ ≠ 1)
    (hym : ∀ b ∈ B, ⁅b,y⁆ ∈ ⁅X,U d.radical a⁆) :
    ⁅B,U d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))⁆ ≤ ⁅X,U d.radical a⁆ := by
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
  obtain ⟨j,hj,hr,hact,_⟩ := full_cover_embedding p cv.cover hc
    cv.embedding cv.injective (U d.radical a) (Q d.radical t) (Q d.radical t) cv.range_eq
    cv.actor cv.actor cv.actor_conjugation cv.actor_conjugation
  have hi' : (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
      (j.range ⊓ centralizer (X : Set (FreeAmalgam d.radical)))=Nat.card cv.field.Carrier := by
    rwa [hr,hFc]
  have hh := embedded_fixed_hyperplane_saturation action j hj (Q d.radical t) X B hX hB
    cv.actor hact hi' y (by rwa [hr]) hyn (by rwa [hr])
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


/-- A nontrivially moving element of the escaping opposite hyperplane
spans that hyperplane modulo its full radical fixed layer. Thus if all its
individual displacements lie in the opposite root movement, the whole
hyperplane movement lies there. This uses the original full cover and field. -/
theorem source_four_large_full_hyperplane_saturation
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
    (y : FreeAmalgam d.radical)
    (hy : y ∈ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hyn : ∃ b ∈ Z d.radical z, ⁅b,y⁆ ≠ 1)
    (hym : ∀ b ∈ Z d.radical z, ⁅b,y⁆ ∈
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆) :
    ⁅Z d.radical z,P⁆ ≤
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ := by
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
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hreverse : (2^n)^2 ≤ (Q d.radical a).relIndex (Z d.radical z) := by
    rw [(source_four_large_midpoint_kernels h d g hb hsat path hat hzt c c' hcritical).2.2.2]
  let D := U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical))
  have hDY : D ≤ Y₀ := inf_le_inf_left _ (centralizer_le hXT)
  have hDindex : D.relIndex (U d.radical a)=(2^n)^2 := by
    rw [inf_relIndex_left]
    exact (source_four_large_plane_cover h d g hb hsat rev hzt hat c' c hreverse).2.2.1
  have hindex : (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex Y₀=2^n := by
    have hh := relIndex_mul_relIndex D Y₀ (U d.radical a) hDY inf_le_left
    rw [hYindex,hDindex,pow_two] at hh
    have he : D.relIndex Y₀=2^n := Nat.eq_of_mul_eq_mul_right (by positivity) hh
    have hDY' : Y₀ ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical))=D := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨hDY hx,hx.2⟩⟩
    rwa [←inf_relIndex_left,hDY']
  change y ∈ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) at hy
  rw [hY,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCY] at hy
  obtain ⟨u,hu,v,hv,rfl⟩ := hy
  have hval (b : FreeAmalgam d.radical) (hbZ : b ∈ Z d.radical z) : ⁅b,u*v⁆=⁅b,u⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_commute.mpr (hCT hv b (hZT hbZ))]
    simp only [mul_one,mul_inv_cancel_right]
  have hun : ∃ b ∈ Z d.radical z, ⁅b,u⁆ ≠ 1 := by
    obtain ⟨b,hbZ,hn⟩ := hyn
    exact ⟨b,hbZ,by rwa [←hval b hbZ]⟩
  have hum : ∀ b ∈ Z d.radical z, ⁅b,u⁆ ∈ ⁅X,U d.radical a⁆ := by
    intro b hbZ
    rw [←hM,←hval b hbZ]
    exact hym b hbZ
  change ⁅Z d.radical z,P⁆ ≤ ⁅X,Z d.radical a⁆
  rw [hH,hM]
  exact full_plane_fixed_hyperplane_saturation h d cv hfull X (Z d.radical z) hXT hZT
    hindex u hu hun hum

/-- When the two field-sized movements are distinct, every nontrivially
moving element of the opposite hyperplane has an individual displacement
outside the root movement. This is the second-field obstruction on p.875. -/
theorem source_four_large_full_hyperplane_value_escape
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
    (hMnot : ¬ ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ≤
      ⁅Z d.radical z,P⁆)
    (y : FreeAmalgam d.radical)
    (hy : y ∈ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hyn : ∃ b ∈ Z d.radical z, ⁅b,y⁆ ≠ 1) :
    ∃ b ∈ Z d.radical z, ⁅b,y⁆ ∉
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ := by
  classical
  by_contra hn
  push Not at hn
  have hle := source_four_large_full_hyperplane_saturation h d g hb hsat path hat hzt c c'
    hcritical P hP hpoint hi hescape hfull y hy hyn hn
  let M := ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆
  have hMcard : Nat.card M=(2^n)^2 := by
    have hh := (source_four_large_escaping_movement h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).2.2
    simpa only [hfull,pow_two] using hh
  let : Finite M := Nat.finite_of_card_ne_zero (by rw [hMcard]; positivity)
  have he : ⁅Z d.radical z,P⁆=M := Subgroup.eq_of_le_of_card_ge hle (by rw [hHcard,hMcard])
  exact hMnot he.ge

/-- The actual hyperplane of source (4) has the second-field value obstruction:
in the unequal-attachment escape branch, no nontrivially moving element of its
opposite centralizer has all its values in the movement intersection. The
full attachments, section centralizer and original marking are retained. -/
theorem source_four_large_unequal_value_escape
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
        ∀ y ∈ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)),
          (∃ b ∈ Z d.radical z, ⁅b,y⁆ ≠ 1) →
            ∃ b ∈ Z d.radical z, ⁅b,y⁆ ∉ ⁅X,Z d.radical a⁆) := by
  obtain ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hesc⟩ :=
    source_four_large_unequal_intersection h d g hb hsat path hat hzt c c' hcritical hne
  refine ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,?_⟩
  intro hescape
  obtain ⟨hn,hfull,hfull',hIcard⟩ := hesc hescape
  refine ⟨hn,hfull,hfull',hIcard,?_⟩
  intro y hy hyn
  apply source_four_large_full_hyperplane_value_escape h d g hb hsat path hat hzt c c'
    hcritical P hP hpoint hi hescape hfull ?_ hn y hy hyn
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
