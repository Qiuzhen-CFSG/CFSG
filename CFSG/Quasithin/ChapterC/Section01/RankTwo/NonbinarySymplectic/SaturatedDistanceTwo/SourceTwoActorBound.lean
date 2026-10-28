module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoLargeCritical

/-!
# The full fixed-core actor bound in source (3.7)(2)

A quadratic actor on the original natural symplectic cover has image order
at most twice the field order when its full commutator has order at most
q times the complete covering kernel. If that kernel were contained in the
commutator, displacement lifting would inject the kernel times a natural
plane into the commutator, contradicting this bound. The escaping kernel
therefore gives an invariant quadratic refinement, whose orthogonal plane
stabilizer supplies the actor bound.

The source application retains both actual critical endpoints, their whole
fixed attachments and the exact saturated radical. The paired full-kernel
order identity supplies the bound in the opposite original cover.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.7)(2), printed p.873.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors

private theorem cover_actor_bound_of_small_displacement
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A : Subgroup G) [Finite U]
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hAU : A ≤ normalizer (U : Set G))
    (hquad : ⁅⁅U,A⁆,A⁆=⊥)
    (hsmall : Nat.card (⁅A,U⁆ : Subgroup G) ≤ Nat.card F *
      Nat.card (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j)) :
    Nat.card (((commutator (Sp F)).subtype.comp β).range) ≤ 2 * Nat.card F := by
  classical
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let α := (commutator (Sp F)).subtype.comp β
  let K := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
  let C := ⁅A,U⁆
  let D := displacementSpace α.range
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
  by_cases hle : Nat.card α.range ≤ Nat.card F
  · exact hle.trans (by omega)
  have hbig : Nat.card F < Nat.card α.range := by omega
  have hP := large_quadratic_displacement_self_orthogonal α.range hq hbig
  have hescape : ¬ K ≤ C := by
    intro hK
    let : Finite C := Finite.of_injective
      (inclusion (le_normalizer_iff_commutator_le_right.mp hAU)) (inclusion_injective _)
    have hlift : ∀ v : D, ∃ w : W, p w=v.val ∧ j (Multiplicative.ofAdd w) ∈ C :=
      fun v => natural_displacement_lifts U A j hjr β σ hact p hp.1 v.val v.property
    choose w hw hm using hlift
    let f : p.toLinearMap.ker × D → C := fun x =>
      ⟨j (Multiplicative.ofAdd (x.1.val+w x.2)),by
        rw [ofAdd_add,map_mul]
        exact C.mul_mem (hK ⟨Multiplicative.ofAdd x.1.val,x.1.property,rfl⟩) (hm x.2)⟩
    have hf : Function.Injective f := by
      rintro ⟨k,v⟩ ⟨l,u⟩ he
      have hh : k.val+w v=l.val+w u :=
        Multiplicative.ofAdd.injective (hj (congrArg Subtype.val he))
      have hvu : v=u := by
        apply Subtype.ext
        have hk : p k.val=0 := k.property
        have hl : p l.val=0 := l.property
        have hpv := congrArg p hh
        simpa only [map_add,hk,hl,zero_add,hw] using hpv
      subst u
      have hkl : k=l := Subtype.ext (add_right_cancel hh)
      subst l
      rfl
    have hcard := Nat.card_le_card_of_injective f hf
    have hkcard : Nat.card K = Nat.card p.toLinearMap.ker := by
      rw [show K=p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j from rfl,
        card_map_of_injective hj]
      exact Nat.card_congr
        { toFun := fun x => ⟨x.val.toAdd,x.property⟩
          invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hdim : Module.finrank F D=2 := by
      have hd := LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate D
      rw [show (form F).orthogonal D=D from hP] at hd
      have hV : Module.finrank F (Theory.SpecificGroups.SymplecticFour.Vector F)=4 := by
        simp [Theory.SpecificGroups.SymplecticFour.Vector]
      rw [hV] at hd
      omega
    rw [Nat.card_prod,Module.natCard_eq_pow_finrank (K := F) (V := D),hdim] at hcard
    change Nat.card C ≤ Nat.card F * Nat.card K at hsmall
    rw [hkcard] at hsmall
    have hkpos : 0 < Nat.card p.toLinearMap.ker := Nat.card_pos
    have hF : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  obtain ⟨c,hc⟩ := embedded_cover_preserves_refinement_of_kernel_escape C A σ p hp j β
    hact (by rw [hjr]) hescape
  apply card_le_of_fixes_self_orthogonal_plane α.range D hP
    (fun a v hv => displacementSpace_le_fixedSpace_of_quadratic α.range hq hv a.val a.property) c
  rintro ⟨_,⟨a,rfl⟩⟩ v
  exact hc a v


open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The fixed attachment has actor image of order at most twice the field
order in the opposite full-core quotient, as in MS93 (3.7)(2), p.873. -/
theorem source_two_large_fixedCore_actor_index
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    (Q d.radical z).relIndex (fixedCore d.radical a) ≤ 2 * 2^n := by
  let := replacementComponent_normal h d
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (U_le_Z z)) (inclusion_injective _)
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
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
  have haction (x : stabilizer d.radical z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hAS : fixedCore d.radical a ≤ stabilizer d.radical z :=
    (inf_le_left.trans c.core_le_edge).trans c'.edge_le
  let β := γ.comp (inclusion hAS)
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  have hquad : ⁅⁅U d.radical z,fixedCore d.radical a⁆,fixedCore d.radical a⁆=⊥ :=
    le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      (source_two_fixedCore_quadratic h d g hb hsat path hat hzt c c').le) bot_le
  have hm := source_two_large_displacement_card h d g hb hsat path hat hzt c c' hlarge
  rw [fixedCore_displacement_eq_moving h d g hb path hat hzt c c',
    commutator_comm (U d.radical z)] at hm
  have hcards := (source_two_large_paired_fixed_layers h d g hb hsat path hat hzt c c' hlarge).2.2.2.1
  rw [hcards] at hm
  have hbound := cover_actor_bound_of_small_displacement (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) he (U d.radical z) (fixedCore d.radical a)
    j hj hjr β (fun x => haction (inclusion hAS x)) (hAS.trans (U_normalized z)) hquad
    (by simpa only [hk,E.card_eq,hE] using hm)
  have hαker : α.ker = (Q d.radical z).subgroupOf (fixedCore d.radical a) := by
    have hkκ : κ.ker = (Q d.radical z).subgroupOf (stabilizer d.radical z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [α,β,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  have hi : (Q d.radical z).relIndex (fixedCore d.radical a)=Nat.card α.range := by
    rw [relIndex,←hαker,index_ker]
  rw [hi]
  simpa only [E.card_eq,hE] using hbound

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
