module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.IndexEstimates
public import Theory.Representation.RankOne.QuadraticRecognition.TwoRankOne
public import Theory.Representation.BinaryOffender.ActionImage

/-!
# Sylow-faithful rank-one displacement on the original center

In a faithful binary action of a group of two-rank one, a transvection
involution forces at most three involutions. An involution which is the
square of an element cannot permute that triple nontrivially: its square
root fixes it and permutes the other two. It therefore becomes the unique
involution and is central. Generation by Sylow-fixed vectors would then
make its action trivial, a contradiction.

For a source center action the entire quotient need not act faithfully.
Lift its prescribed Sylow through the original quotient and use 6.2(c) to
prove faithfulness on that Sylow. Pass to the actual action image, preserving
two-rank, Sylow order and fixed-space generation. Every escaping elementary
actor consequently has fixed index at least four when the quotient has
two-rank one and its Sylow has order greater than two. Identity coordinates
return this index to the original moving center.

`ReciprocalSmallUnitary` applies the result to SU₃(2) and PSU₃(2), including
possible special-unitary scalar kernels, in the moving-intersection case.
Source: DGS, *Groups and Graphs* (1985), (8.2), pp.134--135; (6.2)(c),
p.119, and the binary transvection argument used in Chapter 5. The corrected
Sylow-fixed generation is constructed by the original graph preparation.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

private theorem involution_conj {D : Type*} [Group D] (s t : D) (ht : IsInvolution t) :
    IsInvolution (MulAut.conj s t) := by
  constructor
  · intro he
    exact ht.1 ((MulAut.conj s).injective (he.trans (map_one _).symm))
  · rw [←map_pow,ht.2,map_one]

private theorem rank_one_square_fixedCodim {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hr : primeRank 2 D ≤ 1) (ρ : Representation (ZMod 2) D W)
    (hf : Function.Injective ρ) (S : Subgroup D) (hgen : GeneratedByFixedSpace ρ S)
    (s : D) (hs : s ∈ S) (ht : IsInvolution (s^2))
    (a : D) (ha : IsInvolution a) : 2 ≤ fixedCodim ρ (zpowers a) := by
  by_contra! hsmall
  let t := s^2
  have hall (x : D) (hx : IsInvolution x) : fixedCodim ρ (zpowers x) ≤ 1 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp
      (isConj_of_involutions_odd_product a x ha.2 hx.2 (odd_product_of_two_rank_one hr ha hx))
    rw [←hg,fixedCodim_zpowers_conj]
    omega
  have htrans {x : D} (hx : IsInvolution x) :
      LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom x) ∈
        LinearEquiv.transvections (ZMod 2) W := by
    apply LinearEquiv.mem_transvections_of_square_one_rank_one
    · apply LinearEquiv.ext
      intro v
      change ρ x (ρ x v) = v
      rw [←Module.End.mul_apply,←map_mul,←pow_two,hx.2,map_one]
      rfl
    · exact (fixedCodim_zpowers_eq_displacement_rank ρ x) ▸ hall x hx
  have hinj : Function.Injective ρ.asGroupHom := by
    intro x y he
    exact hf (congrArg Units.val he)
  have hst : MulAut.conj s t = t := by dsimp [t]; simp [pow_two,mul_assoc]
  have hss (x : D) : MulAut.conj s (MulAut.conj s x) = MulAut.conj t x := by
    dsimp [t]; simp [pow_two,mul_assoc]
  have hu : ∃ u : D, IsInvolution u ∧ u ≠ t := by
    by_contra! hu
    have hcent (g : D) : Commute g t := by
      have he := hu (MulAut.conj g t) (involution_conj g t ht)
      exact mul_inv_eq_iff_eq_mul.mp he
    have hfixed : (⨆ g : D, (fixedSpace ρ S).map (ρ g)) ≤ fixedSpace ρ (zpowers t) := by
      apply iSup_le
      intro g
      rintro _ ⟨v,hv,rfl⟩
      rw [mem_fixedSpace_zpowers_iff]
      calc
        ρ t (ρ g v) = ρ g (ρ t v) := by
          rw [←Module.End.mul_apply,←map_mul,(hcent g).eq.symm,map_mul,Module.End.mul_apply]
        _ = ρ g v := congrArg (ρ g) (hv ⟨t,S.pow_mem hs 2⟩)
    have htρ : ρ t = 1 := by
      ext v
      exact (mem_fixedSpace_zpowers_iff ρ t v).mp (hfixed (hgen.symm ▸ Submodule.mem_top))
    exact ht.1 (hf (htρ.trans (map_one ρ).symm))
  obtain ⟨u,hu,hut⟩ := hu
  have hthree {x : D} (hx : IsInvolution x) : x = t ∨ x = u ∨ x = u⁻¹*t*u :=
    three_involutions_of_faithful_transvection_representation ρ hinj htrans
    (fun hx hy hxy => ⟨fun hc => hxy (commuting_involutions_eq_of_two_rank_one hr hx hy hc),
      odd_product_of_two_rank_one hr hx hy⟩) ht hu hut.symm hx
  let v := u⁻¹*t*u
  have hv : IsInvolution v := by simpa [v,MulAut.conj_apply] using involution_conj u⁻¹ t ht
  have hvt : v ≠ t := by
    intro he
    have hcomm : Commute t u := by
      change t*u=u*t
      change u⁻¹*t*u=t at he
      have := congrArg (fun z => u*z) he
      simpa [mul_assoc] using this
    exact hut (commuting_involutions_eq_of_two_rank_one hr hu ht hcomm.symm)
  have hvu : v ≠ u := by
    intro he
    apply hut
    have := congrArg (fun z => u*z*u⁻¹) he
    simpa [v,mul_assoc] using this.symm
  have hxu : MulAut.conj s u = u ∨ MulAut.conj s u = v := by
    rcases hthree (involution_conj s u hu) with he | he | he
    · exact (hut ((MulAut.conj s).injective (he.trans hst.symm))).elim
    · exact Or.inl he
    · exact Or.inr he
  have hyu : MulAut.conj s v = u ∨ MulAut.conj s v = v := by
    rcases hthree (involution_conj s v hv) with he | he | he
    · exact (hvt ((MulAut.conj s).injective (he.trans hst.symm))).elim
    · exact Or.inl he
    · exact Or.inr he
  have htu : MulAut.conj t u = u := by
    rw [←hss]
    rcases hxu with he | he
    · rw [he,he]
    · rw [he]
      rcases hyu with he' | he'
      · exact he'
      · exact (hvu ((MulAut.conj s).injective (he'.trans he.symm))).elim
  have hcomm : Commute t u := mul_inv_eq_iff_eq_mul.mp htu
  exact hut (commuting_involutions_eq_of_two_rank_one hr hu ht hcomm.symm)

private theorem rank_one_sylow_square {D : Type*} [Group D] [Finite D]
    (hr : primeRank 2 D ≤ 1) (S : Sylow 2 D) (hSc : 2 < Nat.card S) :
    ∃ s : S, IsInvolution ((s : D)^2) := by
  have hn : ∃ x : S, x^2 ≠ 1 := by
    by_contra! he
    let : IsMulCommutative S := ⟨⟨fun x y => by
      have hi (z : S) : z⁻¹=z := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using he z)
      calc
        x*y = (x*y)⁻¹ := (hi _).symm
        _ = y*x := by rw [mul_inv_rev,hi,hi]⟩⟩
    let : IsElementaryAbelian 2 S := ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr he⟩
    have hh := (primeRank_le_iff_elementary_card_le D).mp hr S inferInstance
    norm_num at hh
    omega
  obtain ⟨x,hx⟩ := hn
  obtain ⟨k,hk⟩ := S.isPGroup'.exists_orderOf_eq_pow x
  have hk2 : 2 ≤ k := by
    by_contra! hsmall
    have hd : orderOf x ∣ 2 := by rw [hk]; interval_cases k <;> norm_num
    exact hx (orderOf_dvd_iff_pow_eq_one.mp hd)
  have hd : 4 ∣ orderOf x := by rw [hk]; exact Nat.pow_dvd_pow 2 hk2
  let s := x^(orderOf x / 4)
  have hs : orderOf s = 4 := orderOf_pow_orderOf_div (orderOf_pos x).ne' hd
  have hs2 : orderOf (s^2) = 2 := by rw [orderOf_pow',hs]; norm_num; decide
  refine ⟨s,?_,?_⟩
  · intro he
    have he' : s^2=1 := Subtype.ext he
    rw [he',orderOf_one] at hs2
    omega
  · have hh : (s^2)^2=1 := orderOf_dvd_iff_pow_eq_one.mp (hs2.symm ▸ dvd_rfl)
    exact congrArg Subtype.val hh

private theorem rank_one_image_field_bound {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hr : primeRank 2 D ≤ 1) (ρ : Representation (ZMod 2) D W)
    (S : Sylow 2 D) (hgen : GeneratedByFixedSpace ρ S)
    (hf : Function.Injective (ρ.comp (S : Subgroup D).subtype))
    (hSc : 2 < Nat.card S) (A : Subgroup D) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    4 ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
  let f := actionHom ρ
  let σ := imageRepresentation ρ
  let T := S.mapSurjective (f := f) ρ.asGroupHom.rangeRestrict_surjective
  have hfaith (s : D) (hs : s ∈ S) (he : ∀ v, ρ s v=v) : s=1 := by
    have hh : (ρ.comp (S : Subgroup D).subtype) ⟨s,hs⟩ =
        (ρ.comp (S : Subgroup D).subtype) 1 := by
      ext v
      change ρ s v = ρ 1 v
      rw [map_one]
      exact he v
    exact congrArg Subtype.val (hf hh)
  let e := faithfulActionEquiv ρ (S : Subgroup D) hfaith
  have hTr : primeRank 2 (actionImage ρ) ≤ 1 := by
    rw [T.primeRank_eq]
    change primeRank 2 (actionSubgroup ρ (S : Subgroup D)) ≤ 1
    rw [←Theory.GroupTheory.primeRank_equiv 2 e,←S.primeRank_eq]
    exact hr
  have hTgen : GeneratedByFixedSpace σ T :=
    generatedByFixedSpace_of_equivariant_surjection ρ σ f LinearMap.id
      Function.surjective_id (fun _ _ => rfl) S hgen
  have hTc : 2 < Nat.card T := by
    change 2 < Nat.card (actionSubgroup ρ (S : Subgroup D))
    rwa [←Nat.card_congr e.toEquiv]
  obtain ⟨s,hs⟩ := rank_one_sylow_square hTr T hTc
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have haf : f a ≠ 1 := by
    intro he
    obtain ⟨R,hAR⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D R S
    have hags : MulAut.conj g a ∈ S := by
      rw [←hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hAR ha)
    have he' : f (MulAut.conj g a)=1 := by
      change f (g*a*g⁻¹)=1
      rw [map_mul,map_mul,map_inv,he,mul_one,mul_inv_cancel]
    have hge := hfaith _ hags ((actionHom_eq_one_iff ρ _).mp he')
    exact ha1 ((MulAut.conj g).injective (hge.trans (map_one _).symm))
  have hat : IsInvolution (f a) := ⟨haf,by rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha,map_one]⟩
  have hd := rank_one_square_fixedCodim hTr σ (imageRepresentation_injective ρ) T hTgen
    s s.property hs (f a) hat
  have hlo : 4 ≤ Nat.card (W ⧸ fixedSpace σ (zpowers (f a))) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hd
  have hle : Nat.card (W ⧸ fixedSpace σ (zpowers (f a))) ≤
      Nat.card (W ⧸ fixedSpace σ (actionSubgroup ρ A)) := by
    let : Finite (W ⧸ fixedSpace σ (actionSubgroup ρ A)) := Finite.of_surjective _
      (fixedSpace σ (actionSubgroup ρ A)).mkQ_surjective
    exact Nat.card_le_card_of_surjective _
      (Submodule.factor_surjective (fixedSpace_antitone σ (zpowers_le.mpr (mem_map_of_mem f ha))))
  simpa only [σ,fixedSpace_actionSubgroup] using hlo.trans hle

open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The original local center action is faithful on each prescribed quotient
Sylow, even when its full special-unitary scalar kernel is nontrivial. -/
theorem source_center_quotient_sylow_faithful (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (hz : center (d.localGroup v) = ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D) :
    letI := CommutingOneProfile.source_center_elementary h v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup v)))
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) v))),
      (∀ (l : d.localGroup v) (z : Additive (Z (family P) v)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      ∀ S : Sylow 2 D, Function.Injective (ρ.comp (S : Subgroup D).subtype) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h v
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  dsimp only
  intro ρ hact S
  obtain ⟨R,hR⟩ := Sylow.mapSurjective_surjective (f := q)
    (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) 2 S
  have hh := source_centerless_two_actor_faithful h d v hz
    ((R : Subgroup L).map L.subtype) (R.isPGroup'.map L.subtype) (map_subtype_le _) e ρ hact
  have he : (((R : Subgroup L).map L.subtype).subgroupOf L).map q = S := by
    rw [subgroupOf,comap_map_eq_self_of_injective L.subtype_injective]
    exact congrArg Sylow.toSubgroup hR
  change Function.Injective (ρ.comp ((((R : Subgroup L).map L.subtype).subgroupOf L).map q).subtype) at hh
  intro x y hxy
  let x' : (((R : Subgroup L).map L.subtype).subgroupOf L).map q := ⟨x,he.symm ▸ x.property⟩
  let y' : (((R : Subgroup L).map L.subtype).subgroupOf L).map q := ⟨y,he.symm ▸ y.property⟩
  apply Subtype.ext
  exact congrArg (fun z : (((R : Subgroup L).map L.subtype).subgroupOf L).map q => (z : D))
    (hh (a₁ := x') (a₂ := y') hxy)

/-- A moving center with a rank-one quotient and a Sylow of order greater
than two has displacement index at least four for every escaping elementary
actor. Faithfulness is required only on the original Sylow and is proved
from 6.2(c); the faithful image retains fixed-space generation. -/
theorem source_moving_rank_one_square_bound (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* D)
    (hr : primeRank 2 D ≤ 1) (hSc : ∀ S : Sylow 2 D, 2 < Nat.card S)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup w.val)
    (hAQ : ¬ A ≤ Q (family P) w.val) :
    4 ≤ (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let F := family P
  let L := d.localGroup w.val
  let Z₀ := Z F w.val
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : Finite Z₀ := Finite.of_injective (inclusion (Z_le_stabilizer F w.val)) (inclusion_injective _)
  obtain ⟨ρ,S,hact,_,_,_,hgen,_,_⟩ := source_moving_center_module h d hc hab hd hb hcomm w hm e
  have hf := source_center_quotient_sylow_faithful h d w.val
    (source_moving_actor h d hc hab hd hb hcomm w hm).1 e ρ hact S
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hne : (A.subgroupOf L).map q ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [local_quotient_kernel F d w.val e] at hk
    exact hAQ (fun a ha => hk (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha))
  have hbound := rank_one_image_field_bound (W := Additive (Z F w.val)) hr ρ S hgen hf (hSc S) _ hne
  have hZL : Z₀ ≤ L := pGroup_le_localGroup F d w.val _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer F w.val)
  have hi := center_action_fixed_index L Z₀ A hZL
    ((d.local_le w.val).trans (stabilizer_normalizes_Z F w.val)) hAL q ρ hact
  rwa [hi] at hbound

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
