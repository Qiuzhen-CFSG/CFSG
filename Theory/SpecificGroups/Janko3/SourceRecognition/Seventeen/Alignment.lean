module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Coordinates
/-!
# Simultaneous compatible embedding conjugacy in Sym(17)

The regular-core coordinates identify the point actions of two faithful
source completions. Conjugacy of their faithful overlap actions aligns
both point groups and the literal overlaps, while preserving the two
marked vertices. The pair-subgroup rigidity theorem then aligns H₂ with
the same equivalence. Arbitrary labellings of the seventeen-point actions
turn this equivalence into one simultaneous conjugator in Sym(17).

Generation and faithfulness give an isomorphism of the completions carrying
H₁ and H₂ to their counterparts. All involutions in 3 × D₁₀ are conjugate,
so this isomorphism may also preserve specified overlap involutions.

This proves Lemma 2.9 and the marked uniqueness needed for Corollary 2.10.
The actual fourth-power-Frobenius PSL₂(16):2 amalgam still must be constructed
before the latter recognition theorem follows; it is not assumed here.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.9 and the deduction of Corollary 2.10, printed p.498.
-/

public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Janko3.SourceRecognition.Seventeen.SourceData
variable {G : Type*} [Group G] (S : SourceData G)

/-- Simultaneous alignment of the point group and its actual overlap, preserving
both distinguished vertices. No compatibility of the initial markings is assumed. -/
theorem exists_point_overlap_equiv {K : Type*} [Group K] (T : SourceData K)
    (b : G) (hb : b*b=1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3)
    (d : K) (hd : d*d=1) (hdout : d ∉ T.H1) (hd2 : d ∈ T.H2) (hd3 : d ∈ T.H3) :
    let X := CosetGraph.Vertex (S.cosetData b hb hout)
    let Y := CosetGraph.Vertex (T.cosetData d hd hdout)
    ∃ f : X ≃ Y,
      f (CosetGraph.base (S.cosetData b hb hout)) = CosetGraph.base (T.cosetData d hd hdout) ∧
      f (CosetGraph.other (S.cosetData b hb hout)) = CosetGraph.other (T.cosetData d hd hdout) ∧
      (S.H1.map (toPermHom G X)).map f.permCongrHom.toMonoidHom = T.H1.map (toPermHom K Y) ∧
      ((S.H1 ⊓ S.H2).map (toPermHom G X)).map f.permCongrHom.toMonoidHom =
        (T.H1 ⊓ T.H2).map (toPermHom K Y) := by
  classical
  let X := CosetGraph.Vertex (S.cosetData b hb hout)
  let Y := CosetGraph.Vertex (T.cosetData d hd hdout)
  let CS := S.coreCoordinates b hb hout hb2 hb3
  let CT := T.coreCoordinates d hd hdout hd2 hd3
  let ρ := toPermHom G X
  let τ := toPermHom K Y
  obtain ⟨e, he⟩ := S.core_actions_equivalent T
  let f : X ≃ Y := (CS.symm.trans (Equiv.optionCongr e.toEquiv)).trans CT
  have hf (z : Option (pCore 2 S.H1)) : f (CS z) = CT (z.map e) := by
    change CT ((Equiv.optionCongr e.toEquiv) (CS.symm (CS z))) = _
    rw [CS.symm_apply_apply]
    rfl
  have hbase : f (CosetGraph.base (S.cosetData b hb hout)) =
      CosetGraph.base (T.cosetData d hd hdout) := by
    simpa only [CS, CT, Option.map_none, S.coreCoordinates_none, T.coreCoordinates_none]
      using hf none
  have hother : f (CosetGraph.other (S.cosetData b hb hout)) =
      CosetGraph.other (T.cosetData d hd hdout) := by
    have hh := hf (some 1)
    simpa only [CS, CT, S.coreCoordinates_some, T.coreCoordinates_some,
      Option.map_some, map_one, Subgroup.coe_one, one_smul] using hh
  have hperm (v : pCore 2 S.H1) (c : S.H2.subgroupOf S.H1) :
      ∃ a : T.H2.subgroupOf T.H1,
        f.permCongrHom (ρ (((v : S.H1) : G) * ((c : S.H1) : G))) =
          τ (((e v : T.H1) : K) * ((a : T.H1) : K)) := by
    have hc : (MulAut.congr e) (S.overlapAction c) ∈ T.overlapAction.range :=
      he ▸ (show (MulAut.congr e) (S.overlapAction c) ∈
        S.overlapAction.range.map (MulAut.congr e).toMonoidHom from
          ⟨_, ⟨c, rfl⟩, rfl⟩)
    obtain ⟨a, ha⟩ := hc
    have hev (w : pCore 2 S.H1) : e (S.overlapAction c w) = T.overlapAction a (e w) := by
      have hh := congrArg (fun k : MulAut (pCore 2 T.H1) => k (e w)) ha
      change T.overlapAction a (e w) = e (S.overlapAction c (e.symm (e w))) at hh
      rw [e.symm_apply_apply] at hh
      exact hh.symm
    have hact (z : Option (pCore 2 S.H1)) :
        f ((((v : S.H1) : G) * ((c : S.H1) : G)) • CS z) =
          (((e v : T.H1) : K) * ((a : T.H1) : K)) • f (CS z) := by
      rw [S.coreCoordinates_smul, hf, hf, T.coreCoordinates_smul]
      cases z with
      | none => rfl
      | some w =>
        simp only [Option.map_some, map_mul, hev]
        rfl
    refine ⟨a, ?_⟩
    apply Equiv.ext
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    obtain ⟨z, rfl⟩ := CS.surjective x
    rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply, f.symm_apply_apply]
    exact hact z
  let : FaithfulSMul G X := (S.consequences b hb hout hb2 hb3).1
  let : FaithfulSMul K Y := (T.consequences d hd hdout hd2 hd3).1
  have hρ : Function.Injective ρ := MulAction.toPerm_injective
  have hτ : Function.Injective τ := MulAction.toPerm_injective
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [T.group_card]; decide)
  have hpoint : (S.H1.map ρ).map f.permCongrHom.toMonoidHom ≤ T.H1.map τ := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨⟨v,c⟩, hvc, _⟩ := S.overlap_complements_core.existsUnique (⟨g,hg⟩ : S.H1)
    obtain ⟨a, ha⟩ := hperm v c
    have hgvc : (((v : S.H1) : G) * ((c : S.H1) : G)) = g :=
      congrArg (fun x : S.H1 => (x : G)) hvc
    refine ⟨((e v : T.H1) : K) * ((a : T.H1) : K),
      T.H1.mul_mem (e v : T.H1).property (a : T.H1).property, ?_⟩
    simpa only [hgvc, MulEquiv.coe_toMonoidHom] using ha.symm
  have hoverlap : ((S.H1 ⊓ S.H2).map ρ).map f.permCongrHom.toMonoidHom ≤
      (T.H1 ⊓ T.H2).map τ := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    let c : S.H2.subgroupOf S.H1 := ⟨⟨g, hg.1⟩, hg.2⟩
    obtain ⟨a, ha⟩ := hperm 1 c
    refine ⟨((a : T.H1) : K), ⟨(a : T.H1).property, a.property⟩, ?_⟩
    simpa only [c, map_one, Subgroup.coe_one, one_mul, MulEquiv.coe_toMonoidHom] using ha.symm
  refine ⟨f, hbase, hother, eq_of_le_of_card_ge hpoint ?_, eq_of_le_of_card_ge hoverlap ?_⟩
  · rw [card_map_of_injective (f := f.permCongrHom.toMonoidHom) f.permCongrHom.injective,
      card_map_of_injective (f := ρ) hρ, card_map_of_injective (f := τ) hτ, S.point_card, T.point_card]
  · rw [card_map_of_injective (f := f.permCongrHom.toMonoidHom) f.permCongrHom.injective,
      card_map_of_injective (f := ρ) hρ, card_map_of_injective (f := τ) hτ, S.overlap_card, T.overlap_card]


/-- Baumeister 2.9 on the faithful source actions: one equivalence simultaneously
conjugates both distinguished subgroup images, preserving the marked pair. -/
theorem exists_compatible_action_equiv {K : Type*} [Group K] (T : SourceData K)
    (b : G) (hb : b*b=1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3)
    (d : K) (hd : d*d=1) (hdout : d ∉ T.H1) (hd2 : d ∈ T.H2) (hd3 : d ∈ T.H3) :
    let X := CosetGraph.Vertex (S.cosetData b hb hout)
    let Y := CosetGraph.Vertex (T.cosetData d hd hdout)
    ∃ f : X ≃ Y,
      f (CosetGraph.base (S.cosetData b hb hout)) = CosetGraph.base (T.cosetData d hd hdout) ∧
      f (CosetGraph.other (S.cosetData b hb hout)) = CosetGraph.other (T.cosetData d hd hdout) ∧
      (S.H1.map (toPermHom G X)).map f.permCongrHom.toMonoidHom = T.H1.map (toPermHom K Y) ∧
      (S.H2.map (toPermHom G X)).map f.permCongrHom.toMonoidHom = T.H2.map (toPermHom K Y) ∧
      ((S.H1 ⊓ S.H2).map (toPermHom G X)).map f.permCongrHom.toMonoidHom =
        (T.H1 ⊓ T.H2).map (toPermHom K Y) := by
  let DS := S.cosetData b hb hout
  let DT := T.cosetData d hd hdout
  let X := CosetGraph.Vertex DS
  let Y := CosetGraph.Vertex DT
  let ρ := toPermHom G X
  let τ := toPermHom K Y
  obtain ⟨f, hbase, hother, hpoint, hoverlap⟩ :=
    S.exists_point_overlap_equiv T b hb hout hb2 hb3 d hd hdout hd2 hd3
  let σ := f.permCongrHom.toMonoidHom.comp ρ
  have heval (g : G) (x : X) : σ g (f x) = f (g • x) := by
    change f (g • f.symm (f x)) = _
    rw [f.symm_apply_apply]
  let : FaithfulSMul G X := (S.consequences b hb hout hb2 hb3).1
  have hρ : Function.Injective ρ := MulAction.toPerm_injective
  have hσ : Function.Injective σ := f.permCongrHom.injective.comp hρ
  let P := S.H2.map σ
  let eP : P ≃* PairGroup := (equivMapOfInjective S.H2 σ hσ).symm.trans S.pairEquiv
  have hpair : P ≤ stabilizer (Equiv.Perm Y) ({CosetGraph.base DT, CosetGraph.other DT} : Set Y) := by
    rintro t ⟨g, hg, rfl⟩
    have hh : g ∈ stabilizer G ({CosetGraph.base DS, CosetGraph.other DS} : Set X) :=
      (S.setwise_pair_stabilizer b hb hout hb2).symm ▸ hg
    change g • ({CosetGraph.base DS, CosetGraph.other DS} : Set X) = _ at hh
    rw [Set.smul_set_insert, Set.smul_set_singleton, Set.pair_eq_pair_iff] at hh
    change σ g • ({CosetGraph.base DT, CosetGraph.other DT} : Set Y) = _
    rw [Set.smul_set_insert, Set.smul_set_singleton, Set.pair_eq_pair_iff]
    change (σ g (CosetGraph.base DT) = CosetGraph.base DT ∧
      σ g (CosetGraph.other DT) = CosetGraph.other DT) ∨
      (σ g (CosetGraph.base DT) = CosetGraph.other DT ∧
        σ g (CosetGraph.other DT) = CosetGraph.base DT)
    rw [← hbase, ← hother, heval, heval]
    exact hh.elim (fun h => Or.inl ⟨congrArg f h.1, congrArg f h.2⟩)
      (fun h => Or.inr ⟨congrArg f h.1, congrArg f h.2⟩)
  have hinter : P ⊓ stabilizer (Equiv.Perm Y) (CosetGraph.base DT) =
      (T.H1 ⊓ T.H2).map τ := by
    rw [← hoverlap, map_map]
    ext t
    constructor
    · rintro ⟨⟨g, hg, rfl⟩, hp⟩
      change σ g (CosetGraph.base DT) = CosetGraph.base DT at hp
      rw [← hbase, heval] at hp
      have hg1 : g ∈ S.H1 := by
        have hh : g ∈ stabilizer G (CosetGraph.base DS) := f.injective hp
        rwa [CosetGraph.point_stabilizer DS] at hh
      exact ⟨g, ⟨hg1,hg⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g,hg.2,rfl⟩, ?_⟩
      change σ g (CosetGraph.base DT) = CosetGraph.base DT
      rw [← hbase, heval]
      apply congrArg f
      have hh : g ∈ stabilizer G (CosetGraph.base DS) :=
        (CosetGraph.point_stabilizer DS).symm ▸ hg.1
      exact hh
  have hsecond := T.pair_image_unique d hd hdout hd2 hd3 P eP hpair hinter
  refine ⟨f,hbase,hother,hpoint,?_,hoverlap⟩
  rw [map_map]
  exact hsecond.symm


/-- The literal simultaneous conjugacy in Sym(17), for arbitrary labellings of
the two degree-seventeen source actions. The same conjugator handles H₁ and H₂. -/
theorem embeddings_conjugate_sym17 {K : Type*} [Group K] (T : SourceData K)
    (b : G) (hb : b*b=1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3)
    (d : K) (hd : d*d=1) (hdout : d ∉ T.H1) (hd2 : d ∈ T.H2) (hd3 : d ∈ T.H3)
    (u : CosetGraph.Vertex (S.cosetData b hb hout) ≃ Fin 17)
    (v : CosetGraph.Vertex (T.cosetData d hd hdout) ≃ Fin 17) :
    let σ := u.permCongrHom.toMonoidHom.comp (toPermHom G (CosetGraph.Vertex (S.cosetData b hb hout)))
    let τ := v.permCongrHom.toMonoidHom.comp (toPermHom K (CosetGraph.Vertex (T.cosetData d hd hdout)))
    ∃ π : Equiv.Perm (Fin 17),
      (S.H1.map σ).map (MulAut.conj π).toMonoidHom = T.H1.map τ ∧
      (S.H2.map σ).map (MulAut.conj π).toMonoidHom = T.H2.map τ ∧
      π (u (CosetGraph.base (S.cosetData b hb hout))) = v (CosetGraph.base (T.cosetData d hd hdout)) ∧
      π (u (CosetGraph.other (S.cosetData b hb hout))) = v (CosetGraph.other (T.cosetData d hd hdout)) := by
  obtain ⟨f,hbase,hother,hpoint,hpair,_⟩ :=
    S.exists_compatible_action_equiv T b hb hout hb2 hb3 d hd hdout hd2 hd3
  let π : Equiv.Perm (Fin 17) := u.symm.trans (f.trans v)
  have hconj : (MulAut.conj π).toMonoidHom.comp u.permCongrHom.toMonoidHom =
      v.permCongrHom.toMonoidHom.comp f.permCongrHom.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    apply Equiv.ext
    intro x
    change π (u (g (u.symm (π.symm x)))) = v (f (g (f.symm (v.symm x))))
    simp only [π, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.symm_apply_apply]
  have htransfer (A : Subgroup G) (B : Subgroup K)
      (hh : (A.map (toPermHom G _)).map f.permCongrHom.toMonoidHom = B.map (toPermHom K _)) :
      (A.map (u.permCongrHom.toMonoidHom.comp (toPermHom G _))).map (MulAut.conj π).toMonoidHom =
        B.map (v.permCongrHom.toMonoidHom.comp (toPermHom K _)) := by
    rw [← map_map, map_map, hconj, ← map_map, hh, map_map]
  refine ⟨π, htransfer _ _ hpoint, htransfer _ _ hpair, ?_, ?_⟩
  · change v (f (u.symm (u _))) = _
    rw [u.symm_apply_apply, hbase]
  · change v (f (u.symm (u _))) = _
    rw [u.symm_apply_apply, hother]


/-- Any two faithful source completions are isomorphic with the point and pair
groups both preserved. The model completion for Corollary 2.10 must still be
constructed; this theorem does not assume or assert its identification. -/
theorem completions_marked_equiv {K : Type*} [Group K] (T : SourceData K) :
    ∃ e : G ≃* K, S.H1.map e.toMonoidHom = T.H1 ∧ S.H2.map e.toMonoidHom = T.H2 := by
  obtain ⟨b,hb,hb2,hb3,hbout⟩ := S.exists_outside_involution
  obtain ⟨d,hd,hd2,hd3,hdout⟩ := T.exists_outside_involution
  let X := CosetGraph.Vertex (S.cosetData b hb hbout)
  let Y := CosetGraph.Vertex (T.cosetData d hd hdout)
  let ρ := toPermHom G X
  let τ := toPermHom K Y
  obtain ⟨f,_,_,hpoint,hpair,_⟩ :=
    S.exists_compatible_action_equiv T b hb hbout hb2 hb3 d hd hdout hd2 hd3
  let σ := f.permCongrHom.toMonoidHom.comp ρ
  let : FaithfulSMul G X := (S.consequences b hb hbout hb2 hb3).1
  let : FaithfulSMul K Y := (T.consequences d hd hdout hd2 hd3).1
  have hρ : Function.Injective ρ := MulAction.toPerm_injective
  have hτ : Function.Injective τ := MulAction.toPerm_injective
  have hσ : Function.Injective σ := f.permCongrHom.injective.comp hρ
  have h1 : S.H1.map σ = T.H1.map τ := by simpa only [map_map] using hpoint
  have h2 : S.H2.map σ = T.H2.map τ := by simpa only [map_map] using hpair
  have hrange : σ.range = τ.range := by
    calc
      σ.range = (S.H1 ⊔ S.H2).map σ := by rw [S.generated, ← MonoidHom.range_eq_map]
      _ = τ.range := by rw [Subgroup.map_sup, h1, h2, ← Subgroup.map_sup, T.generated, ← MonoidHom.range_eq_map]
  let e : G ≃* K := (MonoidHom.ofInjective hσ).trans
    ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hτ).symm)
  have heval (g : G) : τ (e g) = σ g := by
    have hh := (MonoidHom.ofInjective hτ).apply_symm_apply
      ((MulEquiv.subgroupCongr hrange) ((MonoidHom.ofInjective hσ) g))
    exact congrArg Subtype.val hh
  have he : τ.comp e.toMonoidHom = σ := MonoidHom.ext heval
  refine ⟨e, ?_, ?_⟩
  · apply Subgroup.map_injective hτ
    rw [map_map, he, h1]
  · apply Subgroup.map_injective hτ
    rw [map_map, he, h2]


private theorem complement_involutions_conjugate :
    ∀ a b : Complement, a*a=1 → a≠1 → b*b=1 → b≠1 →
      ∃ c : Complement, c*a*c⁻¹=b := by decide +kernel

private theorem square_ne_one_of_order_two {L : Type*} [Group L]
    (a : L) (ha : orderOf a = 2) : a*a=1 ∧ a≠1 := by
  constructor
  · simpa only [ha, pow_two] using pow_orderOf_eq_one a
  · intro he
    simp only [he, orderOf_one] at ha
    omega

/-- Completion uniqueness can preserve any prescribed involutions in the
literal overlaps. This is the marking needed to select the field involution
when the PSL₂(16):2 source amalgam is constructed. -/
theorem completions_equiv_preserving_involution {K : Type*} [Group K] (T : SourceData K)
    (s : G) (hs : s ∈ S.H1 ⊓ S.H2) (hos : orderOf s = 2)
    (t : K) (ht : t ∈ T.H1 ⊓ T.H2) (hot : orderOf t = 2) :
    ∃ e : G ≃* K, S.H1.map e.toMonoidHom = T.H1 ∧
      S.H2.map e.toMonoidHom = T.H2 ∧ e s = t := by
  obtain ⟨e0, he1, he2⟩ := S.completions_marked_equiv T
  have hse : e0 s ∈ T.H1 ⊓ T.H2 :=
    ⟨he1 ▸ (show e0 s ∈ S.H1.map e0.toMonoidHom from ⟨s,hs.1,rfl⟩),
      he2 ▸ (show e0 s ∈ S.H2.map e0.toMonoidHom from ⟨s,hs.2,rfl⟩)⟩
  let a : (T.H1 ⊓ T.H2 : Subgroup K) := ⟨e0 s, hse⟩
  let b : (T.H1 ⊓ T.H2 : Subgroup K) := ⟨t, ht⟩
  have hoa : orderOf (T.overlap12 a) = 2 := by
    calc
      orderOf (T.overlap12 a) = orderOf a := by
        simpa only [MulEquiv.coe_toMonoidHom] using
          orderOf_injective T.overlap12.toMonoidHom T.overlap12.injective a
      _ = orderOf (e0 s) := (Subgroup.orderOf_coe a).symm
      _ = 2 := (orderOf_injective e0.toMonoidHom e0.injective s).trans hos
  have hob : orderOf (T.overlap12 b) = 2 := by
    calc
      orderOf (T.overlap12 b) = orderOf b := by
        simpa only [MulEquiv.coe_toMonoidHom] using
          orderOf_injective T.overlap12.toMonoidHom T.overlap12.injective b
      _ = orderOf t := (Subgroup.orderOf_coe b).symm
      _ = 2 := hot
  obtain ⟨ha2, ha1⟩ := square_ne_one_of_order_two _ hoa
  obtain ⟨hb2, hb1⟩ := square_ne_one_of_order_two _ hob
  obtain ⟨c, hc⟩ := complement_involutions_conjugate _ _ ha2 ha1 hb2 hb1
  let c0 := T.overlap12.symm c
  have hconj : c0 * a * c0⁻¹ = b := by
    apply T.overlap12.injective
    simpa only [map_mul, map_inv, c0, MulEquiv.apply_symm_apply] using hc
  have hc1 : T.H1.map (MulAut.conj (c0 : K)).toMonoidHom = T.H1 :=
    mem_normalizer_iff_map_conj_eq.mp (T.H1.le_normalizer c0.property.1)
  have hc2 : T.H2.map (MulAut.conj (c0 : K)).toMonoidHom = T.H2 :=
    mem_normalizer_iff_map_conj_eq.mp (T.H2.le_normalizer c0.property.2)
  let e := e0.trans (MulAut.conj (c0 : K))
  have he : e.toMonoidHom = (MulAut.conj (c0 : K)).toMonoidHom.comp e0.toMonoidHom := rfl
  refine ⟨e, ?_, ?_, congrArg Subtype.val hconj⟩
  · rw [he, ← map_map, he1, hc1]
  · rw [he, ← map_map, he2, hc2]

end Sporadic.Janko3.SourceRecognition.Seventeen.SourceData
