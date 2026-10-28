module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanMiddleIntersection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSynchronizedSections
public import Theory.Representation.BinarySingerPrimary
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointExteriorExclusion

/-!
# The original Singer actor on the fixed-four span

All polynomial operators are evaluated at an actual order-seven element of
the original L. Its synchronized marking, original point quotient image,
and characteristic section actions are retained literally.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix Representation
open scoped MatrixGroups IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
variable {G : Type*} [Group G]

private def actor (L U : Subgroup G) (hLU : L ≤ normalizer U) : L →* MulAut U :=
  U.normalizerMonoidHom.comp (inclusion hLU)

private def word (L U : Subgroup G) (hLU : L ≤ normalizer U) (s : L) (u : U) : U :=
  u * actor L U hLU (s^3) u * actor L U hLU (s^5) u * actor L U hLU (s^6) u

private theorem word_mem (L U S : Subgroup G) (hLU : L ≤ normalizer U)
    (hLS : L ≤ normalizer S) (s : L) (u : U) (hu : (u : G) ∈ S) :
    (word L U hLU s u : G) ∈ S := by
  have h (n : ℕ) : (actor L U hLU (s^n) u : G) ∈ S :=
    (mem_normalizer_iff.mp (hLS (s^n).property) u).mp hu
  exact S.mul_mem (S.mul_mem (S.mul_mem hu (h 3)) (h 5)) (h 6)

private theorem word_map
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (L U : Subgroup G) (hLU : L ≤ normalizer U)
    (p : U →* Multiplicative E) (ρ : Representation (ZMod 2) L E)
    (hp : ∀ (l : L) (u : U), (p (actor L U hLU l u)).toAdd=ρ l (p u).toAdd)
    (s : L) (u : U) :
    (p (word L U hLU s u)).toAdd=BinarySingerPrimary.projector (ρ s) (p u).toAdd := by
  simp only [word,map_mul]
  change (p u).toAdd+(p (actor L U hLU (s^3) u)).toAdd+
    (p (actor L U hLU (s^5) u)).toAdd+(p (actor L U hLU (s^6) u)).toAdd=_
  rw [hp,hp,hp]
  simp only [map_pow]
  rfl

private theorem marked_coordinates
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    {L S D : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A E}
    (hs : HasSectionModel L S D a σ) :
    ∃ p : S →* Multiplicative E, Function.Surjective p ∧ p.ker=D.subgroupOf S ∧
      ∀ (l : L) (u : S),
        (p (actor L S hs.2.1 l u)).toAdd=σ (a l) (p u).toAdd := by
  obtain ⟨_,_,_,hn,e,he⟩ := hs
  let := hn
  let p := e.toMonoidHom.comp (QuotientGroup.mk' (D.subgroupOf S))
  refine ⟨p,e.surjective.comp (QuotientGroup.mk'_surjective _),?_,?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  · intro l u
    exact he l u _ rfl

private theorem word_in_kernel
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (L U S D : Subgroup G) (hLU : L ≤ normalizer U)
    (a : L →* A) (σ : Representation (ZMod 2) A E)
    (hs : HasSectionModel L S D a σ) (s : L)
    (hz : BinarySingerPrimary.projector (σ (a s))=0)
    (u : U) (hu : (u : G) ∈ S) : (word L U hLU s u : G) ∈ D := by
  obtain ⟨p,_,hk,hp⟩ := marked_coordinates hs
  let v : S := ⟨u,hu⟩
  have he : (p (word L S hs.2.1 s v)).toAdd=0 := by
    have h := word_map L S hs.2.1 p (σ.comp a) hp s v
    change (p (word L S hs.2.1 s v)).toAdd=BinarySingerPrimary.projector (σ (a s)) (p v).toAdd at h
    rw [hz,LinearMap.zero_apply] at h
    exact h
  have hh : word L S hs.2.1 s v ∈ p.ker := he
  rw [hk] at hh
  exact hh

private def imageSpace {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (U S : Subgroup G) (p : U →* Multiplicative E) : Submodule (ZMod 2) E :=
  AddSubgroup.toZModSubmodule 2 ((S.subgroupOf U).map p).toAddSubgroup

private theorem mem_imageSpace {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (U S : Subgroup G) (p : U →* Multiplicative E) (x : E) :
    x ∈ imageSpace U S p ↔ ∃ u : U, (u : G) ∈ S ∧ (p u).toAdd=x := Iff.rfl

private theorem projector_image_commutator
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (L U S : Subgroup G) (hLU : L ≤ normalizer U)
    (p : U →* Multiplicative E) (ρ : Representation (ZMod 2) L E)
    (hp : ∀ (l : L) (u : U), (p (actor L U hLU l u)).toAdd=ρ l (p u).toAdd)
    (s : L) (u : U) (hu : (u : G) ∈ S) :
    BinarySingerPrimary.projector (ρ s) (p u).toAdd ∈ imageSpace U ⁅S,L⁆ p := by
  have hd (n : ℕ) : (ρ (s^n) (p u).toAdd-(p u).toAdd) ∈ imageSpace U ⁅S,L⁆ p := by
    apply (mem_imageSpace _ _ _ _).mpr
    refine ⟨actor L U hLU (s^n) u*u⁻¹,?_,?_⟩
    · rw [commutator_comm]
      exact commutator_mem_commutator (s^n).property hu
    · rw [map_mul,map_inv]
      change (p (actor L U hLU (s^n) u)).toAdd + -(p u).toAdd= _
      rw [hp]
      exact (sub_eq_add_neg _ _).symm
  have h := (imageSpace U ⁅S,L⁆ p).add_mem ((imageSpace U ⁅S,L⁆ p).add_mem (hd 3) (hd 5)) (hd 6)
  have he : BinarySingerPrimary.projector (ρ s) (p u).toAdd =
      (ρ (s^3) (p u).toAdd-(p u).toAdd)+
      (ρ (s^5) (p u).toAdd-(p u).toAdd)+(ρ (s^6) (p u).toAdd-(p u).toAdd) := by
    simp only [BinarySingerPrimary.projector,LinearMap.add_apply,Module.End.one_apply,map_pow]
    simp only [sub_eq_add_neg,ZModModule.neg_eq_self]
    have hthree (v : E) : (3 : ℤ) • v=v := by
      rw [←Int.cast_smul_eq_zsmul (ZMod 2)]
      change (3 : ZMod 2) • v=v
      rw [show (3 : ZMod 2)=1 by decide,one_smul]
    abel_nf
    rw [hthree]
  exact he ▸ h


private theorem bound_from_original_sections
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (L U Q D Phi ZQ V : Subgroup G) (hLU : L ≤ normalizer U)
    (p : U →* Multiplicative E) (hps : Function.Surjective p)
    (ρ : Representation (ZMod 2) L E)
    (hp : ∀ (l : L) (u : U), (p (actor L U hLU l u)).toAdd=ρ l (p u).toAdd)
    (a : L →* SL(3,ZMod 2))
    (hseed : HasSectionModel L V ⊥ a (Representation.specialLinearNatural (k := ZMod 2) 3))
    (htop : HasSectionModel L Q D a
      ((Representation.specialLinearNatural (k := ZMod 2) 3).prod (Representation.specialLinearNatural 3)))
    (hphi : HasSectionModel L Phi ZQ a (Representation.specialLinearNatural (k := ZMod 2) 3).dual)
    (hTQ : ⁅U,L⁆ ≤ Q) (hTD : ⁅U,L⁆ ⊓ D ≤ Phi) (hZV : ⁅ZQ,L⁆ ≤ V)
    (s : L) (hs7 : s^7=1)
    (hnat : BinarySingerPrimary.projector ((Representation.specialLinearNatural (k := ZMod 2) 3) (a s))=0) :
    Module.finrank (ZMod 2) (BinarySingerPrimary.projector (ρ s)).range ≤ 3 := by
  let e := BinarySingerPrimary.projector (ρ s)
  have hid : e*e=e := BinarySingerPrimary.projector_idempotent (ρ s) (by rw [←map_pow,hs7,map_one])
  have hdouble : BinarySingerPrimary.projector
      (((Representation.specialLinearNatural (k := ZMod 2) 3).prod (Representation.specialLinearNatural 3)) (a s))=0 := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact LinearMap.congr_fun hnat x.1
    · exact LinearMap.congr_fun hnat x.2
  have hkillV (u : U) (hu : (u:G) ∈ V) : e (p u).toAdd=0 := by
    have hw := word_in_kernel L U V ⊥ hLU a _ hseed s hnat u hu
    have hw1 : word L U hLU s u=1 := Subtype.ext hw
    rw [←word_map L U hLU p ρ hp s u,hw1,map_one]
    rfl
  have hkillZ (u : U) (hu : (u:G) ∈ ZQ) : e (p u).toAdd=0 := by
    obtain ⟨v,hv,he⟩ := (mem_imageSpace _ _ _ _).mp
      (projector_image_commutator L U ZQ hLU p ρ hp s u hu)
    have hh := hkillV v (hZV hv)
    rw [he] at hh
    exact (LinearMap.congr_fun hid (p u).toAdd).symm.trans hh
  let S := U ⊓ Phi
  let f : S →* Multiplicative E := p.comp (inclusion inf_le_left)
  obtain ⟨q,_,hq,_⟩ := marked_coordinates hphi
  let qS := q.comp (inclusion (show S ≤ Phi from inf_le_right))
  have hlift (x : e.range) : ∃ v : S, (f v).toAdd=x.val := by
    obtain ⟨y,hy⟩ := x.property
    obtain ⟨u,hu⟩ := hps (Multiplicative.ofAdd y)
    have hpu : (p u).toAdd=y := congrArg Multiplicative.toAdd hu
    have hi := projector_image_commutator L U U hLU p ρ hp s u u.property
    obtain ⟨v,hv,hev⟩ := (mem_imageSpace _ _ _ _).mp hi
    let w := word L U hLU s v
    have hwT : (w:G) ∈ ⁅U,L⁆ := word_mem L U ⁅U,L⁆ hLU
      (normalizer_commutator_ge_right U L) s v hv
    have hwD : (w:G) ∈ D := word_in_kernel L U Q D hLU a _ htop s hdouble v (hTQ hv)
    refine ⟨⟨w,w.property,hTD ⟨hwT,hwD⟩⟩,?_⟩
    change (p w).toAdd=x.val
    rw [word_map L U hLU p ρ hp,hev]
    change e (e (p u).toAdd)=x.val
    rw [show e (e (p u).toAdd)=e (p u).toAdd from LinearMap.congr_fun hid _,hpu]
    exact hy
  have hkill (v : S) (hv : qS v=1) : e (f v).toAdd=0 := by
    have hqv : inclusion (show S ≤ Phi from inf_le_right) v ∈ q.ker := hv
    rw [hq] at hqv
    exact hkillZ (inclusion inf_le_left v) hqv
  let : Finite (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) :=
    Finite.of_injective (fun f => (f : (Fin 3 → ZMod 2) → ZMod 2)) DFunLike.coe_injective
  have hcard := BinarySingerPrimary.card_range_le_of_section e hid f qS hlift hkill
  have ht : Nat.card (Multiplicative (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)))=8 := by
    change Nat.card (Module.Dual (ZMod 2) (Fin 3 → ZMod 2))=8
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      Subspace.dual_finrank_eq,Module.finrank_fin_fun]
    norm_num
  rw [ht,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hcard


private theorem seed_projector_of_whole_model
    {A : Type*} [Group A]
    (L V W : Subgroup G) [IsElementaryAbelian 2 W] (hVW : V ≤ W)
    (a : L →* A) (ν : Representation (ZMod 2) A (Fin 3 → ZMod 2))
    (hs : HasSectionModel L V ⊥ a ν)
    (σ : Representation (ZMod 2) L (Additive W))
    (hσ : ∀ (l : L) (v : V),
      ((σ l (Additive.ofMul (inclusion hVW v))).toMul : G)=l*(v:G)*(l:G)⁻¹)
    (s : L) (hzero : BinarySingerPrimary.projector (σ s)=0) :
    BinarySingerPrimary.projector (ν (a s))=0 := by
  let pW : V →* Multiplicative (Additive W) :=
    MulEquiv.toMultiplicative_toAdditive.symm.toMonoidHom.comp (inclusion hVW)
  have hp (l : L) (v : V) :
      (pW (actor L V hs.2.1 l v)).toAdd=σ l (pW v).toAdd := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (hσ l v).symm
  obtain ⟨p,hps,hpk,hpact⟩ := marked_coordinates hs
  apply LinearMap.ext
  intro x
  obtain ⟨v,hv⟩ := hps (Multiplicative.ofAdd x)
  have hW := word_map L V hs.2.1 pW σ hp s v
  rw [hzero,LinearMap.zero_apply] at hW
  have hw : word L V hs.2.1 s v=1 := by
    apply Subtype.ext
    exact congrArg (fun w : Additive W => (w.toMul : G)) hW
  have hh := word_map L V hs.2.1 p (ν.comp a) hpact s v
  rw [hw,map_one] at hh
  change 0=BinarySingerPrimary.projector (ν (a s)) (p v).toAdd at hh
  rw [hv] at hh
  exact hh.symm


variable [Finite G]

theorem binary_three_point_synchronized_singer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLC : c.L ≤ centralizer ({z} : Set G)) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    ∃ (f : c.L →* B) (β : B →* SpecialLinearGroup (Fin 3) (ZMod 2)),
      Function.Surjective f ∧
      (∀ l : c.L, (f l : C ⧸ pCore 2 C)=q ⟨l,hLC l.property⟩) ∧
      Function.Surjective β ∧ β.ker=pCore 2 B ∧
      ∃ s : c.L, (β.comp f) s=BinarySingerPrimary.singer ∧ s^7=1 ∧ orderOf s=7 ∧
      let Q := LinearThree.commutatorCore c.L
      let Phi := frattiniIn Q
      let D := Q ⊓ centralizer (Phi : Set G)
      let a := β.comp f
      let v := Representation.specialLinearNatural (k := ZMod 2) 3
      HasSectionModel c.L (⁅coreCenter c.L,c.L⁆) ⊥ a v ∧
      HasSectionModel c.L Phi (sCenter Q) a v.dual ∧
      HasSectionModel c.L D Phi a (v.dual.prod v.dual) ∧
      HasSectionModel c.L Q D a (v.prod v) := by
  obtain ⟨f,β,hf,hfq,hβ,hβk,hmodels⟩ := binary_three_point_synchronized_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLC
  have hfk : IsPGroup 2 f.ker := by
    let j : f.ker →* pCore 2 (centralizer ({z} : Set G)) := {
      toFun x := ⟨⟨x.val,hLC x.val.property⟩,by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨x.val,hLC x.val.property⟩=1
        rw [←hfq]
        have he := congrArg Subtype.val x.property
        exact he⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    apply pCore_isPGroup.of_injective j
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : pCore 2 (centralizer ({z} : Set G)) => (x : G)) h))
  have hβker : IsPGroup 2 β.ker := hβk ▸ pCore_isPGroup
  have hk : IsPGroup 2 (β.comp f).ker := by
    exact hβker.comap_of_ker_isPGroup f hfk
  obtain ⟨s,hs,hs7,hso⟩ := BinarySingerPrimary.exists_order_seven_lift
    (β.comp f) (hβ.comp hf) hk
  exact ⟨f,β,hf,hfq,hβ,hβk,s,hs,hs7,hso,hmodels⟩

set_option maxHeartbeats 1000000 in
/-- The actual original fixed-four-span quotient has complementary Singer
primary dimension at most three. The order-seven lift has the literal
endpoint image under the same marking supplied by the natural-four model. -/
theorem binary_three_source_fixed_span_spectral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2)
    (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let j : c.L →* C := inclusion (le_sup_left.trans hLS)
    let B := (c.L.subgroupOf C).map q
    let U := conjugateSpanBy (intrinsicFour c.L) C
    let Z := zpowers z
    ∃ eK : K ≃* SL(4,ZMod 2),
      (B.subgroupOf K).map eK.toMonoidHom=BinaryEndpointInduction.endpointParabolic ∧
      ∃ (s : c.L) (k : K), s^7=1 ∧ orderOf s=7 ∧
        (k : C ⧸ pCore 2 C)=q (j s) ∧
        eK k=BinarySingerPrimary.endpointSinger ∧
        ∀ hZ : (Z.subgroupOf U).Normal,
          let := hZ
          ∀ hel : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
            let := hel
            ∀ ρ : (C ⧸ pCore 2 C) →* MulAut (U ⧸ Z.subgroupOf U),
              (∀ (x : C) (u v : U), (v : G)=x*(u : G)*(x : G)⁻¹ →
                ρ (q x) (QuotientGroup.mk' (Z.subgroupOf U) u)=
                  QuotientGroup.mk' (Z.subgroupOf U) v) →
              Module.finrank (ZMod 2)
                (BinarySingerPrimary.projector (M := Additive (U ⧸ Z.subgroupOf U))
                  (elementaryRepresentation (p := 2) ρ k.val)).range ≤ 3 ∧
              Module.finrank (ZMod 2) (LinearMap.ker
                (BinarySingerPrimary.cubic (M := Additive (U ⧸ Z.subgroupOf U))
                  (elementaryRepresentation (p := 2) ρ (k.val⁻¹)))) ≤ 3 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let Z := zpowers z
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  obtain ⟨hW,hmodel⟩ := binary_three_source_four_natural_model
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  let := hW
  obtain ⟨σ,hσ,hinj,hker,eK,heK,E,hE⟩ := hmodel
  obtain ⟨f,β,hfs,hfq,hβ,hβk,hseed,hphi,hmid,htop⟩ := binary_three_point_synchronized_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLC
  have hfk : IsPGroup 2 f.ker := by
    let j : f.ker →* pCore 2 C := {
      toFun x := ⟨⟨x.val,hLC x.val.property⟩,by
        apply (QuotientGroup.eq_one_iff _).mp
        change q ⟨x.val,hLC x.val.property⟩=1
        rw [←hfq]
        exact congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    apply pCore_isPGroup.of_injective j
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : pCore 2 C => (x : G)) h))
  let eB : B ≃* BinaryEndpointInduction.endpointParabolic :=
    (subgroupOfEquivOfLe hBK).symm.trans
      ((eK.subgroupMap (B.subgroupOf K)).trans (MulEquiv.subgroupCongr heK))
  have hsmem : BinarySingerPrimary.endpointSinger ∈ BinaryEndpointInduction.endpointParabolic := by
    intro j
    fin_cases j <;> rfl
  let y : B := eB.symm ⟨BinarySingerPrimary.endpointSinger,hsmem⟩
  have hyP : (⟨BinarySingerPrimary.endpointSinger,hsmem⟩ : BinaryEndpointInduction.endpointParabolic)^7=1 :=
    Subtype.ext BinarySingerPrimary.endpointSinger_pow
  have hy7 : y^7=1 := by
    change (eB.symm ⟨BinarySingerPrimary.endpointSinger,hsmem⟩)^7=1
    rw [←map_pow,hyP,map_one]
  have hy1 : y≠1 := by
    intro h
    have he : (⟨BinarySingerPrimary.endpointSinger,hsmem⟩ : BinaryEndpointInduction.endpointParabolic)=1 :=
      eB.symm.injective (h.trans (map_one eB.symm).symm)
    exact BinarySingerPrimary.endpointSinger_ne_one (congrArg Subtype.val he)
  obtain ⟨s,hs,hs7,hso⟩ := BinarySingerPrimary.exists_seven_lift f hfs hfk y hy7 hy1
  let k : K := ⟨(f s).val,hBK (f s).property⟩
  have hk : (k : C ⧸ pCore 2 C)=q ⟨s,hLC s.property⟩ := hfq s
  have hks : eK k=BinarySingerPrimary.endpointSinger := by
    have hy : eB y=⟨BinarySingerPrimary.endpointSinger,hsmem⟩ := eB.apply_symm_apply _
    have hh := (congrArg eB hs).trans hy
    exact congrArg Subtype.val hh
  let σL := σ.comp (q.comp (inclusion hLC))
  have hzero : BinarySingerPrimary.projector (σL s)=0 := by
    have hEs (w : Additive W) :
        E (σL s w)=(Representation.specialLinearNatural (k := ZMod 2) 4
          BinarySingerPrimary.endpointSinger) (E w) := by
      change E (σ (q ⟨s,hLC s.property⟩) w)=_
      rw [←hk,hE,hks]
      simp only [BinaryEndpointInduction.survivorModelMatrix,inv_inv]
      exact (Matrix.mulVec_transpose _ _).symm
    apply LinearMap.ext
    intro w
    apply E.injective
    have hh := BinarySingerPrimary.projector_intertwine E.toLinearMap (σL s)
      (Representation.specialLinearNatural (k := ZMod 2) 4 BinarySingerPrimary.endpointSinger) hEs w
    rw [BinarySingerPrimary.endpointSinger_projector_natural,LinearMap.zero_apply] at hh
    exact hh.trans E.map_zero.symm
  have hnat := seed_projector_of_whole_model c.L V W (le_conjugateSpanBy V C)
    (β.comp f) (Representation.specialLinearNatural (k := ZMod 2) 3) hseed σL
    (fun l v => hσ ⟨l,hLC l.property⟩ (Additive.ofMul (inclusion (le_conjugateSpanBy V C) v))) s hzero
  obtain ⟨_,hT,hTD⟩ := binary_three_source_fixed_span_middle_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  refine ⟨eK,heK,s,k,hs7,hso,hk,hks,?_⟩
  intro hZ
  let := hZ
  dsimp only
  intro hel
  let := hel
  intro ρ hρ
  let p : U →* Multiplicative (Additive (U ⧸ Z.subgroupOf U)) :=
    MulEquiv.toMultiplicative_toAdditive.symm.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf U))
  have hps : Function.Surjective p := MulEquiv.toMultiplicative_toAdditive.symm.surjective.comp
    (QuotientGroup.mk'_surjective _)
  let ρL := (elementaryRepresentation (p := 2) ρ).comp (q.comp (inclusion hLC))
  have hLU : c.L ≤ normalizer U := hLC.trans (le_normalizer_conjugateSpanBy _ _)
  have hp (l : c.L) (u : U) : (p (actor c.L U hLU l u)).toAdd=ρL l (p u).toAdd := by
    apply Additive.toMul.injective
    exact (hρ ⟨l,hLC l.property⟩ u (actor c.L U hLU l u) rfl).symm
  have hh := bound_from_original_sections c.L U (LinearThree.commutatorCore c.L)
    (LinearThree.commutatorCore c.L ⊓ centralizer (frattiniIn (LinearThree.commutatorCore c.L) : Set G))
    (frattiniIn (LinearThree.commutatorCore c.L)) (coreCenter c.L) V hLU p hps ρL hp
    (β.comp f) hseed htop hphi (hT.trans inf_le_left) hTD le_rfl s hs7 hnat
  change Module.finrank (ZMod 2) (BinarySingerPrimary.projector
    (elementaryRepresentation (p := 2) ρ (q ⟨s,hLC s.property⟩))).range ≤ 3 at hh
  rw [←hk] at hh
  refine ⟨hh,?_⟩
  have hi := (Submodule.finrank_mono
    (BinarySingerPrimary.inverse_cubic_kernel_le_projector_range
      (elementaryRepresentation (p := 2) ρ) k.val)).trans hh
  exact hi

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
