module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanSpectral
public import Theory.Representation.BinarySingerCubic

/-!
# The original natural cubic at the exact endpoint Singer

The endpoint marking, original order-seven lift, and all four synchronized
sections remain in one packet. The actual natural-four model selects the
natural cubic on Q/D; no identification of unrelated markings is assumed.
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

set_option maxHeartbeats 1000000 in
/-- The same original endpoint Singer annihilates the marked natural and doubled-natural sections by X³+X+1. -/
theorem binary_three_source_endpoint_synchronized_cubic
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
    ∃ (f : c.L →* B) (β : B →* SL(3,ZMod 2)),
      Function.Surjective f ∧ (∀ l : c.L, (f l : C ⧸ pCore 2 C)=q (j l)) ∧
      Function.Surjective β ∧ β.ker=pCore 2 B ∧
      ∃ eK : K ≃* SL(4,ZMod 2),
        (B.subgroupOf K).map eK.toMonoidHom=BinaryEndpointInduction.endpointParabolic ∧
        ∃ (s : c.L) (k : K), s^7=1 ∧ orderOf s=7 ∧
          (k : C ⧸ pCore 2 C)=q (j s) ∧ eK k=BinarySingerPrimary.endpointSinger ∧
          let Q := LinearThree.commutatorCore c.L
          let Phi := frattiniIn Q
          let D := Q ⊓ centralizer (Phi : Set G)
          let a := β.comp f
          let v := Representation.specialLinearNatural (k := ZMod 2) 3
          HasSectionModel c.L (⁅coreCenter c.L,c.L⁆) ⊥ a v ∧
          HasSectionModel c.L Phi (sCenter Q) a v.dual ∧
          HasSectionModel c.L D Phi a (v.dual.prod v.dual) ∧
          HasSectionModel c.L Q D a (v.prod v) ∧
          (a s).val^3+(a s).val+1=0 ∧
          BinarySingerPrimary.cubic (v (a s))=0 ∧
          BinarySingerPrimary.cubic ((v.prod v) (a s))=0 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
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
  let a := β.comp f
  let v := Representation.specialLinearNatural (k := ZMod 2) 3
  have ha7 : (a s)^7=1 := by rw [←map_pow,hs7,map_one]
  have hk2 : IsPGroup 2 a.ker :=
    (show IsPGroup 2 β.ker from hβk ▸ pCore_isPGroup).comap_of_ker_isPGroup f hfk
  have ha1 : a s≠1 := by
    intro h
    let x : a.ker := ⟨s,h⟩
    have hx : orderOf x=7 := (Subgroup.orderOf_coe x).symm.trans hso
    have hh := hk2.orderOf_coprime (by decide : Nat.Coprime 2 7) x
    rw [hx] at hh
    norm_num at hh
  let φ : Matrix (Fin 3) (Fin 3) (ZMod 2) ≃ₐ[ZMod 2]
      Module.End (ZMod 2) (Fin 3 → ZMod 2) := Matrix.toLinAlgEquiv'
  have hφ : φ (a s).val=v (a s) := by ext x i; rfl
  have hp : 1+(a s).val^3+(a s).val^5+(a s).val^6=0 := by
    apply φ.injective
    simp only [map_add,map_pow,map_one,map_zero,hφ]
    exact hnat
  have hm7 : (a s).val^7=1 := by
    exact congrArg (SpecialLinearGroup.coeMonoidHom : SL(3,ZMod 2) →* Matrix (Fin 3) (Fin 3) (ZMod 2)) ha7
  have hm1 : (a s).val≠1 := fun h => ha1 (Subtype.ext h)
  have hmatrix := BinarySingerCubic.cubic_eq_zero_of_seven_projector (a s).val hm7 hm1 hp
  have hnatural : BinarySingerPrimary.cubic (v (a s))=0 := by
    have hh := congrArg φ hmatrix
    simpa only [map_add,map_pow,map_one,map_zero,hφ,BinarySingerPrimary.cubic] using hh
  have hdouble : BinarySingerPrimary.cubic ((v.prod v) (a s))=0 := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact LinearMap.congr_fun hnatural x.1
    · exact LinearMap.congr_fun hnatural x.2
  exact ⟨f,β,hfs,hfq,hβ,hβk,eK,heK,s,k,hs7,hso,hk,hks,
    hseed,hphi,hmid,htop,hmatrix,hnatural,hdouble⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
