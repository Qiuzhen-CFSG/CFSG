module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CoreComplement
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedCoreInvolutions
public import Theory.GroupTheory.Gaschutz
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups.Defs

/-!
# Todd splitting from the original invariant core preimage

The only additional local premise is an elementary order-128 subgroup P
of the original Q, preserved by the constructed hexad subgroup J, whose
intersection with Q intersect E is exactly the marker line. CoreComplement
constructs U=[P,X] of order 64; J U then complements E in the original
point-plane overlap. The full cocode normalizer has overlap index 1771,
so Gaschütz supplies a global complement.

The resulting isomorphism uses the literal Todd semidirect product and
retains both the original cocode inclusion and the original M24 quotient.
No splitting or local geometry is inferred from the module marking alone.
Existence of P remains to be proved in the source James module; the original
Mathieu application exposes exactly this remaining premise.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.8), printed pp.598--599, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
noncomputable section
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A complement to the original marked cocode kernel gives the literal Todd
semidirect product, with its original kernel and quotient markings. -/
theorem marked_cocode_todd_of_complement
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (hs : ∃ K : Subgroup (normalizer (W : Set G)), f.ker.IsComplement' K) :
    ∃ t : ToddGroup ≃* normalizer (W : Set G),
      (∀ x, f (t x)=x.right) ∧
      (∀ w : W, (t (SemidirectProduct.inl (Multiplicative.ofAdd (E (Additive.ofMul w))))).val=w.val) := by
  obtain ⟨K,hK⟩ := hs
  let M := normalizer (W : Set G)
  let B := f.ker
  let ec : B ≃* W := (MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe W.le_normalizer)
  let ev : B ≃* ToddVector := ec.trans E.toAddEquiv.toMultiplicative
  let r := f.comp K.subtype
  have hr : Function.Bijective r := by
    constructor
    · apply (MonoidHom.ker_eq_bot_iff r).mp
      apply le_bot_iff.mp
      intro x hx
      exact Subtype.ext (disjoint_def.mp hK.disjoint hx x.property)
    · intro u
      obtain ⟨g,hg⟩ := hf u
      obtain ⟨⟨b,k⟩,he⟩ := hK.2 g
      refine ⟨k,?_⟩
      change f k.val=u
      have hb : f b.val=1 := b.property
      rw [←hg,←he,map_mul,hb,one_mul]
  let er : K ≃* M24 := MulEquiv.ofBijective r hr
  let phi := B.normalizerMonoidHom.comp (inclusion (B.normalizer_eq_top ▸ le_top : K ≤ normalizer (B : Set M)))
  let d : B ⋊[phi] K ≃* ToddGroup := SemidirectProduct.congr ev er (by
    intro k
    apply MulEquiv.ext
    intro b
    apply Multiplicative.toAdd.injective
    change E (Additive.ofMul (ec (phi k b))) = cocodeRepresentation (f k.val) (E (Additive.ofMul (ec b)))
    have hec : ec (phi k b)=W.normalizerMonoidHom k.val (ec b) := by
      apply Subtype.ext
      rfl
    rw [hec,hE])
  let m : B ⋊[phi] K ≃* M := SemidirectProduct.mulEquivSubgroup hK
  let t : ToddGroup ≃* M := d.symm.trans m
  refine ⟨t,?_,?_⟩
  · intro x
    obtain ⟨y,rfl⟩ := d.surjective x
    change f (m (d.symm (d y)))=(d y).right
    rw [d.symm_apply_apply]
    change f (y.left.val*y.right.val)=er y.right
    rw [map_mul,show f y.left.val=1 from y.left.property,one_mul]
    rfl
  · intro w
    let b := ec.symm w
    have hev : ev b=Multiplicative.ofAdd (E (Additive.ofMul w)) := by
      change Multiplicative.ofAdd (E (Additive.ofMul (ec (ec.symm w))))=_
      rw [ec.apply_symm_apply]
    have hd : d (SemidirectProduct.inl b)=SemidirectProduct.inl (ev b) := by
      apply SemidirectProduct.ext
      · rfl
      · exact map_one er
    rw [←hev,←hd]
    change (m (d.symm (d (SemidirectProduct.inl b)))).val=w.val
    rw [d.symm_apply_apply]
    change (b.val*1).val=w.val
    rw [mul_one]
    exact congrArg Subtype.val (ec.apply_symm_apply w)

/-- Gaschütz transfers splitting in the literal sextet overlap to the whole
original cocode normalizer. The overlap has odd index 1771. -/
theorem marked_cocode_split_of_plane_split
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z)=sextetVector S)
    (hs : ∃ K : Subgroup ((Subgroup.centralizer ({(z : G)} : Set G)).subgroupOf (normalizer (W : Set G))),
      (f.ker.subgroupOf ((Subgroup.centralizer ({(z : G)} : Set G)).subgroupOf (normalizer (W : Set G)))).IsComplement' K) :
    ∃ t : ToddGroup ≃* normalizer (W : Set G),
      (∀ x, f (t x)=x.right) ∧
      (∀ w : W, (t (SemidirectProduct.inl (Multiplicative.ofAdd (E (Additive.ofMul w))))).val=w.val) := by
  let M := normalizer (W : Set G)
  let H := (Subgroup.centralizer ({(z : G)} : Set G)).subgroupOf M
  have hWH : f.ker ≤ H := by
    rw [hk]
    intro w hw
    exact mem_centralizer_singleton_iff.mpr
      (((Commute.all (⟨w.val,hw⟩ : W) z).map W.subtype).eq)
  have hWc : Nat.card W=2048 := by
    change Nat.card (Additive W)=_
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  have hkc : Nat.card f.ker=2048 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe W.le_normalizer).toEquiv,hWc]
  have hHc : Nat.card H=283115520 := by
    have he : (M ⊓ Subgroup.centralizer ({(z : G)} : Set G)).subgroupOf M=H := by
      rw [inf_subgroupOf_left]
    rw [←he,Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact marked_cocode_plane_card W f hf hk hWc E hE z S hz
  have hMc : Nat.card M=501397585920 := by
    have hc := f.ker.card_mul_index
    rw [hkc,index_ker,MonoidHom.range_eq_top.mpr hf,card_top,m24_order] at hc
    exact hc.symm
  have hi : H.index=1771 := by
    have hc := H.card_mul_index
    rw [hHc,hMc] at hc
    omega
  let ec := (MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe W.le_normalizer)
  let : IsElementaryAbelian 2 f.ker := IsElementaryAbelian.of_injective ec.toMonoidHom ec.injective
  obtain ⟨K,hK⟩ := exists_complement_of_coprime_overgroup f.ker H hWH
    (by rw [hkc,hi]; decide) hs
  exact marked_cocode_todd_of_complement W f hf hk E hE ⟨K,hK⟩

/-- The literal invariant-preimage premise suffices for Todd splitting. All
orders, kernel intersections, and the odd overlap index are discharged here. -/
theorem marked_cocode_todd_of_invariant_preimage
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z)=sextetVector S)
    (h : IsTypeJ4 (z : G))
    (e : CubicAutomorphismQuotient (centralizer (z : G) ⧸ core (z : G)))
    (X : Sylow 3 (CubicLift.subgroup e))
    (J P : Subgroup (centralizer (z : G))) [IsElementaryAbelian 2 P]
    (hJc : Nat.card J=2160) (hXJ : cubicSylowImage e X ≤ J)
    (hJN : J ≤ fullCubicNormalizer e X)
    (hJM : J ≤ (normalizer (W : Set G)).subgroupOf (centralizer (z : G)))
    (hdis : Disjoint (W.subgroupOf (centralizer (z : G)) ⊔ core (z : G)) J)
    (hPQ : P ≤ core (z : G)) (hPc : Nat.card P=128)
    (hEP : (W.subgroupOf (centralizer (z : G)) ⊓ core (z : G)) ⊓ P =
      center (centralizer (z : G)))
    (hJP : J ≤ normalizer (P : Set (centralizer (z : G)))) :
    ∃ t : ToddGroup ≃* normalizer (W : Set G),
      (∀ x, f (t x)=x.right) ∧
      (∀ w : W, (t (SemidirectProduct.inl (Multiplicative.ofAdd (E (Additive.ofMul w))))).val=w.val) := by
  let M := normalizer (W : Set G)
  let C := centralizer (z : G)
  let W0 := W.subgroupOf C
  let H0 := M.subgroupOf C
  let H := C.subgroupOf M
  have hWC : W ≤ C := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (((Commute.all (⟨w,hw⟩ : W) z).map W.subtype).eq)
  have hWc : Nat.card W=2048 := by
    change Nat.card (Additive W)=_
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  have hW0c : Nat.card W0=2048 := (Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv).trans hWc
  obtain ⟨hle,_,hkc,_⟩ := marked_cocode_core_image_and_lifts W f hf hk E hE z S hz h e
  let q := f.comp (coreNormalizerInclusion W hle)
  have hker : q.ker=(W0 ⊓ core (z : G)).subgroupOf (core (z : G)) := by
    ext x
    change f (coreNormalizerInclusion W hle x)=1 ↔ x.val ∈ W0 ⊓ core (z : G)
    rw [←MonoidHom.mem_ker,hk]
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hE1c : Nat.card (W0 ⊓ core (z : G) : Subgroup C)=128 := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv] at hkc
    exact hkc
  let U := ⁅P,cubicSylowImage e X⁆
  obtain ⟨hUQ,_,hUc,hJU,hEU,_,_⟩ := core_invariant_complement_of_elementary_preimage
    h e X (W0 ⊓ core (z : G)) P J inf_le_right hE1c hPQ hPc hEP hXJ hJN hJP
  have hH0c : Nat.card H0=283115520 := by
    have he : (M ⊓ C).subgroupOf C=H0 := inf_subgroupOf_right M C
    rw [←he,Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact marked_cocode_plane_card W f hf hk hWc E hE z S hz
  have hW0H : W0 ≤ H0 := by
    intro w hw
    exact W.le_normalizer hw
  have hc := overlap_complement_of_core_complement W0 (core (z : G)) U J H0
    hW0H hle hJM hUQ hJU hW0c hUc hJc hH0c hdis hEU
  let r : H0 ≃* H := {
    toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let K := ((U ⊔ J).subgroupOf H0).map r.toMonoidHom
  have hbase : (W0.subgroupOf H0).map r.toMonoidHom = f.ker.subgroupOf H := by
    ext x
    rw [hk]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨r.symm x,hx,r.apply_symm_apply x⟩
  apply marked_cocode_split_of_plane_split W f hf hk E hE z S hz
  refine ⟨K,isComplement'_of_card_mul_and_disjoint ?_ ?_⟩
  · rw [←hbase,card_map_of_injective r.injective,card_map_of_injective r.injective,
      hc.card_mul_card,Nat.card_congr r.toEquiv]
  · rw [←hbase]
    apply disjoint_def.mpr
    rintro x ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
    have hba : b=a := r.injective he
    rw [hba] at hb
    rw [disjoint_def.mp hc.disjoint ha hb,map_one]

end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
