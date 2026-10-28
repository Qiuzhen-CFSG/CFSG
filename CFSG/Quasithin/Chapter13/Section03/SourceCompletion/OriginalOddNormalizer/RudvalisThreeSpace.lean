module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisAmbientOrder
public import Theory.Representation.G2BinaryPointCoreSpan

/-!
# The original three-space inside the Rudvalis point-core commutator

The two literal point-stabilizer quotients have distinct kernels. Their
order-32 intersection is the invariant natural hyperplane, and the ambient
kernel maps onto the entire natural point-parabolic two-core. Root
displacements therefore put every invariant three-space into the derived
subgroup of the ambient point core.

The second theorem identifies the actual original chosen three-space.
The original Sylow-invariant flag supplies point-normalizer invariance;
faithfulness on the whole module carries it through the original section
conjugation and central quotient. The last theorem applies this to the
escaping odd-actor component, retaining its relative Sylow placement.

Centralization of this core commutator by the escaping quaternion, its
central-cover lift, the J₄ exclusion and the final odd-normalizer argument
remain with qt-d-13316-source. Earlier Structural1222 retains its final
discharge with qt-theorem-d. The result makes no assertion that every
involution of the ambient core is centralized.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612, in the original
4.4.3 and 13.3.16 application, printed pp.623,893--896.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
/-- A point-stabilizer-invariant three-space in the literal original module
lies in the commutator subgroup of the full ambient point core. -/
theorem unitary_original_pushingUp_rudvalis_invariant_three (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let E := ((W.subgroupOf H).subgroupOf K).map f
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    ∀ z : E, z ≠ 1 →
      let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
      ∀ U : Subgroup Rudvalis.Model, U ≤ E → Nat.card U = 8 →
        C ⊓ D ≤ normalizer (U : Set Rudvalis.Model) →
        U ≤ ⁅D.pCoreIn 2,D.pCoreIn 2⁆ := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let E := ((W.subgroupOf H).subgroupOf K).map f
  let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
  obtain ⟨hCE,a,d,ha,hker,_,he⟩ :=
    unitary_original_pushingUp_rudvalis_full_action s hcover hJH hc K hK e c hVW
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective d.symm.toMonoidHom d.symm.surjective
  have hNC : normalizer (E : Set Rudvalis.Model) = C :=
    (unitary_original_pushingUp_rudvalis_exact_sizes s hcover hJH hc K hK e c hVW).1
  have hEC : E ≤ C := E.le_normalizer.trans hNC.le
  dsimp only
  intro z hz
  let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
  let P := D.subgroupOf C
  have hED : E ≤ D := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    exact setLike_mul_comm hu z.property
  have hEP : E.subgroupOf C ≤ P := fun _ hx => hED hx
  have hv : s.coordinates (Additive.ofMul (d z)) ≠ 0 := by
    intro hh
    apply hz
    apply d.injective
    apply Additive.ofMul.injective
    apply s.coordinates.injective
    change s.coordinates (Additive.ofMul (d z)) = s.coordinates (Additive.ofMul (d 1))
    rw [map_one]
    change s.coordinates (Additive.ofMul (d z)) = s.coordinates 0
    rw [map_zero]
    exact hh
  have hP (x : C) : x ∈ P ↔ Atlas.G2.Natural.action (ZMod 2) (a x)
      (s.coordinates (Additive.ofMul (d z))) = s.coordinates (Additive.ofMul (d z)) := by
    rw [←he x z,s.coordinates.injective.eq_iff,Additive.ofMul.injective.eq_iff,d.injective.eq_iff]
    change (x : Rudvalis.Model) ∈ centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model) ↔ _
    rw [mem_centralizer_singleton_iff,Subtype.ext_iff]
    change (x : Rudvalis.Model)*(z : Rudvalis.Model) = (z : Rudvalis.Model)*(x : Rudvalis.Model) ↔
      (x : Rudvalis.Model)*(z : Rudvalis.Model)*(x : Rudvalis.Model)⁻¹ = (z : Rudvalis.Model)
    rw [mul_inv_eq_iff_eq_mul]
  obtain ⟨g,b,hb,hbk,hmark⟩ := Atlas.G2.Natural.BinaryPointFlag.exists_point_parabolic_map
    a ha P (s.coordinates (Additive.ofMul (d z))) hv hP
  rw [hker] at hbk
  have hPcard : Nat.card P = 12288 :=
    (unitary_original_pushingUp_rudvalis_exact_sizes s hcover hJH hc K hK e c hVW).2.2 z hz
  have hbcard : Nat.card b.ker = 64 := by
    have hm := b.ker.card_mul_index
    rw [index_ker,b.range_eq_top_of_surjective hb,card_top,
      Atlas.G2.BinaryCore.secondParabolic_card] at hm
    change Nat.card b.ker * 192 = Nat.card P at hm
    rw [hPcard] at hm
    omega
  obtain ⟨q,hq,hqk,hrk,hrmap,hrcard,_,t,ht,htE,htR,_,hrcomm⟩ :=
    unitary_original_pushingUp_rudvalis_ambient_point_order s hcover hJH hc K hK e c hVW z hz
  let i : P →* D := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let r := q.comp i
  let j := C.subtype.comp P.subtype
  have hj : Function.Injective j := C.subtype_injective.comp P.subtype_injective
  have hbmap : b.ker.map j = E := by
    rw [hbk,←map_map,map_subgroupOf_eq_of_le hEP,map_subgroupOf_eq_of_le hEC]
  have hinter : Nat.card (b.ker ⊓ r.ker : Subgroup P) = 32 := by
    rw [←card_map_of_injective hj,map_inf _ _ _ hj,hbmap,hrmap,
      ←inf_assoc,inf_eq_left.mpr hEC]
    exact unitary_original_pushingUp_rudvalis_module_core_intersection
      s hcover hJH hc K hK e c hVW z hz

  have hrTwo : IsPGroup 2 r.ker := IsPGroup.of_card (n := 10) hrcard
  let k : b.ker →* E := (j.comp b.ker.subtype).codRestrict E
    (fun v => hbk.le v.property)
  have hk : Function.Bijective k := by
    constructor
    · intro u v h
      have hh : j (u : P) = j (v : P) := congrArg (fun v : E => (v : Rudvalis.Model)) h
      exact Subtype.ext (hj hh)
    · intro u
      let up : P := ⟨⟨u,hEC u.property⟩,hED u.property⟩
      exact ⟨⟨up,hbk.ge u.property⟩,rfl⟩
  let kd := (MulEquiv.ofBijective k hk).trans d
  have hkd (x : P) (v : b.ker) :
      s.coordinates (Additive.ofMul (kd ⟨x * v * x⁻¹,
        (inferInstance : b.ker.Normal).conj_mem v v.property x⟩)) =
      Atlas.G2.Natural.action (ZMod 2) (a (x : C))
        (s.coordinates (Additive.ofMul (kd v))) := by
    have hkconj : k ⟨x * v * x⁻¹,
        (inferInstance : b.ker.Normal).conj_mem v v.property x⟩ =
        E.normalizerMonoidHom (inclusion hCE (x : C)) (k v) := by
      apply Subtype.ext
      rfl
    change s.coordinates (Additive.ofMul (d (k _))) = _
    rw [hkconj,he]
    rfl
  intro U hUE hUcard hUn
  let U' := (U.subgroupOf C).subgroupOf P
  have hUP : U.subgroupOf C ≤ P := fun _ hu => hED (hUE hu)
  have hUC := hUE.trans hEC
  let : U'.Normal := ⟨fun u hu x => (mem_normalizer_iff.mp (hUn ⟨x.val.property,x.property⟩) u.val.val).mp hu⟩
  have hUker : U' ≤ b.ker := fun _ hu => hbk.ge (hUE hu)
  have hU'card : Nat.card U' = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv,hUcard]
  have hbound := Atlas.G2.Natural.BinaryPointFlag.invariant_three_le_second_kernel_commutator_of_marking
    b hb kd s.coordinates (a.comp P.subtype) g hmark hkd
    r.ker hrTwo hrcard
      ((congrArg (fun A : Subgroup P => Nat.card A) (inf_comm r.ker b.ker)).trans hinter)
      U' hUker hU'card
  have hm := map_mono (f := j) hbound
  have hUmap : U'.map j = U := by
    rw [←map_map,map_subgroupOf_eq_of_le hUP,map_subgroupOf_eq_of_le hUC]
  rw [hUmap,map_commutator,hrmap] at hm
  exact hm.trans (commutator_mono inf_le_right inf_le_right)


/-- The literal image of the original Sylow-invariant three-space lies in
 the derived subgroup of the ambient point core. No ambient-Sylow placement
 is assumed. -/
theorem unitary_original_pushingUp_rudvalis_original_three
    (s : Context T L V)
    (Z B U : Subgroup G) (hZV : Z ≤ V) (hBV : B ≤ V) (hUV : U ≤ V)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hB : Nat.card B = 4) (hU : Nat.card U = 8)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let Zc := Z.map (MulAut.conj (c : G)).toMonoidHom
    let Uc := U.map (MulAut.conj (c : G)).toMonoidHom
    let Zbar := ((Zc.subgroupOf H).subgroupOf K).map f
    let Ubar := ((Uc.subgroupOf H).subgroupOf K).map f
    ∀ z ∈ Zbar, z ≠ 1 →
      Ubar ≤ ⁅(centralizer ({z} : Set Rudvalis.Model)).pCoreIn 2,
        (centralizer ({z} : Set Rudvalis.Model)).pCoreIn 2⁆ := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let g := MulAut.conj (c : G)
  let j := H.subtype.comp K.subtype
  let W0 := (W.subgroupOf H).subgroupOf K
  let E := W0.map f
  let C0 := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
  let C := C0.map f
  let lift (A : Subgroup G) := ((A.map g.toMonoidHom).subgroupOf H).subgroupOf K
  let image (A : Subgroup G) := (lift A).map f
  have hfull := unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hVW
  change W = V.map g.toMonoidHom at hfull
  have hWH : W ≤ H := (hc.module_le_center_radical.trans (map_subtype_le _)).trans
    (hc.radical_le.trans hc.local_le)
  have hWK : W.subgroupOf H ≤ K := (hc.ordinary_module_placement K hK).1.trans inf_le_right
  have hAM (A : Subgroup G) (hAV : A ≤ V) : A.map g.toMonoidHom ≤ W := by
    rw [hfull]
    exact map_mono hAV
  have hAlift (A : Subgroup G) (hAV : A ≤ V) : lift A ≤ W0 :=
    subgroupOf_mono K (subgroupOf_mono H (hAM A hAV))
  have hmap (A : Subgroup G) (hAV : A ≤ V) : (lift A).map j = A.map g.toMonoidHom := by
    have hAH := (hAM A hAV).trans hWH
    have hAK := (subgroupOf_mono H (hAM A hAV)).trans hWK
    rw [←map_map,map_subgroupOf_eq_of_le hAK,map_subgroupOf_eq_of_le hAH]
  have hf : Function.Injective (f.comp W0.subtype) := by
    have hi := (unitary_original_pushingUp_chosen_injective s hcover hJH hc K hK c hVW).1
    rw [←hfull] at hi
    exact e.injective.comp hi
  have himage (A : Subgroup G) (hAV : A ≤ V) : Nat.card (image A) = Nat.card A := by
    have hi : Function.Injective (f.subgroupMap (lift A)) := by
      intro x y he
      have hh : (⟨x,hAlift A hAV x.property⟩ : W0) = ⟨y,hAlift A hAV y.property⟩ :=
        hf (congrArg Subtype.val he)
      exact Subtype.ext (congrArg (fun u : W0 => (u : K)) hh)
    rw [←Nat.card_congr (MulEquiv.ofBijective (f.subgroupMap (lift A))
      ⟨hi,f.subgroupMap_surjective (lift A)⟩).toEquiv]
    have hcj : Nat.card ((lift A).map j) = Nat.card (lift A) :=
      card_map_of_injective (H.subtype_injective.comp K.subtype_injective)
    rw [←hcj,hmap A hAV,card_map_of_injective g.injective]
  have hCE : C0 ≤ normalizer (W0 : Set K) :=
    (unitary_original_pushingUp_rudvalis_normalizer_lift s hcover hJH hc K hK e c hVW).1.ge
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  obtain ⟨rho,coords,he,_,_,hz,_,hu⟩ := exists_unitary_flag_marking T L Z B U
    s.chosen.normalizes hNL s.actor s.coordinates s.equivariant hTN
    hZV hBV hUV hTZ hTB hTU hZ hB hU
  have hNU : normalizer (V : Set G) ⊓ centralizer (Z : Set G) ≤ normalizer (U : Set G) :=
    point_centralizer_normalizes_marked_seed U Z _ rho coords he hu hz hUV inf_le_left inf_le_right
  change ∀ z ∈ image Z, z ≠ 1 → image U ≤ _
  intro z hzbar hzne
  have hZE : image Z ≤ E := map_mono (hAlift Z hZV)
  have hUE : image U ≤ E := map_mono (hAlift U hUV)
  have hZcard : Nat.card (image Z) = 2 := (himage Z hZV).trans hZ
  have hZcyclic : image Z ≤ zpowers z := by
    intro w hw
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp (mem_zpowers_of_prime_card hZcard
      (show (⟨z,hzbar⟩ : image Z) ≠ 1 from fun h => hzne (congrArg Subtype.val h))
      (g' := ⟨w,hw⟩))
    exact mem_zpowers_iff.mpr ⟨n,congrArg Subtype.val hn⟩
  apply unitary_original_pushingUp_rudvalis_invariant_three s hcover hJH hc K hK e c hVW
    ⟨z,hZE hzbar⟩ (fun h => hzne (congrArg Subtype.val h)) (image U) hUE
    ((himage U hUV).trans hU)
  intro x hx
  obtain ⟨k,hk,hkx⟩ := hx.1
  have hkW : k ∈ normalizer (W0 : Set K) := hCE hk
  have hkWg : j k ∈ normalizer (W : Set G) := by
    have hh := W0.le_normalizer_map j (mem_map_of_mem j hkW)
    have hwmap : W0.map j = W := by
      rw [←map_map,map_subgroupOf_eq_of_le hWK,map_subgroupOf_eq_of_le hWH]
    rwa [hwmap] at hh
  let n := g.symm (j k)
  have hnV : n ∈ normalizer (V : Set G) := by
    rw [hfull,←map_equiv_normalizer_eq] at hkWg
    obtain ⟨v,hv,hve⟩ := hkWg
    have heq : v = n := by
      apply g.injective
      rw [g.apply_symm_apply]
      exact hve
    exact heq ▸ hv
  have hnZ : n ∈ centralizer (Z : Set G) := by
    intro w hw
    obtain ⟨w',hw',hwe⟩ := (hmap Z hZV).symm ▸ (mem_map_of_mem g.toMonoidHom hw)
    have hwW := hAlift Z hZV hw'
    have hxf : f k ∈ centralizer (zpowers z : Set Rudvalis.Model) := by
      rw [zpowers_eq_closure,centralizer_closure]
      exact hkx.symm ▸ hx.2
    have heq : f (k*w'*k⁻¹) = f w' := by
      simp only [map_mul,map_inv]
      rw [←mem_centralizer_iff.mp hxf (f w') (hZcyclic (mem_map_of_mem f hw')),
        mul_inv_cancel_right]
    have hcomm : k*w'*k⁻¹ = w' := congrArg Subtype.val
      (hf (a₁ := ⟨k*w'*k⁻¹,(mem_normalizer_iff.mp hkW w').mp hwW⟩) (a₂ := ⟨w',hwW⟩) heq)
    have hconj := congrArg (fun u : K => g.symm (j u)) hcomm
    simp only [map_mul,map_inv,hwe,MulEquiv.coe_toMonoidHom,g.symm_apply_apply] at hconj
    change w*n = n*w
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  have hnU := hNU ⟨hnV,hnZ⟩
  have hkUg : j k ∈ normalizer (U.map g.toMonoidHom : Set G) := by
    have hh := U.le_normalizer_map g.toMonoidHom (mem_map_of_mem g.toMonoidHom hnU)
    simpa only [n,MulEquiv.coe_toMonoidHom,g.apply_symm_apply] using hh
  have hkU : k ∈ normalizer (lift U : Set K) := by
    apply mem_normalizer_iff.mpr
    intro u
    exact mem_normalizer_iff.mp hkUg (j u)
  exact hkx ▸ (lift U).le_normalizer_map f (mem_map_of_mem f hkU)

/-- The original odd-actor application, with its unchanged relative Sylow placement. -/
theorem unitary_original_oddActorResidual_original_three (s : Context T L V)
    (Z B U : Subgroup G) (hZV : Z ≤ V) (hBV : B ≤ V) (hUV : U ≤ V)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hB : Nat.card B = 4) (hU : Nat.card U = 8)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
      (c : sectionCentralizerIn (normalizer (L : Set G)) L),
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let W := fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        Y (J.pCoreIn 2) W ∧
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
        (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W ∧
      ∃ K : Subgroup H, IsComponent H K ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          ∃ e : K ⧸ center K ≃* Rudvalis.Model,
            W = V.map (MulAut.conj (c : G)).toMonoidHom ∧
            let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
            let Zc := Z.map (MulAut.conj (c : G)).toMonoidHom
            let Uc := U.map (MulAut.conj (c : G)).toMonoidHom
            let Zbar := ((Zc.subgroupOf H).subgroupOf K).map f
            let Ubar := ((Uc.subgroupOf H).subgroupOf K).map f
            ∀ z ∈ Zbar, z ≠ 1 →
              Ubar ≤ ⁅(centralizer ({z} : Set Rudvalis.Model)).pCoreIn 2,
                (centralizer ({z} : Set Rudvalis.Model)).pCoreIn 2⁆) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,_,_,⟨K,hK,hout,n,hn,⟨e⟩⟩,c,hcS,hcV⟩ :=
    unitary_original_oddActorResidual_escaping_component s A hAN hcomm hodd hAV hnot
  refine ⟨J,H,S,c,hpush,hH,hJH,hlt,hc,hcS,hcV,K,hK,hout,?_⟩
  rcases hn with rfl | rfl
  · exact Or.inl ⟨e⟩
  · apply Or.inr
    have hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G) := by
      have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
      obtain ⟨hcover,_,_,_⟩ := chosen_oddActorResidual_cover h12.toHypothesis1221 s.chosen
        A hAN hcomm hodd hAV
      have hi : oddActorResidual L A ≤ J :=
        ((le_inf le_rfl ((oddActorResidual_le L A).trans inf_le_left)).trans hpush.2).trans
          inf_le_left
      exact hcover.subset.trans (Set.mul_subset_mul hi Set.Subset.rfl)
    exact ⟨e,unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hcV,
      unitary_original_pushingUp_rudvalis_original_three s Z B U hZV hBV hUV hTZ hTB hTU
        hZ hB hU hcover hJH hc K hK e c hcV⟩


end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
