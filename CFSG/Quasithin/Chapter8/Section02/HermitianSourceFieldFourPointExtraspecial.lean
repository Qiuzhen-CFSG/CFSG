module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointLocalCore
public import Theory.GroupTheory.TransvectionFixedCoset
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.DihedralCentralProductFourSix

/-!
# The full core intersection and extraspecial Hermitian point closure

The full point parabolic is perfect after lifting: its residual contains the
original two-core kernel and has the whole parabolic image. Hence it contains
a Sylow subgroup of L. The full transvection pairing corrects a vector fixed
modulo the central line to one fixed by the point radical. Perfectness then
makes it fixed by L_z, and Sylow averaging places it in V. This proves the
fixed-subgroup bound on the entire O₂(LT), with its full original kernel.

Source: Aschbacher–Smith 8.2.12, printed p.722, refs/quasithin.pdf. This
supplies the core-intersection step directly from the pairing in 8.2.11(4).
The same full pairing gives both seed centralizers, identifies the closure's
center, computes its order 512, and recognizes the concrete central product
of four D₈'s. The original closure and both full kernels are retained.
The Chapter 12 tensor application discharges all these local inputs.
The remaining equality EV = O₂(L_z), 8.2.13, and zero weak closure are
separate obligations for the full source exclusion.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- The whole original point centralizer equals its perfect residual once the
original two-core kernel has been placed in that residual. -/
theorem point_residual_eq_centralizer
    (L : Subgroup G) (z : G)
    (f : L →* Matrix.PSL3Four.PSL) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 L)
    (hP : Matrix.PSL3Four.ElementaryParabolic.liftedParabolic f true =
      (centralizer ({z} : Set G)).subgroupOf L)
    (hKR : L.pCoreIn 2 ≤ Centralizer.localResidual L z) :
    Centralizer.localResidual L z = L ⊓ centralizer ({z} : Set G) := by
  apply le_antisymm (Centralizer.localResidual_le L z)
  intro x hx
  have hxP : f ⟨x,hx.1⟩ ∈ Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F true :=
    hP.ge hx.2
  rw [←(point_residual_images L z f hf (hk ▸ pCore_isPGroup) hP).1] at hxP
  obtain ⟨y,hy,he⟩ := hxP
  have hxy : (⟨x,hx.1⟩ : L)*y⁻¹ ∈ pCore 2 L := by
    rw [←hk]
    change f ((⟨x,hx.1⟩ : L)*y⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hm := (Centralizer.localResidual L z).mul_mem
    (hKR (mem_map_of_mem L.subtype hxy)) hy
  change (x*(y : G)⁻¹)*(y : G) ∈ _ at hm
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm

/-- Fixed points modulo the central line in the full LT core already lie
in the original module. No indecomposable-extension premise is added. -/
theorem point_full_core_second_fixed
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G) (z : V)
    (hLN : L ≤ normalizer (V : Set G)) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hVT : V ≤ T) (hVQ : V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hQC : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (V : Set G))
    (hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ ≤ V)
    (hTC : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hz : orderOf (z : G) = 2) (hzT : (z : G) ∈ centralizer (T : Set G))
    (hRC : Centralizer.localResidual L z = L ⊓ centralizer ({(z : G)} : Set G))
    (htrans : FullPointTransvectionAction V (Centralizer.localTwoCore L z) z)
    (hker : (centralizer (V : Set G)).subgroupOf (Centralizer.localTwoCore L z) =
      V.subgroupOf (Centralizer.localTwoCore L z))
    (hfix : V ⊓ centralizer (Centralizer.localTwoCore L z : Set G) = zpowers (z : G))
    (d : G) (hd : d ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hfixed : ∀ x : Centralizer.localTwoCore L z, ⁅(x : G),d⁆ ∈ zpowers (z : G)) : d ∈ V := by
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let R := Centralizer.localResidual L z
  let X := Centralizer.localTwoCore L z
  let W := Centralizer.commutatorSpace L V z
  have hWV : W ≤ V := Centralizer.commutatorSpace_le L V z hLN
  have hRQ : R ≤ normalizer (Q : Set G) :=
    ((Centralizer.localResidual_le L z).trans inf_le_left).trans
      (le_sup_left.trans (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))
  have hRX : R ≤ normalizer (X : Set G) := R.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image R (pCore 2 R))
  have hZR : zpowers (z : G) ≤ centralizer (R : Set G) := by
    apply zpowers_le.mpr
    intro r hr
    exact mem_centralizer_singleton_iff.mp ((Centralizer.localResidual_le L z) hr).2
  let : Group.IsPerfect R := Group.IsPerfect.map _
  have hcentral := centralizer_core_le_of_perfect Q V R X (zpowers (z : G)) hRQ hRX
    ((commutator_mono le_rfl ((Centralizer.localResidual_le L z).trans inf_le_left)).trans hcomm)
    hfix.le hZR
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using
        pCoreIn_le_sylow J (T.subtype le_sup_right)
  obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ J from le_sup_left) (sup_le L.le_normalizer hTL)
  have hST : (S : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hS]
    exact inf_le_left.trans (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)])
  have hSR : (S : Subgroup L).map L.subtype ≤ R := by
    rw [show R = L ⊓ centralizer ({(z : G)} : Set G) from hRC]
    exact le_inf (map_subtype_le _) (fun x hx => mem_centralizer_singleton_iff.mpr (hzT x (hST hx)))
  have hCV := core_centralizer_le_of_sylow L V Q R T hLN hVT hQT
    (by rwa [commutator_comm]) hTC S hSR
  obtain ⟨qW,hqW,_,qX,hqX,hkX,hpair⟩ := htrans
  obtain ⟨w,hw,hwc⟩ := transvection_fixed_coset W X V (z : G) hz qW hqW qX hqX
    (hkX.trans hker) hpair
    ((Centralizer.localTwoCore_le L z).trans ((Centralizer.localResidual_le L z).trans inf_le_right))
    d hfixed (hQC hd)
  have hwdQ : w⁻¹*d ∈ Q := Q.mul_mem (Q.inv_mem (hVQ (hWV hw))) hd
  have hwdV : w⁻¹*d ∈ V := hCV ⟨hwdQ,hcentral ⟨hwdQ,hwc⟩⟩
  simpa only [mul_inv_cancel_left] using V.mul_mem (hWV hw) hwdV


omit [Finite G] in
/-- The full transvection action detects every element centralizing the seed;
the other core contributes no new action because it centralizes V. -/
theorem point_closure_seed_centralizers
    (L V Q : Subgroup G) [IsElementaryAbelian 2 V] (z : V)
    (hz : orderOf (z : G) = 2)
    (hLN : L ≤ normalizer (V : Set G)) (hLQ : L ≤ normalizer (Q : Set G))
    (hVQ : V ≤ Q) (hQC : Q ≤ centralizer (V : Set G))
    (htrans : FullPointTransvectionAction V (Centralizer.localTwoCore L z) z)
    (hker : (centralizer (V : Set G)).subgroupOf (Centralizer.localTwoCore L z) =
      V.subgroupOf (Centralizer.localTwoCore L z))
    (hfix : V ⊓ centralizer (Centralizer.localTwoCore L z : Set G) = zpowers (z : G))
    (hZW : zpowers (z : G) ≤ Centralizer.commutatorSpace L V z)
    (hjoin : (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype ⊔ Q =
      Centralizer.localTwoCore L z ⊔ Q)
    (hcap : Q ⊓ (Centralizer.sourceClosure L V z).map
      (centralizer ({(z : G)} : Set G)).subtype = Centralizer.commutatorSpace L V z) :
    let W := Centralizer.commutatorSpace L V z
    let E := (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype
    E ⊓ centralizer (W : Set G) = W ∧ W ⊓ centralizer (E : Set G) = zpowers (z : G) := by
  let W := Centralizer.commutatorSpace L V z
  let E := (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype
  let X := Centralizer.localTwoCore L z
  let J := X ⊔ Q
  have hWV : W ≤ V := Centralizer.commutatorSpace_le L V z hLN
  have hWE : W ≤ E := Centralizer.commutatorSpace_le_sourceClosure L V z z.property hLN
  have hXL : X ≤ L := (Centralizer.localTwoCore_le L z).trans
    ((Centralizer.localResidual_le L z).trans inf_le_left)
  have hJQ : J ≤ normalizer (Q : Set G) := sup_le (hXL.trans hLQ) Q.le_normalizer
  have hQW : Q ≤ centralizer (W : Set G) := hQC.trans (centralizer_le hWV)
  have hWQ : W ≤ centralizer (Q : Set G) := le_centralizer_iff.mp hQW
  obtain ⟨qW,hqW,_,qX,_,hkX,hpair⟩ := htrans
  have hxfix (x : X) (hx : (x : G) ∈ centralizer (W : Set G)) : (x : G) ∈ V := by
    have hz1 : (z : G) ≠ 1 := by intro he; simp [he] at hz
    have hp (b : ZMod 2) : (z : G)^b.val=1 → b=0 := by
      fin_cases b <;> simp [hz1,ZMod.val_one_eq_one_mod]
    have hx0 : qX x=1 := by
      apply Multiplicative.toAdd.injective
      apply LinearMap.ext
      intro v
      change (qX x).toAdd v = 0
      obtain ⟨w,hw⟩ := hqW (Multiplicative.ofAdd v)
      have he := hpair x w
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx w w.property).symm] at he
      have hv := hp _ he.symm
      simpa only [hw,toAdd_ofAdd] using hv
    exact hker.le (hkX.le hx0)
  have hself : E ⊓ centralizer (W : Set G) ≤ W := by
    intro a ha
    have haJ : a ∈ J := hjoin.le (mem_sup_left ha.1)
    let : (Q.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJQ
    have haJ' : (⟨a,haJ⟩ : J) ∈ X.subgroupOf J ⊔ Q.subgroupOf J := by
      rw [←subgroupOf_sup (show X ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
      exact mem_top _
    obtain ⟨x,hx,q,hq,he⟩ := mem_sup_of_normal_right.mp haJ'
    have he' : (x : G)*(q : G)=a := congrArg J.subtype he
    have hxW : (x : G) ∈ centralizer (W : Set G) := by
      have hh := (centralizer (W : Set G)).mul_mem ha.2 ((centralizer _).inv_mem (hQW hq))
      change a*(q : G)⁻¹ ∈ _ at hh
      rwa [←he',mul_inv_cancel_right] at hh
    have haQ : a ∈ Q := by
      rw [←he']
      exact Q.mul_mem (hVQ (hxfix ⟨x,hx⟩ hxW)) hq
    exact hcap.le ⟨haQ,ha.1⟩
  have hZE : zpowers (z : G) ≤ centralizer (E : Set G) := by
    apply zpowers_le.mpr
    intro e he
    exact mem_centralizer_singleton_iff.mp ((map_subtype_le _) he)
  refine ⟨le_antisymm hself ?_,le_antisymm ?_ (le_inf hZW hZE)⟩
  · intro w hw
    exact ⟨hWE hw, fun v hv => congrArg Subtype.val
      (mul_comm' (⟨v,hWV hv⟩ : V) ⟨w,hWV hw⟩)⟩
  · intro w hw
    apply hfix.le
    refine ⟨hWV hw.1,?_⟩
    have hh : w ∈ centralizer ((E ⊔ Q : Subgroup G) : Set G) := by
      have he : E ≤ centralizer ({w} : Set G) := fun e he => mem_centralizer_singleton_iff.mpr (hw.2 e he)
      have hq : Q ≤ centralizer ({w} : Set G) := fun q hq => mem_centralizer_singleton_iff.mpr (hWQ hw.1 q hq)
      intro a ha
      exact mem_centralizer_singleton_iff.mp ((sup_le he hq) ha)
    rw [hjoin] at hh
    exact centralizer_le (show X ≤ X ⊔ Q from le_sup_left) hh

/-- The actual seed centralizers identify the center of the original relative
normal closure, so its already elementary central quotient is extraspecial. -/
theorem point_closure_extraspecial
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : V)
    (hz : orderOf (z : G) = 2) (hLN : L ≤ normalizer (V : Set G))
    (helem : IsElementaryAbelian 2 ((Centralizer.sourceClosure L V z) ⧸
      center (Centralizer.sourceClosure L V z)))
    (hlarge : 2 < Nat.card (Centralizer.commutatorSpace L V z))
    (hself : let W := Centralizer.commutatorSpace L V z
      let E := (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype
      E ⊓ centralizer (W : Set G) = W)
    (hfixed : let W := Centralizer.commutatorSpace L V z
      let E := (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype
      W ⊓ centralizer (E : Set G) = zpowers (z : G)) :
    IsExtraspecial 2 (Centralizer.sourceClosure L V z) := by
  let Cz := centralizer ({(z : G)} : Set G)
  let E0 := Centralizer.sourceClosure L V z
  let E := E0.map Cz.subtype
  let W := Centralizer.commutatorSpace L V z
  let f := Cz.subtype.comp E0.subtype
  have hf : Function.Injective f := Cz.subtype_injective.comp E0.subtype_injective
  have hWE : W ≤ E := Centralizer.commutatorSpace_le_sourceClosure L V z z.property hLN
  have hcenter : (center E0).map f = zpowers (z : G) := by
    apply le_antisymm
    · rintro a ⟨e,he,rfl⟩
      have heE : f e ∈ E := mem_map_of_mem Cz.subtype e.property
      have hc : f e ∈ centralizer (E : Set G) := by
        rintro x ⟨c,hc,rfl⟩
        exact congrArg f (mem_center_iff.mp he ⟨c,hc⟩)
      exact hfixed.le ⟨hself.le ⟨heE,centralizer_le hWE hc⟩,hc⟩
    · intro a ha
      have haW : a ∈ W := (hfixed.ge ha).1
      obtain ⟨c,hc,rfl⟩ := hWE haW
      refine ⟨⟨c,hc⟩,?_,rfl⟩
      apply mem_center_iff.mpr
      intro e
      apply hf
      exact (hfixed.ge ha).2 (f e) (mem_map_of_mem Cz.subtype e.property)
  have hcard : Nat.card (center E0) = 2 := by
    rw [Nat.card_congr ((center E0).equivMapOfInjective f hf).toEquiv,hcenter,Nat.card_zpowers]
    exact hz
  refine ⟨hcard,helem,QuotientGroup.nontrivial_iff.mpr ?_⟩
  intro htop
  change center E0 = ⊤ at htop
  have hcardE : Nat.card E0=2 := by simpa only [htop,card_top] using hcard
  have hcardE' : Nat.card E = 2 := by
    rw [←Nat.card_congr (E0.equivMapOfInjective Cz.subtype Cz.subtype_injective).toEquiv]
    exact hcardE
  have hle := Nat.card_le_card_of_injective (inclusion hWE) (inclusion_injective hWE)
  rw [hcardE'] at hle
  exact (not_le_of_gt hlarge) hle

/-- The retained kernel gives the exact order of the original closure: the
seed has order 32 and the full dual actor quotient has order 16. -/
theorem point_closure_card
    (L V Q : Subgroup G) (z : G)
    (hLQ : L ≤ normalizer (Q : Set G)) (hVQ : V ≤ Q)
    (hQC : Q ≤ centralizer (V : Set G)) (hVX : V ≤ Centralizer.localTwoCore L z)
    (htrans : FullPointTransvectionAction V (Centralizer.localTwoCore L z) z)
    (hker : (centralizer (V : Set G)).subgroupOf (Centralizer.localTwoCore L z) =
      V.subgroupOf (Centralizer.localTwoCore L z))
    (hWcard : Nat.card (Centralizer.commutatorSpace L V z) = 32)
    (hjoin : (Centralizer.sourceClosure L V z).map (centralizer ({z} : Set G)).subtype ⊔ Q =
      Centralizer.localTwoCore L z ⊔ Q)
    (hcap : Q ⊓ (Centralizer.sourceClosure L V z).map
      (centralizer ({z} : Set G)).subtype = Centralizer.commutatorSpace L V z) :
    Nat.card (Centralizer.sourceClosure L V z) = 512 := by
  let Cz := centralizer ({z} : Set G)
  let E0 := Centralizer.sourceClosure L V z
  let E := E0.map Cz.subtype
  let X := Centralizer.localTwoCore L z
  have hXQ : X ≤ normalizer (Q : Set G) :=
    ((Centralizer.localTwoCore_le L z).trans ((Centralizer.localResidual_le L z).trans inf_le_left)).trans hLQ
  have hEQ : E ≤ normalizer (Q : Set G) :=
    (le_sup_left.trans hjoin.le).trans (sup_le hXQ Q.le_normalizer)
  have hQX : Q ⊓ X = V := by
    apply le_antisymm ?_ (le_inf hVQ hVX)
    intro x hx
    exact hker.le (show (⟨x,hx.2⟩ : X) ∈ (centralizer (V : Set G)).subgroupOf X from hQC hx.1)
  obtain ⟨_,_,_,qX,hqX,hkX,_⟩ := htrans
  have hmodel : Nat.card (Multiplicative (Module.Dual (ZMod 2) (Fin 2 → HermitianTensorThree.E 1))) = 16 := by
    have hd : Module.finrank (ZMod 2) (Fin 2 → HermitianTensorThree.E 1) = 4 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fin 2 → HermitianTensorThree.E 1)
      rw [Nat.card_zmod,Nat.card_fun,Nat.card_fin,card_E] at hh
      exact (Nat.pow_right_inj (by decide : 1<2)).mp hh.symm
    change Nat.card (Module.Dual (ZMod 2) (Fin 2 → HermitianTensorThree.E 1))=16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,Subspace.dual_finrank_eq,hd]
    norm_num
  have hXcard : Nat.card X = 16*Nat.card V := by
    rw [qX.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective qX hqX).toEquiv,hmodel,
      hkX,hker,Nat.card_congr (subgroupOfEquivOfLe hVX).toEquiv]
  have hprodX := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q X hXQ
  rw [hQX,hXcard] at hprodX
  have hprodE := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q E hEQ
  rw [hcap,hWcard,sup_comm Q E,hjoin,sup_comm X Q] at hprodE
  have hsum : Nat.card (Q ⊔ X : Subgroup G) = 16*Nat.card Q := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := V))
    nlinarith [hprodX]
  have hcard : Nat.card E = 512 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q))
    rw [hsum] at hprodE
    nlinarith [hprodE]
  exact (Nat.card_congr (E0.equivMapOfInjective Cz.subtype Cz.subtype_injective).toEquiv).trans hcard

/-- The original normal closure is the literal central product of four D₈'s.
The seed, its order, and its center containment are retained in recognition. -/
theorem point_closure_four_model
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : V)
    (hLN : L ≤ normalizer (V : Set G))
    (hextra : IsExtraspecial 2 (Centralizer.sourceClosure L V z))
    (hEcard : Nat.card (Centralizer.sourceClosure L V z) = 512)
    (hWcard : Nat.card (Centralizer.commutatorSpace L V z) = 32)
    (hself : let W := Centralizer.commutatorSpace L V z
      let E := (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype
      E ⊓ centralizer (W : Set G) = W) :
    Nonempty (Centralizer.sourceClosure L V z ≃* DihedralCentralProductFourSix.FourModel) := by
  let Cz := centralizer ({(z : G)} : Set G)
  let E0 := Centralizer.sourceClosure L V z
  let W := Centralizer.commutatorSpace L V z
  have hWC : W ≤ Cz := Centralizer.commutatorSpace_le_centralizer L V z z.property hLN
  let Wc := W.subgroupOf Cz
  have hWE : Wc ≤ E0 := le_normalClosure
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (Centralizer.commutatorSpace_le L V z hLN)
  let : IsElementaryAbelian 2 Wc := IsElementaryAbelian.subgroupOf hWC
  let : IsElementaryAbelian 2 (Wc.subgroupOf E0) := IsElementaryAbelian.subgroupOf hWE
  let := hextra
  have hcard : Nat.card (Wc.subgroupOf E0) = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWE).toEquiv).trans
      ((Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv).trans hWcard)
  have hcenter : center E0 ≤ Wc.subgroupOf E0 := by
    intro e he
    apply hself.le
    refine ⟨mem_map_of_mem Cz.subtype e.property,?_⟩
    intro w hw
    let wc : Cz := ⟨w,hWC hw⟩
    exact congrArg (Cz.subtype.comp E0.subtype) (mem_center_iff.mp he ⟨wc,hWE hw⟩)
  exact ⟨DihedralCentralProductFourSix.recognition 3 hEcard (Wc.subgroupOf E0) hcard hcenter⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
