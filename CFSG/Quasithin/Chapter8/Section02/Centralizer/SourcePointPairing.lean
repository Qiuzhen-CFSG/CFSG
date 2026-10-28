module
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.SourceClosure
public import Theory.GroupTheory.TransvectionFixedCoset
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.Commutator.PerfectClassTwoAction
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PCoreRestriction

/-!
# The full source point pairing and core intersection

The actual commutator pairing removes a displacement in the central line
by an element of V_z. Perfectness of L_z propagates fixation to L_z, and
averaging over a Sylow subgroup of L puts the corrected element in V.
Thus fixed cosets in the entire O₂(LT) are controlled by the original
point pairing, without classifying extensions of the module.

Source: Aschbacher--Smith 8.2.11(4) and 8.2.12, printed p.722,
refs/quasithin.pdf. The whole residual, central line and action kernel
are retained; the M22 application supplies the native four-dimensional
quotient and its dual.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- Both original quotient maps in the full binary point pairing.
The actor kernel is its entire centralizer on V. -/
@[expose] def SourcePointPairing (L V : Subgroup G) (z : G)
    (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] : Prop :=
  ∃ qW : commutatorSpace L V z →* Multiplicative M,
    Function.Surjective qW ∧ qW.ker = (zpowers z).subgroupOf (commutatorSpace L V z) ∧
    ∃ qX : localTwoCore L z →* Multiplicative (Module.Dual (ZMod 2) M),
      Function.Surjective qX ∧ qX.ker = (centralizer (V : Set G)).subgroupOf (localTwoCore L z) ∧
      ∀ (x : localTwoCore L z) (w : commutatorSpace L V z),
        ⁅(x : G),(w : G)⁆ = z ^ ((qX x).toAdd (qW w).toAdd).val

/-- Fixed points modulo the central line in the full LT core already lie
in the original module. No indecomposable-extension premise is added. -/
theorem sourcePoint_full_core_second_fixed
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G) (z : V)
    (hLN : L ≤ normalizer (V : Set G)) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hVT : V ≤ T) (hVQ : V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hQC : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (V : Set G))
    (hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ ≤ V)
    (hTC : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hz : orderOf (z : G) = 2) (hzT : (z : G) ∈ centralizer (T : Set G))
    (hRC : localResidual L z = L ⊓ centralizer ({(z : G)} : Set G))
    (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (htrans : SourcePointPairing L V z M)
    (hker : (centralizer (V : Set G)).subgroupOf (localTwoCore L z) =
      V.subgroupOf (localTwoCore L z))
    (hfix : V ⊓ centralizer (localTwoCore L z : Set G) = zpowers (z : G))
    (d : G) (hd : d ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hfixed : ∀ x : localTwoCore L z, ⁅(x : G),d⁆ ∈ zpowers (z : G)) : d ∈ V := by
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let R := localResidual L z
  let X := localTwoCore L z
  let W := commutatorSpace L V z
  have hWV : W ≤ V := commutatorSpace_le L V z hLN
  have hRQ : R ≤ normalizer (Q : Set G) :=
    ((localResidual_le L z).trans inf_le_left).trans
      (le_sup_left.trans (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))
  have hRX : R ≤ normalizer (X : Set G) := R.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image R (pCore 2 R))
  have hZR : zpowers (z : G) ≤ centralizer (R : Set G) := by
    apply zpowers_le.mpr
    intro r hr
    exact mem_centralizer_singleton_iff.mp ((localResidual_le L z) hr).2
  let : Group.IsPerfect R := Group.IsPerfect.map _
  have hcentral := centralizer_core_le_of_perfect Q V R X (zpowers (z : G)) hRQ hRX
    ((commutator_mono le_rfl ((localResidual_le L z).trans inf_le_left)).trans hcomm)
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
    ((localTwoCore_le L z).trans ((localResidual_le L z).trans inf_le_right))
    d hfixed (hQC hd)
  have hwdQ : w⁻¹*d ∈ Q := Q.mul_mem (Q.inv_mem (hVQ (hWV hw))) hd
  have hwdV : w⁻¹*d ∈ V := hCV ⟨hwdQ,hcentral ⟨hwdQ,hwc⟩⟩
  simpa only [mul_inv_cancel_left] using V.mul_mem (hWV hw) hwdV


omit [Finite G] in
/-- The full transvection action detects every element centralizing the seed;
the other core contributes no new action because it centralizes V. -/
theorem sourcePoint_seed_centralizers
    (L V Q : Subgroup G) [IsElementaryAbelian 2 V] (z : V)
    (hz : orderOf (z : G) = 2)
    (hLN : L ≤ normalizer (V : Set G)) (hLQ : L ≤ normalizer (Q : Set G))
    (hVQ : V ≤ Q) (hQC : Q ≤ centralizer (V : Set G))
    (M : Type*) [AddCommGroup M] [Module (ZMod 2) M]
    (htrans : SourcePointPairing L V z M)
    (hker : (centralizer (V : Set G)).subgroupOf (localTwoCore L z) =
      V.subgroupOf (localTwoCore L z))
    (hfix : V ⊓ centralizer (localTwoCore L z : Set G) = zpowers (z : G))
    (hZW : zpowers (z : G) ≤ commutatorSpace L V z)
    (hjoin : (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype ⊔ Q =
      localTwoCore L z ⊔ Q)
    (hcap : Q ⊓ (sourceClosure L V z).map
      (centralizer ({(z : G)} : Set G)).subtype = commutatorSpace L V z) :
    let W := commutatorSpace L V z
    let E := (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype
    E ⊓ centralizer (W : Set G) = W ∧ W ⊓ centralizer (E : Set G) = zpowers (z : G) := by
  let W := commutatorSpace L V z
  let E := (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype
  let X := localTwoCore L z
  let J := X ⊔ Q
  have hWV : W ≤ V := commutatorSpace_le L V z hLN
  have hWE : W ≤ E := commutatorSpace_le_sourceClosure L V z z.property hLN
  have hXL : X ≤ L := (localTwoCore_le L z).trans
    ((localResidual_le L z).trans inf_le_left)
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


omit [Finite G] in
/-- The same two maps transfer the original point-section irreducibility to
its full dual core quotient, with V as the complete denominator. -/
theorem sourcePoint_dual_interval
    (L V : Subgroup G) (z : G) (hz : z ≠ 1)
    (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (htrans : SourcePointPairing L V z M)
    (hker : (centralizer (V : Set G)).subgroupOf (localTwoCore L z) =
      V.subgroupOf (localTwoCore L z))
    (hZW : zpowers z ≤ commutatorSpace L V z)
    (hRW : localResidual L z ≤ normalizer (commutatorSpace L V z : Set G))
    (hirr : ∀ Y : Subgroup G, zpowers z ≤ Y → Y ≤ commutatorSpace L V z →
      localResidual L z ≤ normalizer (Y : Set G) → Y = zpowers z ∨ Y = commutatorSpace L V z)
    (Y : Subgroup G) (hVY : V ≤ Y) (hYX : Y ≤ localTwoCore L z)
    (hRY : localResidual L z ≤ normalizer (Y : Set G)) :
    Y = V ∨ Y = localTwoCore L z := by
  obtain ⟨qW,hqW,hkerW,qX,_,hkerX,hpair⟩ := htrans
  exact transvection_dual_interval (commutatorSpace L V z) (localTwoCore L z)
    V (localResidual L z) z hz qW hqW hkerW qX (hkerX.trans hker) hpair hZW
    ((localTwoCore_le L z).trans ((localResidual_le L z).trans inf_le_right))
    hRW hirr Y hVY hYX hRY

/-- Remove the full LT-core denominator using the perfect point action. -/
theorem sourcePoint_closure_join_module
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G) (z : V)
    (hz : orderOf (z : G) = 2)
    (hLN : L ≤ normalizer (V : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (localResidual L z : Set G))
    (hVQ : V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hQC : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (V : Set G))
    (hVX : V ≤ localTwoCore L z)
    (hRW : localResidual L z ≤ normalizer (commutatorSpace L V z : Set G))
    (hirr : ∀ Y : Subgroup G, zpowers (z : G) ≤ Y → Y ≤ commutatorSpace L V z →
      localResidual L z ≤ normalizer (Y : Set G) →
      Y = zpowers (z : G) ∨ Y = commutatorSpace L V z)
    (hnact : ¬ commutatorSpace L V z ≤ centralizer (localResidual L z : Set G))
    (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (htrans : SourcePointPairing L V z M)
    (hker : (centralizer (V : Set G)).subgroupOf (localTwoCore L z) =
      V.subgroupOf (localTwoCore L z))
    (hfix : V ⊓ centralizer (localTwoCore L z : Set G) = zpowers (z : G))
    (hZW : zpowers (z : G) ≤ commutatorSpace L V z)
    (hE : (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype =
      (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (hclass : ⁅sourceClosure L V z,sourceClosure L V z⁆ ≤
      (zpowers (z : G)).subgroupOf (centralizer ({(z : G)} : Set G)))
    (hjoin : (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcap : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓
      (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype =
      commutatorSpace L V z) :
    (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype ⊔ V =
      localTwoCore L z := by
  let C := centralizer ({(z : G)} : Set G)
  let E := (sourceClosure L V z).map C.subtype
  let R := localResidual L z
  let X := localTwoCore L z
  let W := commutatorSpace L V z
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let J := L ⊔ (T : Subgroup G)
  have hRL : R ≤ L := (localResidual_le L z).trans inf_le_left
  have hRC : R ≤ C := (localResidual_le L z).trans inf_le_right
  have hXR : X ≤ R := localTwoCore_le L z
  have hWV : W ≤ V := commutatorSpace_le L V z hLN
  have hWE : W ≤ E := commutatorSpace_le_sourceClosure L V z z.property hLN
  have hLQ : L ≤ normalizer (Q : Set G) := le_sup_left.trans
    (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hXQ : X ≤ normalizer (Q : Set G) := (hXR.trans hRL).trans hLQ
  have hEC : E ≤ C := map_subtype_le _
  have hCE : C ≤ normalizer (E : Set G) := by
    rw [show E = C.pCoreIn 2 from hE]
    exact C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hRE := hRC.trans hCE
  have hRX : R ≤ normalizer (X : Set G) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R (pCore 2 R))
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using
        pCoreIn_le_sylow J (T.subtype le_sup_right)
  have hQR := hQT.trans hTR
  have hER : E ≤ normalizer (R : Set G) :=
    (le_sup_left.trans hjoin.le).trans (sup_le (hXR.trans R.le_normalizer) hQR)
  have hEX : E ⊓ R ≤ X := by
    rw [show E = C.pCoreIn 2 from hE,inf_comm]
    exact inf_pCoreIn_le_of_le 2 hRC
  have hQX : Q ⊓ X = V := by
    apply le_antisymm ?_ (le_inf hVQ hVX)
    intro x hx
    exact hker.le (show (⟨x,hx.2⟩ : X) ∈ (centralizer (V : Set G)).subgroupOf X from hQC hx.1)
  obtain ⟨hself,hfixed⟩ := sourcePoint_seed_centralizers L V Q z hz hLN hLQ hVQ hQC
    M htrans hker hfix hZW hjoin hcap
  let Y := V ⊔ (E ⊓ X)
  have hRY : R ≤ normalizer (Y : Set G) :=
    (le_inf (hRL.trans hLN) ((le_inf hRE hRX).trans inf_normalizer_le_normalizer_inf)).trans
      (normalizer_inf_normalizer_le_normalizer_sup V (E ⊓ X))
  have hXY : X ≤ E ⊔ V := by
    have hz1 : (z : G) ≠ 1 := by intro he; simp [he] at hz
    rcases sourcePoint_dual_interval L V z hz1 M htrans hker hZW hRW hirr Y
      le_sup_left (sup_le hVX inf_le_right) hRY with hy|hy
    · exfalso
      have hc : ⁅E,R⁆ ≤ V := by
        have hh : ⁅E,R⁆ ≤ E ⊓ R := le_inf
          (le_normalizer_iff_commutator_le_left.mp hRE)
          (le_normalizer_iff_commutator_le_right.mp hER)
        exact ((le_inf (hh.trans inf_le_left) (hh.trans hEX)).trans
          (show E ⊓ X ≤ Y from le_sup_right)).trans hy.le
      have hclass' : ⁅E,E⁆ ≤ zpowers (z : G) := by
        have hh := map_mono (f := C.subtype) hclass
        rw [map_commutator,map_subgroupOf_eq_of_le (hZW.trans (hWV.trans (by
          intro v hv
          exact mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mul_comm' (⟨v,hv⟩ : V) z)))))] at hh
        exact hh
      have hcenter : E ⊓ centralizer (E : Set G) ≤ zpowers (z : G) := by
        intro a ha
        exact hfixed.le ⟨hself.le ⟨ha.1,centralizer_le hWE ha.2⟩,ha.2⟩
      have hZR : zpowers (z : G) ≤ centralizer (R : Set G) := zpowers_le.mpr (by
        intro r hr
        exact mem_centralizer_singleton_iff.mp (hRC hr))
      let : Group.IsPerfect R := Group.IsPerfect.map _
      have hzero := commutator_eq_bot_of_perfect_abelian_classTwo_action E (zpowers (z : G)) R
        hRE hclass' hcenter (commutator_eq_bot_iff_le_centralizer.mpr hZR)
        (le_bot_iff.mp ((commutator_mono hc hc).trans_eq (commutator_self_eq_bot_iff.mpr inferInstance)))
      exact hnact
        (hWE.trans (commutator_eq_bot_iff_le_centralizer.mp hzero))
    · exact hy.ge.trans (sup_le le_sup_right (inf_le_left.trans le_sup_left))
  have hEQ : E ≤ normalizer (Q : Set G) :=
    (le_sup_left.trans hjoin.le).trans (sup_le hXQ Q.le_normalizer)
  have hVE : V ≤ normalizer (E : Set G) := (hVX.trans (hXR.trans hRC)).trans hCE
  have hEV : E ⊓ V = W := le_antisymm
    (fun a ha => hcap.le ⟨hVQ ha.2,ha.1⟩) (le_inf hWE hWV)
  have h1 := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q E hEQ
  have h2 := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q X hXQ
  have h3 := card_mul_eq_card_inf_mul_card_sup_of_normalizes E V hVE
  rw [hcap,sup_comm Q E,hjoin,sup_comm X Q] at h1
  rw [hQX] at h2
  rw [hEV] at h3
  have hc : Nat.card (E ⊔ V : Subgroup G) = Nat.card X := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := W))
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q))
    nlinarith [congrArg (fun n => n*Nat.card V) h1,
      congrArg (fun n => n*Nat.card E) h2,
      congrArg (fun n => n*Nat.card Q) h3]
  exact (eq_of_le_of_card_ge hXY hc.le).symm


omit [Finite G] in
/-- The full-core fixed-subgroup bound identifies both the full core
intersection and the original relative normal closure. -/
theorem sourcePoint_core_intersection_of_fixed_bound
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G) (z : V)
    (hLN : L ≤ normalizer (V : Set G))
    (hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hVQ : V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcore : sourceClosure L V z ≤ pCore 2 (centralizer ({(z : G)} : Set G)))
    (hcover : (centralizer ({(z : G)} : Set G)).pCoreIn 2 ≤
      (sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype ⊔
        (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hc : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓
      (centralizer ({(z : G)} : Set G)).pCoreIn 2, localTwoCore L z⁆ ≤ zpowers (z : G))
    (hfixed : ∀ a ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2,
      (∀ x : localTwoCore L z, ⁅(x : G),a⁆ ∈ zpowers (z : G)) →
        a ∈ commutatorSpace L V z) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ (centralizer ({(z : G)} : Set G)).pCoreIn 2 =
      commutatorSpace L V z ∧
      sourceClosure L V z = pCore 2 (centralizer ({(z : G)} : Set G)) := by
  let C := centralizer ({(z : G)} : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let E := sourceClosure L V z
  let W := commutatorSpace L V z
  have hWE := commutatorSpace_le_sourceClosure L V z z.property hLN
  have hWQ : W ≤ Q := (commutatorSpace_le L V z hLN).trans hVQ
  have hcap : Q ⊓ C.pCoreIn 2 = W := by
    apply le_antisymm ?_ (le_inf hWQ (hWE.trans (map_mono hcore)))
    intro a ha
    apply hfixed a ha.1
    intro x
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator x.property ha)
  refine ⟨hcap,sourceClosure_eq_core_of_cover L V z (Q.subgroupOf C) hcore ?_ ?_⟩
  · have hQC : Q ≤ C := by
      have hQT : Q ≤ (T : Subgroup G) := by
        simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
          (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
          pCoreIn_le_sylow _ (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right))
      exact hQT.trans hTC
    have hm : pCore 2 C ≤ E ⊔ Q.subgroupOf C := by
      apply (map_le_map_iff_of_injective C.subtype_injective).mp
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hQC]
      exact hcover
    exact hm
  · intro a ha
    exact hcap.le ⟨ha.2,mem_map_of_mem C.subtype ha.1⟩

end CFSG.Quasithin.Chapter8.Section02.Centralizer
