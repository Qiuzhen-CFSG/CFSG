module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointExtraspecial
public import Theory.GroupTheory.Commutator.PerfectClassTwoAction

/-!
# The original point radical is the closure times the module

The full dual interval applies to V(E ∩ O₂(L_z)). Its small alternative
would make [E,L_z] abelian. Since L_z is perfect and fixes the center of
the class-two group E, the three-subgroup lemma would force it to centralize
E, contradicting its actual natural action on V_z/⟨z⟩. Thus the interval
fills O₂(L_z). The previously computed core intersection and product orders
remove the entire O₂(LT) denominator and give EV = O₂(L_z).

Source: Aschbacher–Smith 8.2.12(3), printed p.722, refs/quasithin.pdf.
The original relative closure, residual, module, Sylow and full kernels
are retained. The Chapter 12 tensor consumer supplies all local premises.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

omit [Finite G] in
/-- The marked natural section has a nontrivial action, witnessed by an upper transvection. -/
theorem PointSectionActions.natural_not_centralized
    (V W Z R : Subgroup G) (h : PointSectionActions V W Z R) :
    ¬ W ≤ centralizer (R : Set G) := by
  obtain ⟨_,hRW,eR,qW,hqW,_,hact,_⟩ := h
  intro hc
  let u : SL(2,E 1) := ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩
  let v : Multiplicative (Fin 2 → E 1) := Multiplicative.ofAdd ![0,1]
  obtain ⟨r,hr⟩ := (eR.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 R))) u
  change eR (QuotientGroup.mk' (pCore 2 R) r) = u at hr
  obtain ⟨w,hw⟩ := hqW v
  have he : W.normalizerMonoidHom (inclusion hRW r) w = w := by
    apply Subtype.ext
    change (r : G)*(w : G)*(r : G)⁻¹=(w : G)
    rw [hc w.property r r.property,mul_inv_cancel_right]
  have hh := hact r w
  rw [he,hw,hr] at hh
  have h0 := congrArg (fun a : Multiplicative (Fin 2 → E 1) => a.toAdd 0) hh
  simp [Matrix.SL2.naturalAction_apply,u,v,Matrix.mulVec,dotProduct] at h0

/-- Remove the full LT-core denominator using the perfect point action. -/
theorem point_closure_join_module
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G) (z : V)
    (hz : orderOf (z : G) = 2)
    (hLN : L ≤ normalizer (V : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hVQ : V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hQC : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (V : Set G))
    (hVX : V ≤ Centralizer.localTwoCore L z)
    (hsections : PointSectionActions V (Centralizer.commutatorSpace L V z)
      (zpowers (z : G)) (Centralizer.localResidual L z))
    (htrans : FullPointTransvectionAction V (Centralizer.localTwoCore L z) z)
    (hker : (centralizer (V : Set G)).subgroupOf (Centralizer.localTwoCore L z) =
      V.subgroupOf (Centralizer.localTwoCore L z))
    (hfix : V ⊓ centralizer (Centralizer.localTwoCore L z : Set G) = zpowers (z : G))
    (hZW : zpowers (z : G) ≤ Centralizer.commutatorSpace L V z)
    (hE : (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype =
      (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (hclass : ⁅Centralizer.sourceClosure L V z,Centralizer.sourceClosure L V z⁆ ≤
      (zpowers (z : G)).subgroupOf (centralizer ({(z : G)} : Set G)))
    (hjoin : (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      Centralizer.localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcap : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓
      (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype =
      Centralizer.commutatorSpace L V z) :
    (Centralizer.sourceClosure L V z).map (centralizer ({(z : G)} : Set G)).subtype ⊔ V =
      Centralizer.localTwoCore L z := by
  let C := centralizer ({(z : G)} : Set G)
  let E := (Centralizer.sourceClosure L V z).map C.subtype
  let R := Centralizer.localResidual L z
  let X := Centralizer.localTwoCore L z
  let W := Centralizer.commutatorSpace L V z
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let J := L ⊔ (T : Subgroup G)
  have hRL : R ≤ L := (Centralizer.localResidual_le L z).trans inf_le_left
  have hRC : R ≤ C := (Centralizer.localResidual_le L z).trans inf_le_right
  have hXR : X ≤ R := Centralizer.localTwoCore_le L z
  have hWV : W ≤ V := Centralizer.commutatorSpace_le L V z hLN
  have hWE : W ≤ E := Centralizer.commutatorSpace_le_sourceClosure L V z z.property hLN
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
  have hQR := hQT.trans (point_commutator_normalizes L V (T : Subgroup G) z hTL hTV hTC).1
  have hER : E ≤ normalizer (R : Set G) :=
    (le_sup_left.trans hjoin.le).trans (sup_le (hXR.trans R.le_normalizer) hQR)
  have hEX : E ⊓ R ≤ X := by
    rw [show E = C.pCoreIn 2 from hE,inf_comm]
    exact inf_pCoreIn_le_of_le 2 hRC
  have hQX : Q ⊓ X = V := by
    apply le_antisymm ?_ (le_inf hVQ hVX)
    intro x hx
    exact hker.le (show (⟨x,hx.2⟩ : X) ∈ (centralizer (V : Set G)).subgroupOf X from hQC hx.1)
  obtain ⟨hself,hfixed⟩ := point_closure_seed_centralizers L V Q z hz hLN hLQ hVQ hQC
    htrans hker hfix hZW hjoin hcap
  let Y := V ⊔ (E ⊓ X)
  have hRY : R ≤ normalizer (Y : Set G) :=
    (le_inf (hRL.trans hLN) ((le_inf hRE hRX).trans inf_normalizer_le_normalizer_inf)).trans
      (normalizer_inf_normalizer_le_normalizer_sup V (E ⊓ X))
  have hXY : X ≤ E ⊔ V := by
    have hz1 : (z : G) ≠ 1 := by intro he; simp [he] at hz
    rcases point_residual_dual_interval L V z hz1 hZW hsections htrans hker Y
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
      exact hsections.natural_not_centralized V W (zpowers (z : G)) R
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

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
