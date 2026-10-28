module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreStructure
public import Theory.GroupAction.CentralKernelFixedCommutator
public import Theory.ElementaryAbelian.AutomorphismLinearModel
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The actual linear quotient of an original cubic normalizer

In the large-core branch the original core D has central quotient elementary
of order nine. Conjugation by N_G(D) on D/Z(D) has kernel exactly D: a kernel
element fixes D′, hence lies in the original cubic centralizer D H₂; the
opposite SL₂(3) acts faithfully because its central involution inverts D/Z(D).
Orders then make this action onto GL₂(3). The quotient equivalence retains
the literal quotient map and this conjugation action.

The original local Sylow has image of order three. The entire original Borel
maps to its full normalizer, of order twelve. These are marked endpoint
quotient maps for the remaining Atlas amalgam comparison; maps of the whole
endpoints and their compatibility on the whole middle are still required.
The strongly-three-embedded source branch is not excluded here.

Source: Aschbacher–Smith I.4(G1)–(G2) and I.4.5, printed p.417, and the
cubic-normalizer calculation of Fong–Wong, Nagoya Math. J.36 (1969), §3B,
printed p.156. The literal source application is Chapter14LinearQuotient.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
variable (t : CubicTorus c)

theorem maximal_core_central_quotient_elementary : IsElementaryAbelian 3 (cubicOddCore c t.x ⧸ center (cubicOddCore c t.x)) := by
  let D := cubicOddCore c t.x
  let Z := center D
  let q := QuotientGroup.mk' Z
  have hcomm := (cubic_oddCore_inversion c t.x t.x_order t.z
    ((orderOf_coe t.z).trans t.z_order) t.centralizer).2
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
  · intro a b
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective Z a
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective Z b
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact cubicCoreLine_le_center c t.x (hcomm (commutator_mem_commutator a.property b.property))
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective Z a
    rw [←map_pow,t.left_oddCore_cube,map_one]

theorem maximal_core_central_quotient_card (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (cubicOddCore c t.x ⧸ center (cubicOddCore c t.x))=9 := by
  have hz : Nat.card (center (cubicOddCore c t.x))=27 := by
    rw [←card_map_of_injective (cubicOddCore c t.x).subtype_injective,
      ←centerIn_eq_map_center,t.maximal_core_center_card hc]
  have hh := (center (cubicOddCore c t.x)).card_mul_index
  rw [hz,hc,index_eq_card] at hh
  omega

omit [Finite G] in
theorem cubic_core_normalized :
    cubicNormalizer c t.x ≤ normalizer (cubicOddCore c t.x:Set G) := by
  have h := normalizer_le_normalizer_centralizer (zpowers ((t.x:c.H):G))
  have he : Subgroup.centralizer (zpowers ((t.x:c.H):G):Set G)=cubicCentralizer c t.x := by
    rw [zpowers_eq_closure,centralizer_closure]; rfl
  rw [he] at h
  exact h.trans (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _))

def cubicCentralQuotientAction : cubicNormalizer c t.x →*
    MulAut (cubicOddCore c t.x ⧸ center (cubicOddCore c t.x)) :=
  (quotientAut (center (cubicOddCore c t.x))).comp
    ((cubicOddCore c t.x).normalizerMonoidHom.comp (inclusion t.cubic_core_normalized))

private def oppositeInNormalizer : c.H₂ →* cubicNormalizer c t.x where
  toFun y := ⟨y, by
    rw [t.left_ambient_normalizer]
    exact mem_sup_left (mem_sup_right (mem_map_of_mem c.H.subtype y.property))⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private def oppositeCentralAction : c.H₂ →*
    MulAut (cubicOddCore c t.x ⧸ center (cubicOddCore c t.x)) :=
  t.cubicCentralQuotientAction.comp t.oppositeInNormalizer

private theorem central_quotient_inverted (d : cubicOddCore c t.x) :
    t.oppositeCentralAction ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
      (QuotientGroup.mk' (center (cubicOddCore c t.x)) d) =
        (QuotientGroup.mk' (center (cubicOddCore c t.x)) d)⁻¹ := by
  change quotientAut _ _ (QuotientGroup.mk' _ d)=_
  rw [quotientAut_apply_mk]
  apply eq_inv_iff_mul_eq_one.mpr
  rw [←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply cubicCoreLine_le_center c t.x
  exact (cubic_oddCore_inversion c t.x t.x_order t.z
    ((orderOf_coe t.z).trans t.z_order) t.centralizer).1 d d.property

private theorem oppositeCentralAction_injective
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Function.Injective t.oppositeCentralAction := by
  let D := cubicOddCore c t.x
  let W := center D
  let q := QuotientGroup.mk' W
  let ρ := t.oppositeCentralAction
  let z : c.H₂ := ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
  have hz : orderOf z=2 := (orderOf_coe z).symm.trans t.z_order
  have hzρ : ρ z≠1 := by
    intro he
    have hW : W=⊤ := by
      apply top_unique
      intro d _
      have hinv := t.central_quotient_inverted d
      change ρ z (q d)=(q d)⁻¹ at hinv
      rw [he] at hinv
      change q d=(q d)⁻¹ at hinv
      have htwo : (q d)^2=1 := by
        rw [pow_two]
        calc
          q d * q d = (q d)⁻¹ * q d := congrArg (fun a => a * q d) hinv
          _ = 1 := inv_mul_cancel _
      have hthree : (q d)^3=1 := by rw [←map_pow,t.left_oddCore_cube,map_one]
      apply (QuotientGroup.eq_one_iff _).mp
      change q d=1
      simpa only [show 3=2+1 from rfl,pow_succ,htwo,one_mul] using hthree
    have hh := t.maximal_core_central_quotient_card hc
    change Nat.card (D ⧸ W)=9 at hh
    simp [hW] at hh
  let e := c.H₂_model.some
  let f := ρ.comp e.symm.toMonoidHom
  have hez : e z = -1 := by
    have hz2 : (e z)*(e z)=1 := by
      simpa only [←pow_two,e.orderOf_eq,hz] using pow_orderOf_eq_one (e z)
    have hzne : e z≠1 := by
      intro hh
      have hh' : z=1 := e.injective (hh.trans e.map_one.symm)
      simp [hh'] at hz
    exact (by decide +kernel : ∀ a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      a*a=1 → a≠1 → a = -1) _ hz2 hzne
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp
    (Matrix.SpecialLinearGroup.eq_bot_of_neg_one_not_mem (by decide : (2:ZMod 3)≠0)
      f.ker (by
        intro h
        apply hzρ
        change ρ (e.symm (-1))=1 at h
        rw [←hez,e.symm_apply_apply] at h
        exact h))
  intro a b hab
  apply e.injective
  apply hf
  change ρ (e.symm (e a))=ρ (e.symm (e b))
  simpa only [e.symm_apply_apply] using hab

private theorem core_le_action_kernel :
    (cubicOddCore c t.x).subgroupOf (cubicNormalizer c t.x) ≤
      t.cubicCentralQuotientAction.ker := by
  let D := cubicOddCore c t.x
  let : IsElementaryAbelian 3 (D ⧸ center D) := t.maximal_core_central_quotient_elementary
  intro a ha
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro v
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (center D) v
  change quotientAut _ _ (QuotientGroup.mk' _ v)=QuotientGroup.mk' _ v
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' (center D) ((⟨a,ha⟩:D)*v*(⟨a,ha⟩:D)⁻¹)=_
  rw [map_mul,map_mul,map_inv,mul_comm (QuotientGroup.mk' (center D) (⟨a,ha⟩:D)),
    mul_inv_cancel_right]

private theorem action_kernel_le_cubic_centralizer
    (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : cubicNormalizer c t.x) (ha : a∈t.cubicCentralQuotientAction.ker) :
    (a:G)∈cubicCentralizer c t.x := by
  let D := cubicOddCore c t.x
  let q := QuotientGroup.mk' (center D)
  let α : MulAut D := D.normalizerMonoidHom (inclusion t.cubic_core_normalized a)
  have hfix : _root_.commutator D ≤ α.fixedSubgroup := by
    have hh := α.fixes_commutator_of_central_displacement q
      (by rw [QuotientGroup.ker_mk']) ⊤ (by
        intro v _
        have he := DFunLike.congr_fun ha (q v)
        change quotientAut (center D) α (q v)=q v at he
        simpa only [q,quotientAut_apply_mk] using he)
    simpa only [map_subtype_commutator,←commutator_def] using hh
  have hx : ((t.x:c.H):G)∈(_root_.commutator D).map D.subtype := by
    rw [map_subtype_commutator,t.maximal_core_derived hc]
    exact mem_zpowers _
  obtain ⟨v,hv,hvx⟩ := hx
  have hh := congrArg Subtype.val ((MulAut.mem_fixedSubgroup α v).mp (hfix hv))
  change (a:G)*(v:G)*(a:G)⁻¹=(v:G) at hh
  change (v:G)=((t.x:c.H):G) at hvx
  rw [hvx] at hh
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)

theorem cubicCentralQuotientAction_kernel
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.cubicCentralQuotientAction.ker=
      (cubicOddCore c t.x).subgroupOf (cubicNormalizer c t.x) := by
  apply le_antisymm ?_ t.core_le_action_kernel
  intro a ha
  have haC := t.action_kernel_le_cubic_centralizer hc a ha
  rw [cubic_centralizer_split c t.x t.x_order] at haC
  have hn : c.H₂.map c.H.subtype ≤ normalizer (cubicOddCore c t.x:Set G) := by
    apply le_trans ?_ t.cubic_core_normalized
    rw [t.left_ambient_normalizer]
    exact le_sup_right.trans le_sup_left
  change (a:G)∈(↑(cubicOddCore c t.x⊔c.H₂.map c.H.subtype):Set G) at haC
  rw [coe_mul_of_right_le_normalizer_left _ _ hn] at haC
  obtain ⟨v,hv,y,⟨yH,hyH,rfl⟩,hvy⟩ := haC
  let y₂ : c.H₂ := ⟨yH,hyH⟩
  let yN := t.oppositeInNormalizer y₂
  have hvN : v∈cubicNormalizer c t.x := by
    rw [t.left_ambient_normalizer]
    exact mem_sup_left (mem_sup_left hv)
  have haeq : a=(⟨v,hvN⟩:cubicNormalizer c t.x)*yN := Subtype.ext hvy.symm
  have hyker : t.oppositeCentralAction y₂=1 := by
    change t.cubicCentralQuotientAction yN=1
    have hh : t.cubicCentralQuotientAction a=1 := ha
    rw [haeq,map_mul,
      show t.cubicCentralQuotientAction ⟨v,hvN⟩=1 from t.core_le_action_kernel hv,
      one_mul] at hh
    exact hh
  have hy1 : y₂=1 := t.oppositeCentralAction_injective hc
    (hyker.trans t.oppositeCentralAction.map_one.symm)
  have hyG : (yH:G)=1 := congrArg (fun h:c.H₂=>((h:c.H):G)) hy1
  change (a:G)∈cubicOddCore c t.x
  change v*(yH:G)=(a:G) at hvy
  rw [←hvy,hyG,mul_one]
  exact hv

noncomputable def cubicCentralQuotientCoordinates
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    MulAut (cubicOddCore c t.x ⧸ center (cubicOddCore c t.x)) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) := by
  letI := t.maximal_core_central_quotient_elementary
  exact IsElementaryAbelian.mulAutLinearEquivOfCard _ (t.maximal_core_central_quotient_card hc)

noncomputable def cubicLinearAction (hc : Nat.card (cubicOddCore c t.x)=243) :
    cubicNormalizer c t.x →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  (t.cubicCentralQuotientCoordinates hc).toMonoidHom.comp t.cubicCentralQuotientAction

theorem cubicLinearAction_kernel (hc : Nat.card (cubicOddCore c t.x)=243) :
    (t.cubicLinearAction hc).ker=
      (cubicOddCore c t.x).subgroupOf (cubicNormalizer c t.x) := by
  rw [cubicLinearAction,MonoidHom.ker_comp_of_injective _ _
    (t.cubicCentralQuotientCoordinates hc).injective,t.cubicCentralQuotientAction_kernel hc]

theorem cubicLinearAction_surjective (hc : Nat.card (cubicOddCore c t.x)=243) :
    Function.Surjective (t.cubicLinearAction hc) := by
  apply MonoidHom.surjective_of_card_ker_le_div
  have hDN : cubicOddCore c t.x≤cubicNormalizer c t.x := by
    rw [t.left_ambient_normalizer]
    exact le_sup_left.trans le_sup_left
  rw [t.cubicLinearAction_kernel hc,
    Nat.card_congr (subgroupOfEquivOfLe hDN).toEquiv,
    t.left_ambient_normalizer_card,hc]
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))=48 := by
    rw [Matrix.card_GL_field]; decide
  rw [hGL]

noncomputable def cubicLinearQuotientEquiv (hc : Nat.card (cubicOddCore c t.x)=243) :
    letI := t.left_core_normal_in_cubic_normalizer
    (cubicNormalizer c t.x ⧸ (cubicOddCore c t.x).subgroupOf (cubicNormalizer c t.x)) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  letI := t.left_core_normal_in_cubic_normalizer
  (QuotientGroup.quotientMulEquivOfEq (t.cubicLinearAction_kernel hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (t.cubicLinearAction hc)
      (t.cubicLinearAction_surjective hc))

theorem cubicLinearQuotientEquiv_mk (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : cubicNormalizer c t.x) :
    letI := t.left_core_normal_in_cubic_normalizer
    t.cubicLinearQuotientEquiv hc
      (QuotientGroup.mk' ((cubicOddCore c t.x).subgroupOf (cubicNormalizer c t.x)) a)=
        t.cubicLinearAction hc a := rfl

private theorem coreExtension_le_normalizer :
    t.leftCoreExtension≤cubicNormalizer c t.x := by
  rw [t.left_ambient_normalizer]
  exact sup_le (le_sup_left.trans le_sup_left)
    ((zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
      (le_sup_right.trans le_sup_left))

/-- The full original Borel maps to the normalizer of the marked cubic image. -/
theorem cubicLinearAction_borel_image (hc : Nat.card (cubicOddCore c t.x)=243) :
    (t.leftCubicBorel.subgroupOf (cubicNormalizer c t.x)).map (t.cubicLinearAction hc)=
      normalizer (((t.leftCoreExtension.subgroupOf (cubicNormalizer c t.x)).map
        (t.cubicLinearAction hc)):Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) := by
  let N := cubicNormalizer c t.x
  let S := t.leftCoreExtension.subgroupOf N
  let f := t.cubicLinearAction hc
  have hk : f.ker≤S := by
    rw [t.cubicLinearAction_kernel hc]
    exact fun _ h=>mem_sup_left h
  have hn : t.leftCubicBorel.subgroupOf N=normalizer (S:Set N) := by
    rw [←subgroupOf_normalizer_eq t.coreExtension_le_normalizer]
    ext a
    change (a:G)∈t.leftCubicBorel ↔ (a:G)∈normalizer (t.leftCoreExtension:Set G)
    rw [←t.maximal_leftCoreExtension_normalizer hc]
    exact and_iff_right a.property
  rw [hn]
  apply (comap_injective (t.cubicLinearAction_surjective hc))
  rw [comap_map_eq_self (hk.trans S.le_normalizer),
    comap_normalizer_eq_of_surjective _ (t.cubicLinearAction_surjective hc),
    comap_map_eq_self hk]

private theorem cubicLinearAction_image_card (hc : Nat.card (cubicOddCore c t.x)=243)
    (K : Subgroup G) (hDK : cubicOddCore c t.x≤K) (hKN : K≤cubicNormalizer c t.x) :
    243 * Nat.card ((K.subgroupOf (cubicNormalizer c t.x)).map (t.cubicLinearAction hc))=
      Nat.card K := by
  let N := cubicNormalizer c t.x
  let C := (cubicOddCore c t.x).subgroupOf N
  let A := K.subgroupOf N
  have hCA : C≤A := fun _ h=>hDK h
  have hD : Nat.card C=243 :=
    (Nat.card_congr (subgroupOfEquivOfLe (hDK.trans hKN)).toEquiv).trans hc
  have hA : Nat.card A=Nat.card K := Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv
  have hh := (C.subgroupOf A).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hCA).toEquiv,hD,hA] at hh
  change 243*C.relIndex A=Nat.card K at hh
  have he : C=(t.cubicLinearAction hc).ker := (t.cubicLinearAction_kernel hc).symm
  rw [he,relIndex_ker] at hh
  exact hh

/-- The marked local Sylow has a cubic image in the actual linear quotient. -/
theorem cubicLinearAction_sylow_image_card (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card ((t.leftCoreExtension.subgroupOf (cubicNormalizer c t.x)).map
      (t.cubicLinearAction hc))=3 := by
  have hh := t.cubicLinearAction_image_card hc t.leftCoreExtension le_sup_left
    t.coreExtension_le_normalizer
  rw [t.maximal_leftCoreExtension_card hc] at hh
  omega

/-- The entire order2916 middle has its actual order12 Borel image. -/
theorem cubicLinearAction_borel_image_card (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card ((t.leftCubicBorel.subgroupOf (cubicNormalizer c t.x)).map
      (t.cubicLinearAction hc))=12 := by
  have hh := t.cubicLinearAction_image_card hc t.leftCubicBorel
    (le_sup_left.trans le_sup_left) t.leftCubicBorel_le
  rw [(t.maximal_leftCubicBorel_split hc).2.2.2] at hh
  omega

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
