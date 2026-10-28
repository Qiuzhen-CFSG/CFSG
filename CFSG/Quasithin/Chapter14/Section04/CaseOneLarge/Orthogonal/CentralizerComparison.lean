module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Actions
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Source
public import Theory.GroupTheory.PResidual.Restriction

/-!
# The selected centralizer and its literal residual image

Rank-four involution displacement on the eight-dimensional central quotient
has equal image and kernel. Thus a coset centralizing i* can be corrected
by an element of U to centralize i modulo Z(U). This proves the centralizer
comparison in 14.4.9 with the original H/O₂(H) quotient map.

The commutator homomorphism from that preimage into ⟨z⟩ kills its
two-residual. Consequently K₀=O²(C_H(i)) has image exactly the two-residual
of C_{H*}(i*). No ordinary-centralizer surjectivity is needed.

The original selection theorem is applied with the same x=gkg. It now
supplies the moved order, exchanged action, centralizer comparison and
residual image together. The final consumer discharges the exchanged-action
and centralizer-comparison premises of the existing orthogonal exclusion.
The compatible diagonal A₅ module and component identification remain to
be constructed; this module does not assert the full orthogonal exclusion.

Source: Aschbacher--Smith, Lemma 14.4.9, printed p.1010;
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Orthogonal CoreGeometry
open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

omit [Finite G] in
private theorem mem_preimage_of_commutator (H Z : Subgroup G)
    (hZH : Z ≤ H) (hHZ : H ≤ normalizer (Z : Set G))
    (b i : H) (hc : ⁅(b:G),(i:G)⁆ ∈ Z) :
    (b:G) ∈ commutatorPreimage H (zpowers (i:G)) Z := by
  let ZH := Z.subgroupOf H
  let : ZH.Normal := normal_subgroupOf_of_le_normalizer hHZ
  let q := QuotientGroup.mk' ZH
  let A := (centralizer ({q i} : Set (H ⧸ ZH))).comap q
  have hb : b ∈ A := by
    apply mem_centralizer_singleton_iff.mpr
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hc
  have hAZ : ⁅A,zpowers i⁆ ≤ ZH := by
    rw [←QuotientGroup.ker_mk' ZH,←Subgroup.map_eq_bot_iff]
    rw [map_commutator,commutator_eq_bot_iff_le_centralizer,MonoidHom.map_zpowers,
      zpowers_eq_closure,centralizer_closure]
    exact map_comap_le (f:=q) (centralizer ({q i} : Set (H ⧸ ZH)))
  have hm : ⁅A.map H.subtype,zpowers (i:G)⁆ ≤ Z := by
    have hh := map_mono (f:=H.subtype) hAZ
    rw [map_commutator,MonoidHom.map_zpowers] at hh
    simpa only [ZH,map_subgroupOf_eq_of_le hZH,Subgroup.subtype_apply] using hh
  exact le_commutatorPreimage (map_subtype_le A) hm (mem_map_of_mem H.subtype hb)

private theorem fixed_mem_range (t : Binary.V ≃ₗ[ZMod 2] Binary.V)
    (ht : t ^ 2 = 1)
    (hd : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 4)
    (v : Binary.V) (hv : t v = v) :
    ∃ w : Binary.V, t w - w = v := by
  let f : Binary.V →ₗ[ZMod 2] Binary.V := t.toLinearMap - LinearMap.id
  have hle : f.range ≤ f.ker := by
    rintro _ ⟨w,rfl⟩
    change t (t w - w) - (t w - w) = 0
    have htw : t (t w) = w := LinearEquiv.congr_fun ht w
    rw [map_sub,htw]
    apply sub_eq_zero.mpr
    exact sub_eq_sub_iff_add_eq_add.mpr (by
      apply Matrix.ext
      intro j k
      exact (CharTwo.add_self_eq_zero (w j k)).trans
        (CharTwo.add_self_eq_zero (t w j k)).symm)
  have hr := f.finrank_range_add_finrank_ker
  rw [Binary.finrank_binary] at hr
  have heq : f.range = f.ker := Submodule.eq_of_le_of_finrank_le hle (by
    change finrank (ZMod 2) f.range = 4 at hd
    omega)
  have hm : v ∈ f.ker := sub_eq_zero.mpr hv
  rw [←heq] at hm
  exact hm

omit [Finite G] in
/-- Full involution displacement lifts every quotient-centralizing coset to
an element centralizing i modulo Z(U). This is the literal comparison used
in the normalizer-Sylow argument, rather than ordinary centralizer surjectivity. -/
theorem centralizer_comparison_of_moved_rank
    (H U : Subgroup G) (m : ExchangedModel.CaseThreeAction H U)
    (hcore : H.pCoreIn 2 = U) (z : G) (hZ : (center U).map U.subtype = zpowers z)
    (hHZ : H ≤ normalizer (zpowers z : Set G))
    (i : H) (hio : orderOf (i:G) = 2)
    (hd : finrank (ZMod 2) (LinearMap.range ((m.action i).toLinearMap - LinearMap.id)) = 4) :
    ((commutatorPreimage H (zpowers (i:G)) (zpowers z)).subgroupOf H).map
      (QuotientGroup.mk' (pCore 2 H)) =
      centralizer ({QuotientGroup.mk' (pCore 2 H) i} : Set (H ⧸ pCore 2 H)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hUH : U ≤ H := by
    have hh : H.pCoreIn 2 ≤ H := map_subtype_le _
    rwa [hcore] at hh
  have hZU : zpowers z ≤ U := by rw [←hZ]; exact map_subtype_le _
  have hqU (u : H) : q u = 1 ↔ (u:G) ∈ U := by
    rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    constructor
    · intro hu
      rw [←hcore]
      exact mem_map_of_mem H.subtype hu
    · intro hu
      rw [←hcore] at hu
      obtain ⟨v,hv,he⟩ := hu
      exact (show v = u from Subtype.ext he) ▸ hv
  have hi2 : (i:G)^2 = 1 := hio ▸ pow_orderOf_eq_one (i:G)
  have hii : (i:G)⁻¹ = (i:G) := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hi2)
  have himul : (i:G)*(i:G) = 1 := by simpa only [pow_two] using hi2
  apply le_antisymm
  · rintro _ ⟨b,hb,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply (hqU _).mpr
    exact hZU ((commutator_commutatorPreimage_le H (zpowers (i:G)) (zpowers z) hHZ)
      (commutator_mem_commutator hb (mem_zpowers (i:G))))
  · intro y hy
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) y
    have hc : ⁅(h:G),(i:G)⁆ ∈ U := by
      apply (hqU ⁅h,i⁆).mp
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_singleton_iff.mp hy)
    let c : U := ⟨⁅(h:G),(i:G)⁆,hc⟩
    have hci : U.normalizerMonoidHom ⟨i,m.normalizes i.property⟩ c = c⁻¹ := by
      apply Subtype.ext
      change (i:G)*⁅(h:G),(i:G)⁆*(i:G)⁻¹ = ⁅(h:G),(i:G)⁆⁻¹
      simp only [commutatorElement_def,mul_inv_rev,inv_inv,hii,mul_assoc,himul,mul_one]
    have hfix : m.action i (m.projection c).toAdd = (m.projection c).toAdd := by
      have he := m.projection_equivariant i c
      rw [hci,map_inv] at he
      exact (congrArg Multiplicative.toAdd he).symm.trans (by
        apply Matrix.ext
        intro j k
        exact CharTwo.neg_eq _)
    have ht : (m.action i)^2 = 1 := by
      rw [←map_pow,show i^2=1 from Subtype.ext hi2,map_one]
    obtain ⟨w,hw⟩ := fixed_mem_range (m.action i) ht hd _ hfix
    obtain ⟨u,hu⟩ := m.projection_surjective (Multiplicative.ofAdd w)
    let r : U := ⟨⁅(u:G),(i:G)⁆,m.comm_mem i u⟩
    let b : H := ⟨(u:G)*(h:G),H.mul_mem (hUH u.property) h.property⟩
    let v : U := u*c*u⁻¹*r
    have hv : (v:G) = ⁅(b:G),(i:G)⁆ := by
      change (u:G)*⁅(h:G),(i:G)⁆*(u:G)⁻¹*⁅(u:G),(i:G)⁆ = ⁅(u:G)*(h:G),(i:G)⁆
      simp only [commutatorElement_def]
      group
    have hp : m.projection v = 1 := by
      apply Multiplicative.toAdd.injective
      change (m.projection (u*c*u⁻¹*r)).toAdd = 0
      simp only [map_mul,map_inv,toAdd_mul,toAdd_inv]
      rw [show m.projection r = Multiplicative.ofAdd
        ((m.projection u).toAdd - m.action i (m.projection u).toAdd) from
          m.projection_commutator i u,hu]
      change w + (m.projection c).toAdd + -w + (w - m.action i w) = 0
      rw [←hw]
      abel
    have hvZ : v ∈ center U := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply m.coordinates.injective
      exact hp.trans m.coordinates.map_one.symm
    have hb : (b:G) ∈ commutatorPreimage H (zpowers (i:G)) (zpowers z) :=
      mem_preimage_of_commutator H (zpowers z) (hZU.trans hUH) hHZ b i
        (hZ ▸ (show ⁅(b:G),(i:G)⁆ ∈ (center U).map U.subtype from ⟨v,hvZ,hv⟩))
    refine ⟨b,hb,?_⟩
    change q ((⟨u,hUH u.property⟩ : H)*h) = q h
    rw [map_mul,(hqU _).mpr u.property,one_mul]

/-- The two-residual removes the central error in C_H(i mod ⟨z⟩).
The commutator map to the central group ⟨z⟩ has two-group image. -/
theorem diagonalResidual_eq_mod_center (H : Subgroup G) (z i : G)
    (hz : orderOf z = 2) (hH : H ≤ centralizer ({z} : Set G)) :
    diagonalResidual H i =
      (pResidual 2 (commutatorPreimage H (zpowers i) (zpowers z))).map
        (commutatorPreimage H (zpowers i) (zpowers z)).subtype := by
  let P := commutatorPreimage H (zpowers i) (zpowers z)
  let C := H ⊓ centralizer ({i} : Set G)
  have hPH : P ≤ H := commutatorPreimage_le _ _ _
  have hHZ : H ≤ centralizer (zpowers z : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using hH
  have hPN : H ≤ normalizer (zpowers z : Set G) :=
    hHZ.trans (Subgroup.centralizer_le_normalizer _)
  have hc (p : P) : ⁅(p:G),i⁆ ∈ zpowers z :=
    (commutator_commutatorPreimage_le H (zpowers i) (zpowers z) hPN)
      (commutator_mem_commutator p.property (mem_zpowers i))
  let f : P →* zpowers z := {
    toFun := fun p => ⟨⁅(p:G),i⁆,hc p⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅(a:G)*(b:G),i⁆ = ⁅(a:G),i⁆ * ⁅(b:G),i⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        ←hHZ (hPH a.property) _ (hc b),mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm (⟨⁅(b:G),i⁆,hc b⟩ : zpowers z)
        (⟨⁅(a:G),i⁆,hc a⟩ : zpowers z)) }
  have hp : IsPGroup 2 (zpowers z) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p:=2) (hz ▸ pow_orderOf_eq_one z)).isPGroup 2 _
  have hRP : (pResidual 2 P).map P.subtype ≤ C := by
    rintro _ ⟨p,hp',rfl⟩
    refine ⟨hPH p.property,mem_centralizer_singleton_iff.mpr ?_⟩
    apply commutatorElement_eq_one_iff_mul_comm.mp
    exact congrArg Subtype.val (pResidual_le_ker_of_isPGroup 2 f hp hp')
  have hCP : C ≤ P := by
    apply le_commutatorPreimage inf_le_left
    have hC : C ≤ centralizer (zpowers i : Set G) := by
      simpa only [zpowers_eq_closure,centralizer_closure] using
        (inf_le_right : C ≤ centralizer ({i} : Set G))
    rw [commutator_eq_bot_iff_le_centralizer.mpr hC]
    exact bot_le
  exact embedded_pResidual_eq_of_le_of_residual_le 2 hCP hRP

/-- The actual diagonal residual maps to the two-residual of the quotient
centralizer. Ordinary centralizer surjectivity is not required. -/
theorem diagonalResidual_image_of_comparison (H : Subgroup G) (z : G) (i : H)
    (hz : orderOf z = 2) (hH : H ≤ centralizer ({z} : Set G))
    (hcompare : ((commutatorPreimage H (zpowers (i:G)) (zpowers z)).subgroupOf H).map
      (QuotientGroup.mk' (pCore 2 H)) =
      centralizer ({QuotientGroup.mk' (pCore 2 H) i} : Set (H ⧸ pCore 2 H))) :
    ((diagonalResidual H (i:G)).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) =
      (pResidual 2 (centralizer ({QuotientGroup.mk' (pCore 2 H) i} :
        Set (H ⧸ pCore 2 H)))).map
          (centralizer ({QuotientGroup.mk' (pCore 2 H) i} : Set (H ⧸ pCore 2 H))).subtype := by
  let P := commutatorPreimage H (zpowers (i:G)) (zpowers z)
  have hPH : P ≤ H := commutatorPreimage_le _ _ _
  have hr := diagonalResidual_eq_mod_center H z (i:G) hz hH
  have hs : (diagonalResidual H (i:G)).subgroupOf H =
      (pResidual 2 (P.subgroupOf H)).map (P.subgroupOf H).subtype := by
    apply (map_injective H.subtype_injective)
    rw [map_subgroupOf_eq_of_le (show diagonalResidual H (i:G) ≤ H from
      (map_subtype_le _).trans inf_le_left),map_embedded_pResidual,
      map_subgroupOf_eq_of_le hPH]
    exact hr
  rw [hs,map_embedded_pResidual,hcompare]

/-- The original selected involution satisfies the centralizer comparison
of 14.4.9 with the unchanged quotient map and the original central line. -/
theorem source_orthogonal_centralizer_comparison (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (z : G) (hzp : F.Vi 1 = zpowers z)
    (hH : F.H = centralizer ({z} : Set G))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) (hio : orderOf (i:G) = 2) :
    ((commutatorPreimage F.H (zpowers (i:G)) (zpowers z)).subgroupOf F.H).map
      (QuotientGroup.mk' (pCore 2 F.H)) =
      centralizer ({QuotientGroup.mk' (pCore 2 F.H) i} : Set (F.H ⧸ pCore 2 F.H)) := by
  let m := source_orthogonal_action d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he
  have hcore := (source_orthogonal_twoCore d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he).2
  have hHZ : F.H ≤ normalizer (zpowers z : Set G) := by
    rw [hH]
    simpa only [zpowers_eq_closure,centralizer_closure] using
      (centralizer_le_normalizer (zpowers z : Set G))
  exact centralizer_comparison_of_moved_rank F.H F.U m hcore z (hZ.trans hzp) hHZ i hio
    (source_orthogonal_moved_rank d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he i hiX hiV hio).1

/-- Actual application to the original orthogonal exclusion. The exchanged
action, core equality, order and centralizer comparison are discharged here.
Only the selected diagonal module and its component identification remain explicit. -/
theorem source_selected_contradiction_of_diagonal (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (z x : G) (hz : orderOf z = 2) (hzp : F.Vi 1 = zpowers z)
    (hH : F.H = centralizer ({z} : Set G))
    (hiT : conjugateElement z x ∈ T) (hout : conjugateElement z x ∉ F.U)
    (hiX : conjugateElement z x ∈ F.X g)
    (hiV : conjugateElement z x ∉ centralizer (V : Set G))
    (hKU : diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (F.U : Set G))
    (m : MovedCoreModel F.U
      (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x))
      (conjugateElement z x) hKU)
    (components : QuotientModel.SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
        ⟨conjugateElement z x,(hH ▸ (show (T : Subgroup G) ≤ F.H from F.invariant 1)) hiT⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x)).subgroupOf
        (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) :
    False := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1
  have hc := (source_orthogonal_twoCore d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he).2
  have hsize := (source_orthogonal_flag_reduction d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he).1
  have hi : orderOf (conjugateElement z x) = 2 := by
    simpa only [conjugateElement,MulEquiv.orderOf_eq] using hz
  have hcompare : ∀ hiH : conjugateElement z x ∈ F.H,
      ((commutatorPreimage F.H (zpowers (conjugateElement z x)) (zpowers z)).subgroupOf F.H).map
        (QuotientGroup.mk' (pCore 2 F.H)) =
        centralizer ({QuotientGroup.mk' (pCore 2 F.H) ⟨conjugateElement z x,hiH⟩} :
          Set (F.H ⧸ pCore 2 F.H)) := by
    intro hiH
    exact source_orthogonal_centralizer_comparison d earlier hq chosen
      structural alternatives F hne hZ g hg hgP hgH κ e he z hzp hH
      ⟨conjugateElement z x,hiH⟩ hiX hiV hi
  rw [hH] at hcompare
  exact source_selected_configuration_contradiction d.qtke F.U T z x hz
    (hZ.trans hzp) (hH ▸ hc) hsize (hH ▸ (show (T : Subgroup G) ≤ F.H from F.invariant 1)) hiT hout hKU m
    (source_orthogonal_exchanged_action d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he z x hH) components (hcompare _)

/-- The original selection now carries its actual moved image of order
sixteen, the exchanged action, centralizer comparison and exact residual
image, with the same x=gkg. -/
theorem source_orthogonal_selected_actions (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    F.H.pCoreIn 2 = F.U ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ k : G, k ∈ (pResidual 2 F.H).map F.H.subtype ∧
          let x := g*k*g
          let i := conjugateElement z x
          orderOf i = 2 ∧ i ∈ F.X g ∧ i ∈ T ∧ i ∉ F.U ∧
          i ∉ centralizer (V : Set G) ∧
          Nat.card (movedImage F.U i) = 16 ∧
          Nonempty (ExchangedModel.CaseThreeAction
            (centralizer ({i} : Set G)) (conjugateCore F.U x)) ∧
          ∃ hiH : i ∈ F.H,
            QuotientGroup.mk' (pCore 2 F.H) ⟨i,hiH⟩ ∉
              (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H)) ∧
            ((commutatorPreimage F.H (zpowers i) (zpowers z)).subgroupOf F.H).map
              (QuotientGroup.mk' (pCore 2 F.H)) =
              centralizer ({QuotientGroup.mk' (pCore 2 F.H) ⟨i,hiH⟩} :
                Set (F.H ⧸ pCore 2 F.H)) ∧
            ((diagonalResidual F.H i).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H)) =
              (pResidual 2 (centralizer ({QuotientGroup.mk' (pCore 2 F.H) ⟨i,hiH⟩} :
                Set (F.H ⧸ pCore 2 F.H)))).map
                  (centralizer ({QuotientGroup.mk' (pCore 2 F.H) ⟨i,hiH⟩} :
                    Set (F.H ⧸ pCore 2 F.H))).subtype := by
  obtain ⟨hcore,z,hzo,hzp,hH,k,hk,hio,hiX,hiT,hiU,hiV⟩ :=
    source_orthogonal_selected_involution d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  have hiH := F.invariant 1 hiT
  have hm := (source_orthogonal_moved_rank d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he ⟨_,hiH⟩ hiX hiV hio).2
  refine ⟨hcore,z,hzo,hzp,hH,k,hk,hio,hiX,hiT,hiU,hiV,hm,⟨?_⟩,hiH,?_,?_,?_⟩
  · exact source_orthogonal_exchanged_action d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he z (g*k*g) hH
  · intro hiK
    exact hiV (source_orthogonal_residual_fixes_seed d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he ⟨_,hiH⟩ hiX hiK)
  · exact source_orthogonal_centralizer_comparison d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he z hzp hH ⟨_,hiH⟩ hiX hiV hio
  · exact diagonalResidual_image_of_comparison F.H z ⟨_,hiH⟩ hzo hH.le
      (source_orthogonal_centralizer_comparison d earlier hq chosen structural alternatives
        F hne hZ g hg hgP hgH κ e he z hzp hH ⟨_,hiH⟩ hiX hiV hio)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
