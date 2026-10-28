module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.ModelDefinitions
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Recognition

/-!
# Transport and assembly for the second-centralizer residual

The literal inclusions identify K ∩ L with C_L(t), and identify its embedded
O² with X. Transport through the marked A₈ equivalence gives the concrete
residual model without changing either inclusion defining X.

A model Sylow subgroup with z in its center gives control of two-element
fusion in K ∩ L. Once transfer identifies J ∩ L with X, the supplement
K = J(K ∩ L) replaces a K-conjugator by a J-conjugator. Thus local involution
fusion and the four-group centralizer pass to J, and the existing recognition
theorem gives A₅. The finite-model facts and transfer equality remain explicit
premises here; this module does not yet prove the unconditional source result.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, and *Sporadic Groups* 7.3–7.4.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
open Subgroup
namespace InvolutionData
variable {G : Type*} [Group G] {z : G} {L : Subgroup G} (d : InvolutionData z L)

/-- Reassociate the two actual inclusions, without changing the ambient element. -/
def localCentralizerEquiv : d.M ≃* centralizer ({d.t} : Set L) where
  toFun a := ⟨⟨(a.val : G), a.property⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp a.val.property))⟩
  invFun a := ⟨⟨(a.val : G), mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.property))⟩,
    a.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The marked A₈ equivalence restricted to the actual local centralizer. -/
def localModelEquiv : d.M ≃* ResidualModel.C :=
  d.localCentralizerEquiv.trans
    { toFun := fun a => ⟨d.equiv a.val, mem_centralizer_singleton_iff.mpr (by
        have he := congrArg d.equiv (mem_centralizer_singleton_iff.mp a.property)
        simpa only [map_mul, t, d.equiv.apply_symm_apply] using he)⟩
      invFun := fun a => ⟨d.equiv.symm a.val, mem_centralizer_singleton_iff.mpr (by
        apply d.equiv.injective
        simpa only [map_mul, t, d.equiv.apply_symm_apply] using
          mem_centralizer_singleton_iff.mp a.property)⟩
      left_inv := fun a => Subtype.ext (d.equiv.symm_apply_apply a.val)
      right_inv := fun a => Subtype.ext (d.equiv.apply_symm_apply a.val)
      map_mul' := fun a b => Subtype.ext (map_mul d.equiv a.val b.val) }

theorem localModelEquiv_apply (a : d.M) :
    (d.localModelEquiv a : Eight) = d.equiv ⟨(a.val : G), a.property⟩ := rfl

/-- The embedded residual of K ∩ L is exactly the two-inclusion definition of X. -/
theorem map_localResidual :
    ((pResidual 2 d.M).map d.M.subtype).map d.K.subtype = d.X := by
  rw [X, ← map_pResidual 2 d.localCentralizerEquiv]
  simp only [map_map]
  rfl

/-- The local residual and its literal image X. -/
noncomputable def residualLocalEquiv : pResidual 2 d.M ≃* d.X :=
  ((pResidual 2 d.M).equivMapOfInjective
    (d.K.subtype.comp d.M.subtype)
    (d.K.subtype_injective.comp d.M.subtype_injective)).trans
    (MulEquiv.subgroupCongr (by rw [← map_map]; exact d.map_localResidual))

/-- Transport X to the actual residual of the eight-point centralizer. -/
noncomputable def residualModelEquiv : d.X ≃* ResidualModel.R :=
  d.residualLocalEquiv.symm.trans
    (((d.localModelEquiv.subgroupMap (pResidual 2 d.M)).trans
      (MulEquiv.subgroupCongr (map_pResidual 2 d.localModelEquiv))).trans
      ((pResidual 2 ResidualModel.C).equivMapOfInjective
        ResidualModel.C.subtype ResidualModel.C.subtype_injective))

theorem residualModelEquiv_apply (a : d.X) :
    (d.residualModelEquiv a : Eight) = d.equiv ⟨(a : G), d.X_le_L a.property⟩ := by
  obtain ⟨b, rfl⟩ := d.residualLocalEquiv.surjective a
  simp only [residualModelEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

/-- The intrinsic transfer equality in K gives the source equality in G. -/
theorem intersection_of_residual_restriction
    (hres : (pResidual 2 d.K) ⊓ d.M = (pResidual 2 d.M).map d.M.subtype) :
    d.J ⊓ L = d.X := by
  rw [← d.map_localResidual, ← hres]
  ext a
  constructor
  · rintro ⟨ha, haL⟩
    obtain ⟨b, hb, rfl⟩ := mem_map.mp ha
    exact mem_map.mpr ⟨b, ⟨hb, haL⟩, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨mem_map.mpr ⟨b, hb.1, rfl⟩, hb.2⟩

variable [Finite G]

omit [Finite G] in
/-- Unique fixation restricts from G/L to the actual K-coset action. -/
theorem local_unique_fixed_coset (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) :
    ∃! q : d.K ⧸ d.M, (⟨z, d.z_mem_K⟩ : d.K) • q = q := by
  apply UniqueFixedCoset.unique_of_fusion_and_centralizer (M := d.M)
    (x := (⟨z, d.z_mem_K⟩ : d.K)) (show _ from d.z_mem)
  · intro a ha
    apply hCL
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))
  · intro k hk
    have hkL : (k : G) ∈ L := UniqueFixedCoset.transporter_mem d.z_mem
      (d.unique_fixed_coset hz hCL) hk
    exact ⟨k, hkL, rfl⟩

/-- Promote the model central Sylow subgroup using the proved odd local index. -/
theorem exists_central_sylow_K (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (hmodel : ∃ T : Sylow 2 ResidualModel.C,
      ResidualModel.z ∈ (T : Subgroup ResidualModel.C) ∧
      ∀ a ∈ (T : Subgroup ResidualModel.C), Commute ResidualModel.z a) :
    ∃ T : Sylow 2 d.K, (T : Subgroup d.K) ≤ d.M ∧
      (⟨z, d.z_mem_K⟩ : d.K) ∈ (T : Subgroup d.K) ∧
      ∀ a ∈ (T : Subgroup d.K), Commute (⟨z, d.z_mem_K⟩ : d.K) a := by
  obtain ⟨T, hzT, hcT⟩ := hmodel
  let S : Sylow 2 d.M := T.mapSurjective (f := d.localModelEquiv.symm.toMonoidHom)
    d.localModelEquiv.symm.surjective
  let U : Subgroup d.K := (S : Subgroup d.M).map d.M.subtype
  have hU : IsPGroup 2 U := S.isPGroup'.map d.M.subtype
  have hi : ¬ 2 ∣ U.index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul S.not_dvd_index (d.local_index_odd hz hCL).not_two_dvd_nat
  have he : d.localModelEquiv (⟨⟨z, d.z_mem_K⟩, d.z_mem⟩ : d.M) = ResidualModel.z :=
    Subtype.ext d.z_image
  have he' : d.localModelEquiv.symm ResidualModel.z =
      (⟨⟨z, d.z_mem_K⟩, d.z_mem⟩ : d.M) := d.localModelEquiv.symm_apply_eq.mpr he.symm
  refine ⟨hU.toSylow hi, map_subtype_le _, ?_, ?_⟩
  · exact mem_map.mpr ⟨⟨⟨z, d.z_mem_K⟩, d.z_mem⟩,
      mem_map.mpr ⟨ResidualModel.z, hzT, he'⟩, rfl⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_map.mp ha
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hb
    change (⟨z, d.z_mem_K⟩ : d.K) * d.M.subtype (d.localModelEquiv.symm c) =
      d.M.subtype (d.localModelEquiv.symm c) * ⟨z, d.z_mem_K⟩
    apply Subtype.ext
    have hh := congrArg (fun a : d.M => (a.val : G))
      ((hcT c hc).map d.localModelEquiv.symm).eq
    simpa only [Subgroup.coe_mul, Subgroup.subtype_apply, he'] using hh

/-- The precise fusion-control hypothesis needed by the transfer step. -/
theorem local_two_element_fusion (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (hmodel : ∃ T : Sylow 2 ResidualModel.C,
      ResidualModel.z ∈ (T : Subgroup ResidualModel.C) ∧
      ∀ a ∈ (T : Subgroup ResidualModel.C), Commute ResidualModel.z a)
    {a b : d.K} (ha : a ∈ d.M) (hb : b ∈ d.M)
    (hap : IsPGroup 2 (zpowers a)) (hab : IsConj a b) :
    ∃ m ∈ d.M, m * a * m⁻¹ = b := by
  obtain ⟨T, hTM, hzT, hcT⟩ := d.exists_central_sylow_K hz hCL hmodel
  exact UniqueFixedCoset.p_element_fusion T hTM hzT hcT
    (d.local_unique_fixed_coset hz hCL) ha hb hap hab

/-- The residual supplement lets the conjugator be chosen in J itself. -/
theorem involution_conjugate_into_X (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (htransfer : d.J ⊓ L = d.X) (u : d.J) (hu : orderOf u = 2) :
    ∃ j : d.J, (↑(j * u * j⁻¹) : G) ∈ d.X := by
  let uk : d.K := ⟨(u : G), d.J_le_K u.property⟩
  have huk : orderOf uk = 2 := (Subgroup.orderOf_coe uk).symm.trans
    ((Subgroup.orderOf_coe u).trans hu)
  obtain ⟨k, hk⟩ := d.involution_conjugate_into_M hz hCL uk huk
  obtain ⟨T, hT⟩ := d.exists_sylow_K_le_M hz hCL
  have hs : d.M ⊔ pResidual 2 d.K = ⊤ := by
    rw [sup_comm]
    exact top_unique ((pResidual_sup_sylow_eq_top T).ge.trans (sup_le_sup_left hT _))
  obtain ⟨m, hm, j, hj, he⟩ := mem_sup_of_normal_right.mp
    (show k ∈ d.M ⊔ pResidual 2 d.K by rw [hs]; trivial)
  let jJ : d.J := ⟨(j : G), mem_map.mpr ⟨j, hj, rfl⟩⟩
  refine ⟨jJ, ?_⟩
  rw [← htransfer]
  refine ⟨(jJ * u * jJ⁻¹).property, ?_⟩
  have hmem : j * uk * j⁻¹ ∈ d.M := by
    have hh := d.M.mul_mem (d.M.mul_mem (d.M.inv_mem hm) hk) hm
    rw [← he] at hh
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel, mul_one] using hh
  exact hmem

/-- A single involution class in X becomes a single involution class in J. -/
theorem X_involutions_conjugate_in_J (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (htransfer : d.J ⊓ L = d.X) (hiX : (d.i : G) ∈ d.X)
    (hfusion : ∀ a : d.X, orderOf a = 2 →
      IsConj a (⟨(d.i : G), hiX⟩ : d.X)) :
    ∀ a : d.J, orderOf a = 2 → IsConj a (⟨(d.i : G), d.X_le_J hiX⟩ : d.J) := by
  intro a ha
  obtain ⟨j, hj⟩ := d.involution_conjugate_into_X hz hCL htransfer a ha
  let b : d.X := ⟨(↑(j * a * j⁻¹) : G), hj⟩
  have hb : orderOf b = 2 := by
    exact (Subgroup.orderOf_coe b).symm.trans
      ((Subgroup.orderOf_coe (j * a * j⁻¹)).trans (((MulAut.conj j).orderOf_eq a).trans ha))
  have hf := (inclusion d.X_le_J).map_isConj (hfusion b hb)
  exact (isConj_iff.mpr ⟨j, rfl⟩).trans hf

omit [Finite G] in
/-- The marked centralizer containment is an actual isomorphism of centralizers. -/
def centralizerInXEquiv (hCL : Centralizer z ≤ L)
    (htransfer : d.J ⊓ L = d.X) (hiX : (d.i : G) ∈ d.X) :
    centralizer ({⟨(d.i : G), d.X_le_J hiX⟩} : Set d.J) ≃*
      centralizer ({⟨(d.i : G), hiX⟩} : Set d.X) where
  toFun a := ⟨⟨(a.val : G), d.J_centralizer_i_le_X hCL htransfer
    ⟨a.val.property, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.property))⟩⟩,
    mem_centralizer_singleton_iff.mpr (Subtype.ext
      (congrArg (fun v : d.J => (v : G)) (mem_centralizer_singleton_iff.mp a.property)))⟩
  invFun a := ⟨⟨(a.val : G), d.X_le_J a.val.property⟩,
    mem_centralizer_singleton_iff.mpr (Subtype.ext
      (congrArg (fun v : d.X => (v : G)) (mem_centralizer_singleton_iff.mp a.property)))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
/-- Transport the literal mark `(45)(67)`, not merely its conjugacy class. -/
theorem i_mem_X_of_model (hi : i8 ∈ ResidualModel.R) : (d.i : G) ∈ d.X := by
  let a : d.X := d.residualModelEquiv.symm ⟨i8, hi⟩
  have he : d.equiv ⟨(a : G), d.X_le_L a.property⟩ = i8 :=
    (d.residualModelEquiv_apply a).symm.trans
      (congrArg Subtype.val (d.residualModelEquiv.apply_symm_apply ⟨i8, hi⟩))
  have he' : (a : G) = (d.i : G) := congrArg Subtype.val
    (d.equiv.injective (he.trans (d.equiv.apply_symm_apply i8).symm))
  exact he' ▸ a.property

omit [Finite G] in
theorem residualModelEquiv_i (hi : i8 ∈ ResidualModel.R) :
    d.residualModelEquiv ⟨(d.i : G), d.i_mem_X_of_model hi⟩ = ⟨i8, hi⟩ := by
  apply Subtype.ext
  rw [d.residualModelEquiv_apply]
  exact d.equiv.apply_symm_apply i8

/-- Assemble the residual contract from transfer and finite-model facts. -/
theorem residualFacts_of_model_and_intersection
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (htransfer : d.J ⊓ L = d.X)
    (hcard : Nat.card ResidualModel.R = 12) (hi : i8 ∈ ResidualModel.R)
    (hfusion : ∀ a : ResidualModel.R, orderOf a = 2 →
      IsConj a (⟨i8, hi⟩ : ResidualModel.R))
    (hcentralizer : Nonempty
      (centralizer ({⟨i8, hi⟩} : Set ResidualModel.R) ≃* DihedralGroup 2)) :
    ResidualFacts d := by
  let iX : d.X := ⟨(d.i : G), d.i_mem_X_of_model hi⟩
  have he : d.residualModelEquiv.symm ⟨i8, hi⟩ = iX :=
    d.residualModelEquiv.symm_apply_eq.mpr (d.residualModelEquiv_i hi).symm
  have hfx : ∀ a : d.X, orderOf a = 2 → IsConj a iX := by
    intro a ha
    have hh := d.residualModelEquiv.symm.toMonoidHom.map_isConj
      (hfusion (d.residualModelEquiv a) ((d.residualModelEquiv.orderOf_eq a).trans ha))
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, he] using hh
  refine ⟨htransfer, (Nat.card_congr d.residualModelEquiv.toEquiv).trans hcard,
    d.X_le_J (d.i_mem_X_of_model hi),
    d.X_involutions_conjugate_in_J hz hCL htransfer (d.i_mem_X_of_model hi) hfx, ?_⟩
  let e : centralizer ({iX} : Set d.X) ≃*
      centralizer ({⟨i8, hi⟩} : Set ResidualModel.R) :=
    { toFun := fun a => ⟨d.residualModelEquiv a.val, mem_centralizer_singleton_iff.mpr (by
        have hh := congrArg d.residualModelEquiv
          (mem_centralizer_singleton_iff.mp a.property)
        simpa only [map_mul, iX, d.residualModelEquiv_i hi] using hh)⟩
      invFun := fun a => ⟨d.residualModelEquiv.symm a.val, mem_centralizer_singleton_iff.mpr (by
        have hh := congrArg d.residualModelEquiv.symm
          (mem_centralizer_singleton_iff.mp a.property)
        simpa only [map_mul, he] using hh)⟩
      left_inv := fun a => Subtype.ext (d.residualModelEquiv.symm_apply_apply a.val)
      right_inv := fun a => Subtype.ext (d.residualModelEquiv.apply_symm_apply a.val)
      map_mul' := fun a b => Subtype.ext (map_mul d.residualModelEquiv a.val b.val) }
  exact ⟨((d.centralizerInXEquiv hCL htransfer (d.i_mem_X_of_model hi)).trans e).trans
    hcentralizer.some⟩

/-- Actual application to A₅ recognition, with transfer and model premises explicit. -/
theorem residual_equiv_alternating_five_of_model_and_intersection
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) (hK : ¬ d.K ≤ L)
    (htransfer : d.J ⊓ L = d.X)
    (hcard : Nat.card ResidualModel.R = 12) (hi : i8 ∈ ResidualModel.R)
    (hfusion : ∀ a : ResidualModel.R, orderOf a = 2 →
      IsConj a (⟨i8, hi⟩ : ResidualModel.R))
    (hcentralizer : Nonempty
      (centralizer ({⟨i8, hi⟩} : Set ResidualModel.R) ≃* DihedralGroup 2)) :
    Nonempty (d.J ≃* alternatingGroup (Fin 5)) :=
  residual_equiv_alternating_five d hz hCL hK
    (d.residualFacts_of_model_and_intersection hz hCL htransfer hcard hi hfusion hcentralizer)

end InvolutionData
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index

end
