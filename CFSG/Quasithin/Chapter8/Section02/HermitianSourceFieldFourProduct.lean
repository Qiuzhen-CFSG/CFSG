module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Kernel
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.ResidualAction
public import Theory.GroupTheory.PCoreInRestriction
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore
import all CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Kernel

/-!
# The Hermitian pair's faithful core-section product

For the literal parameter-one pair, P = B₀ B₀^i and C_I(P/U)=P.
The full kernel C_R(B₀/U)=O₂(R) extends to P/U because the two
conjugate factors generate P. The bound [R,I]≤O₂(R) makes their action
images commute. The centerless quotient I/P makes those images disjoint,
so O₂(RI)=P O₂(R) is exactly the full action kernel.

All normality is relative to Y=R∨I. Conjugation acts on the original
ambient subgroup quotient P/U; the marked product equivalence sends
the class of ri to the original classes of r and i. Neither global
normality nor a faithful replacement of R or I is assumed. The Chapter12
consumer discharges the residual normalization, commutator and B₀/U
kernel inputs at the original selected four-space.

Source: Aschbacher–Smith E.2.10, E.2.13(7) and 8.2.8(4), printed
pp.222–225,718, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic.Construction Normalizer.TensorRecognition
open Normalizer.SmallOvergroups
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

private theorem selected_centerless {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S) :
    center (I ⧸ pCore 2 I) = ⊥ := by
  have hcard : Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (localCore M I))) = 2 := by
    let := s.twoConjugate.elementary
    let : IsElementaryAbelian 2 (coreImage I V) := IsElementaryAbelian.map _
    have hh := s.rank_eq
    have hpow : Nat.card (coreImage I V) = 2 ^ rank (coreImage I V) := by
      obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 2 (coreImage I V)).exists_card_eq
      rw [rank,ha,Nat.log_pow Nat.one_lt_two]
    rw [hh] at hpow
    change Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = _ at hpow
    rw [←relIndex_ker,QuotientGroup.ker_mk'] at hpow
    rw [←relIndex_ker,QuotientGroup.ker_mk',s.core_eq]
    simpa using hpow
  obtain ⟨m,hm,ho,he,hz⟩ := s.twoConjugate.quotient_P_recognition hcard
  have hp := selected_one_native_core s
  let := s.twoConjugate.core_geometry.1
  have hc : center (I ⧸ TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹) ≤
      pCore 2 (I ⧸ TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹) := by
    let := s.twoConjugate.elementary
    exact le_sSup ⟨inferInstance, ((IsElementaryAbelian.isPGroup 2 (V.subgroupOf I)).map _).to_le hz⟩
  have hz0 : center (I ⧸ TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹) = ⊥ := by
    have hzero : pCore 2 (I ⧸ TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹) = ⊥ := by
      let e := QuotientGroup.quotientMulEquivOfEq hp
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [pCore_map_iso,Subgroup.map_bot,pCore_quotient_pCore_eq_bot]
    exact bot_unique (hc.trans hzero.le)
  exact centerless_of_equiv (QuotientGroup.quotientMulEquivOfEq hp) hz0


private theorem pair_join_action
    (R I V U : Subgroup G) (hRI : R ≤ normalizer (I : Set G))
    (hRU : R ≤ normalizer (U : Set G)) (hIC : I ≤ centralizer (U : Set G))
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2) (i : I)
    (hP : (V ⊓ I.pCoreIn 2) ⊔ (V ⊓ I.pCoreIn 2).map
      (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2)
    (hB : ∀ r : R, (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G),(b : G)⁆ ∈ U) ↔
      r ∈ pCore 2 R)
    (hUN : (U.subgroupOf I).Normal)
    (hI : letI := hUN; centralizerModulo ⊤ (pCore 2 I) (U.subgroupOf I) = pCore 2 I)
    (hcenter : center (I ⧸ pCore 2 I) = ⊥) :
    let Y := R ⊔ I
    ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : Y ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
          f.ker = pCore 2 Y ∧ Y.pCoreIn 2 = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
          (f.comp (inclusion le_sup_left)).ker = pCore 2 R ∧
          (f.comp (inclusion le_sup_right)).ker = pCore 2 I ∧
          ∃ e : (Y ⧸ pCore 2 Y) ≃* (R ⧸ pCore 2 R) × (I ⧸ pCore 2 I),
            ∀ (r : R) (a : I), e (QuotientGroup.mk' (pCore 2 Y)
              (inclusion le_sup_left r * inclusion le_sup_right a)) =
              (QuotientGroup.mk' (pCore 2 R) r, QuotientGroup.mk' (pCore 2 I) a) := by
  let Y := R ⊔ I
  let R' := R.subgroupOf Y
  let I' := I.subgroupOf Y
  have hRY : R ≤ Y := le_sup_left
  have hIY : I ≤ Y := le_sup_right
  have hPY : I.pCoreIn 2 ≤ Y := (pCoreIn_le 2 I).trans hIY
  have hQY : R.pCoreIn 2 ≤ Y := (pCoreIn_le 2 R).trans hRY
  have hYR : Y ≤ normalizer (R : Set G) := sup_le R.le_normalizer
    (le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (pCoreIn_le 2 R)))
  have hYI : Y ≤ normalizer (I : Set G) := sup_le hRI I.le_normalizer
  have hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G) := hYI.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hYU : Y ≤ normalizer (U : Set G) := sup_le hRU
    (hIC.trans (Subgroup.centralizer_le_normalizer _))
  have hUP : (U.subgroupOf (I.pCoreIn 2)).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 I).trans (hIC.trans (Subgroup.centralizer_le_normalizer _)))
  let := hUP
  let := hUN
  let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
  let : R'.Normal := normal_subgroupOf_of_le_normalizer hYR
  let : I'.Normal := normal_subgroupOf_of_le_normalizer hYI
  let : (U.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hYU
  let : (R'.pCoreIn 2).Normal := by unfold pCoreIn; infer_instance
  have hQR : R'.pCoreIn 2 = (R.pCoreIn 2).subgroupOf Y := pCoreIn_subgroupOf 2 R Y hRY
  have hPI : I'.pCoreIn 2 = (I.pCoreIn 2).subgroupOf Y := pCoreIn_subgroupOf 2 I Y hIY
  have hgen : R' ⊔ I' = ⊤ := by
    rw [← subgroupOf_sup hRY hIY]
    exact subgroupOf_self Y
  let b := (V ⊓ I.pCoreIn 2).subgroupOf Y
  let a : Y := inclusion hIY i
  have hbY : V ⊓ I.pCoreIn 2 ≤ Y := inf_le_right.trans hPY
  have hpair : b ⊔ b.map (MulAut.conj a⁻¹).toMonoidHom = (I.pCoreIn 2).subgroupOf Y := by
    apply map_injective Y.subtype_injective
    rw [Subgroup.map_sup, map_map, map_subgroupOf_eq_of_le hPY]
    have he : Y.subtype.comp (MulAut.conj a⁻¹).toMonoidHom =
        (MulAut.conj i.val⁻¹).toMonoidHom.comp Y.subtype := by ext; rfl
    rw [he, ←map_map]
    change ((V ⊓ I.pCoreIn 2).subgroupOf Y).map Y.subtype ⊔
      (((V ⊓ I.pCoreIn 2).subgroupOf Y).map Y.subtype).map
        (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2
    rw [map_subgroupOf_eq_of_le hbY]
    exact hP
  have hQB : ⁅R'.pCoreIn 2,b⁆ ≤ U.subgroupOf Y := by
    rw [hQR]
    apply commutator_le.mpr
    intro r hr v hv
    obtain ⟨r0,hr0,he⟩ := hr
    have h := (hB r0).mpr hr0 ⟨v.val,hv⟩
    change ⁅(r : G),(v : G)⁆ ∈ U
    change (r0 : G) = (r : G) at he
    simpa only [he] using h
  have hQP := two_conjugate_commutator (R'.pCoreIn 2) b (U.subgroupOf Y)
    ((I.pCoreIn 2).subgroupOf Y) a hpair hQB
  have hkill : R'.pCoreIn 2 ≤ f.ker := by
    intro r hr
    apply (mem_sectionAction_ker Y _ U hYP hYU r).mpr
    intro p
    exact hQP (commutator_mem_commutator hr
      (show (⟨p.val,hPY p.property⟩ : Y) ∈ (I.pCoreIn 2).subgroupOf Y from p.property))
  have hRker : (f.comp (inclusion hRY)).ker = pCore 2 R := by
    ext r
    constructor
    · intro hr
      apply (hB r).mp
      intro v
      exact (mem_sectionAction_ker Y _ U hYP hYU (inclusion hRY r)).mp hr
        ⟨v.val,v.property.2⟩
    · intro hr
      apply hkill
      rw [hQR]
      exact mem_map_of_mem R.subtype hr
  have hIker : (f.comp (inclusion hIY)).ker = pCore 2 I := by
    ext r
    rw [←hI]
    rw [mem_centralizerModulo_iff]
    simp only [mem_top, true_and]
    rw [show r ∈ (f.comp (inclusion hIY)).ker ↔
      ∀ p : I.pCoreIn 2, ⁅(r : G),(p : G)⁆ ∈ U from
        mem_sectionAction_ker Y _ U hYP hYU (inclusion hIY r)]
    constructor
    · intro hr p hp
      have hc := hr ⟨p.val,mem_map_of_mem I.subtype hp⟩
      change ⁅(p : G),(r : G)⁆ ∈ U
      simpa only [commutatorElement_inv] using U.inv_mem hc
    · intro hr p
      obtain ⟨p0,hp0,he⟩ := p.property
      have hc : ⁅(p0 : G),(r : G)⁆ ∈ U := hr p0 hp0
      change ⁅(r : G),(p : G)⁆ ∈ U
      rw [←he]
      change ⁅(r : G),(p0 : G)⁆ ∈ U
      simpa only [commutatorElement_inv] using U.inv_mem hc
  have restrict_kernel (A : Subgroup G) (hAY : A ≤ Y)
      (hk : (f.comp (inclusion hAY)).ker = pCore 2 A) :
      (f.comp (A.subgroupOf Y).subtype).ker = pCore 2 (A.subgroupOf Y) := by
    let e := subgroupOfEquivOfLe hAY
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso]
    rw [←hk]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hx
      exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
  have hR' := restrict_kernel R hRY hRker
  have hI' := restrict_kernel I hIY hIker
  let eI : I' ≃* I := subgroupOfEquivOfLe hIY
  have hcI : center (I' ⧸ pCore 2 I') = ⊥ :=
    centerless_of_equiv (QuotientGroup.congr _ _ eI (pCore_map_iso 2 eI)).symm hcenter
  have hcomm' : ⁅R',I'⁆ ≤ f.ker := by
    apply le_trans _ hkill
    rw [hQR]
    apply commutator_le.mpr
    intro r hr t ht
    exact hcomm (commutator_mem_commutator hr ht)
  obtain ⟨hcore,hker,e,he⟩ := action_core_product f R' I' hgen hcomm'
    (centerless_action_image f I' hI' hcI) hR' hI'
  have hcoreG : Y.pCoreIn 2 = I.pCoreIn 2 ⊔ R.pCoreIn 2 := by
    have hh := congrArg (Subgroup.map Y.subtype) (hcore.trans hker)
    rw [Subgroup.map_sup,hQR,hPI,map_subgroupOf_eq_of_le hQY,map_subgroupOf_eq_of_le hPY] at hh
    exact hh.trans (sup_comm _ _)
  let eR : (R ⧸ pCore 2 R) ≃* R'.map f :=
    (QuotientGroup.quotientMulEquivOfEq hRker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (f.comp (inclusion hRY))).trans
        (MulEquiv.subgroupCongr (by
          rw [MonoidHom.range_comp]
          congr 1
          ext r
          exact ⟨fun ⟨x,hx⟩ => hx ▸ x.property,fun hr => ⟨⟨r,hr⟩,rfl⟩⟩)))
  let eI' : (I ⧸ pCore 2 I) ≃* I'.map f :=
    (QuotientGroup.quotientMulEquivOfEq hIker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (f.comp (inclusion hIY))).trans
        (MulEquiv.subgroupCongr (by
          rw [MonoidHom.range_comp]
          congr 1
          ext r
          exact ⟨fun ⟨x,hx⟩ => hx ▸ x.property,fun hr => ⟨⟨r,hr⟩,rfl⟩⟩)))
  let q : (Y ⧸ pCore 2 Y) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientKerEquivRange f)
  refine ⟨hYP,hYU,hUP,hcore.symm,hcoreG,hRker,hIker,q.trans (e.symm.trans (eR.symm.prodCongr eI'.symm)),?_⟩
  intro r t
  apply (eR.prodCongr eI').injective
  change (eR (eR.symm _),eI' (eI'.symm _)) = _
  simp only [eR.apply_symm_apply,eI'.apply_symm_apply]
  apply e.injective
  change e (e.symm (q _)) = e
    (eR (QuotientGroup.mk' (pCore 2 R) r),eI' (QuotientGroup.mk' (pCore 2 I) t))
  rw [e.apply_symm_apply]
  apply Subtype.ext
  rw [he]
  exact map_mul f _ _


/-- On the literal selected pair, the join has full kernel O₂(RI)=O₂(I)O₂(R)
and its faithful quotient is the marked product of the original core quotients. -/
theorem selected_one_product_action
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    {H M I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T M V I 1 i S) (hT : HypothesisE322 V T)
    (eV : Additive V ≃ₗ[ZMod 2] Representation.HermitianTensorThree.Space 1)
    (j : Automizer V →* Representation.HermitianTensorThree.binaryNormalizer 1)
    (hj : Function.Injective j)
    (he : ∀ a v, eV (automizerRepresentation V a v) =
      Representation.HermitianTensorThree.overgroupAction 1
        (Representation.HermitianTensorThree.binaryNormalizer 1) (j a) (eV v))
    (R : Subgroup G)
    (hRI : R ≤ normalizer (I : Set G))
    (hRU : R ≤ normalizer (V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G))
    (hcomm : ⁅R,centralizer (V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G)⁆ ≤ R.pCoreIn 2)
    (hB :
      let U := V ⊓ centralizer
        (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
      ∀ r : R, (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G),(b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R) :
    let U := V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
    let Y := R ⊔ I
    ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : Y ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
          f.ker = pCore 2 Y ∧ Y.pCoreIn 2 = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
          (f.comp (inclusion le_sup_left)).ker = pCore 2 R ∧
          (f.comp (inclusion le_sup_right)).ker = pCore 2 I ∧
          ∃ e : (Y ⧸ pCore 2 Y) ≃* (R ⧸ pCore 2 R) × (I ⧸ pCore 2 I),
            ∀ (r : R) (a : I), e (QuotientGroup.mk' (pCore 2 Y)
              (inclusion le_sup_left r * inclusion le_sup_right a)) =
              (QuotientGroup.mk' (pCore 2 R) r, QuotientGroup.mk' (pCore 2 I) a) := by
  obtain ⟨_,_,_,_,_,_,_,hIC,_⟩ := selected_one_fixed_subgroup s hT 1 eV j hj he
  obtain ⟨hU,hI⟩ := selected_one_section_kernel s hT 1 eV j hj he
  have hIP : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPi : (I.pCoreIn 2).map (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hIP (I.inv_mem i.property))
  have hP : (V ⊓ I.pCoreIn 2) ⊔ (V ⊓ I.pCoreIn 2).map
      (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2 := by
    rw [map_inf _ _ _ (MulAut.conj i.val⁻¹).injective,hPi]
    exact (selected_one_core_product s).symm
  exact pair_join_action R I V _ hRI hRU hIC
    ((commutator_mono le_rfl hIC).trans hcomm) i hP hB hU hI (selected_centerless s)

/-- The full original pair action, with its quotient representatives, kernels,
section size and literal inclusion of B₀/U. -/
@[expose] def PairProductAction (R I V U : Subgroup G) : Prop :=
    let Y := R ⊔ I
    ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : Y ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
          IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ∧
          Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2^8 ∧
          f.ker = pCore 2 Y ∧ Y.pCoreIn 2 = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
          (f.comp (inclusion le_sup_left)).ker = pCore 2 R ∧
          (f.comp (inclusion le_sup_right)).ker = pCore 2 I ∧
          let B₀ := V ⊓ I.pCoreIn 2
          ∃ hRB : R ≤ normalizer (B₀ : Set G),
            ∃ hBU : (U.subgroupOf B₀).Normal, letI := hBU
              let q := QuotientGroup.quotientMapSubgroupOfOfLe (show U ≤ U from le_rfl)
                (show B₀ ≤ I.pCoreIn 2 from inf_le_right)
              (∀ (r : R) (b : B₀ ⧸ U.subgroupOf B₀),
                q (sectionAction R B₀ U hRB (le_sup_left.trans hYU) r b) =
                  f (inclusion le_sup_left r) (q b)) ∧
              ∃ e : (Y ⧸ pCore 2 Y) ≃* (R ⧸ pCore 2 R) × (I ⧸ pCore 2 I),
                ∀ (r : R) (a : I), e (QuotientGroup.mk' (pCore 2 Y)
                  (inclusion le_sup_left r * inclusion le_sup_right a)) =
                  (QuotientGroup.mk' (pCore 2 R) r, QuotientGroup.mk' (pCore 2 I) a)

/-- The selected eight-space and its literal B₀/U inclusion carry the
faithful product action, with every kernel supplied by the earlier pair lemmas. -/
theorem selected_one_full_product_action
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    {H M I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T M V I 1 i S) (hT : HypothesisE322 V T)
    (eV : Additive V ≃ₗ[ZMod 2] Representation.HermitianTensorThree.Space 1)
    (j : Automizer V →* Representation.HermitianTensorThree.binaryNormalizer 1)
    (hj : Function.Injective j)
    (he : ∀ a v, eV (automizerRepresentation V a v) =
      Representation.HermitianTensorThree.overgroupAction 1
        (Representation.HermitianTensorThree.binaryNormalizer 1) (j a) (eV v))
    (R : Subgroup G)
    (hRV : R ≤ normalizer (V : Set G))
    (hRI : R ≤ normalizer (I : Set G))
    (hRU : R ≤ normalizer (V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G))
    (hcomm : ⁅R,centralizer (V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G)⁆ ≤ R.pCoreIn 2)
    (hB :
      let U := V ⊓ centralizer
        (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
      ∀ r : R, (∀ b : ↥(V ⊓ I.pCoreIn 2), ⁅(r : G),(b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R) :
    let U := V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
    PairProductAction R I V U := by
  let U := V ⊓ centralizer
    (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  obtain ⟨hYP,hYU,hUP,hker,hcore,hR,hI,e,heq⟩ :=
    selected_one_product_action s hT eV j hj he R hRI hRU hcomm hB
  let := hUP
  obtain ⟨hUP',hEl,hcard,_⟩ := selected_one_core_section s hT 1 eV j hj he
  let B₀ := V ⊓ I.pCoreIn 2
  have hRB : R ≤ normalizer (B₀ : Set G) :=
    (le_inf hRV (le_sup_left.trans hYP)).trans inf_normalizer_le_normalizer_inf
  let : IsElementaryAbelian 2 B₀ := IsElementaryAbelian.of_le
    (show B₀ ≤ V from inf_le_left)
  have hBU : (U.subgroupOf B₀).Normal := inferInstance
  let := hBU
  refine ⟨hYP,hYU,hUP,hEl,hcard,hker,hcore,hR,hI,hRB,hBU,?_,e,heq⟩
  intro r b
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B₀) b
  rfl


end CFSG.Quasithin.Chapter8.Section02.HermitianSource
