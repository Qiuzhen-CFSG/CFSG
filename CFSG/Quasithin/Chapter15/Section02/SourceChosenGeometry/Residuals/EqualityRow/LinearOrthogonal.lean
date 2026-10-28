module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearRows
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.OrthogonalExclusion

/-!
# The original orthogonal-six row from ResidualInput

The genuine Thompson offender on U survives on its marked alternating-eight
quotient. The actual Sylow and residual rank place its normal two-group in
the intrinsic core of the four-block stabilizer, where the checked model
has no offender. The proof retains the full extension XQI, the original
core kernel and the central attachment C_U(X).

Source: Aschbacher--Smith 15.2.23(c), printed p.1117, and B.3.2(6).
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRow.Linear
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B0 I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : ResidualInput hsource H B0)

omit [Finite G] in
private theorem conjugation_kernel (A W : Subgroup G)
    (hn : A ≤ normalizer (W : Set G)) :
    (W.normalizerMonoidHom.comp (inclusion hn)).ker.map A.subtype =
      A ⊓ centralizer (W : Set G) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨a.property,?_⟩
    intro u hu
    have he := congrArg (fun f : MulAut W => (f ⟨u,hu⟩ : G)) ha
    change (a : G) * u * (a : G)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    refine ⟨⟨x,hx.1⟩,?_,rfl⟩
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    change x * (u : G) * x⁻¹ = u
    rw [← hx.2 u u.property, mul_inv_cancel_right]

include d in
/-- The core bound follows from the original Sylow and K-containment clauses. -/
theorem extension_core_le_seed_kernel
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    (X ⊔ QI H T ⁅V,B0⁆).pCoreIn 2 ≤
      QI H T ⁅V,B0⁆ ⊓ centralizer (conjugateSpanBy ⁅V,B0⁆ X : Set G) := by
  let S := planeSylow T ⁅V,B0⁆
  let E := X ⊔ QI H T ⁅V,B0⁆
  have hSI : S ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le_for_blocks hI)).trans inf_le_right
  have hQS : QI H T ⁅V,B0⁆ ≤ S := d.planeParabolicCore_le_plane hI
  have hSQ : S ≤ normalizer (QI H T ⁅V,B0⁆ : Set G) :=
    le_sup_right.trans ((KS H T ⁅V,B0⁆).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hSE : S ≤ normalizer (E : Set G) :=
    (le_inf (hSI.trans hn) hSQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hES : E ≤ X ⊔ S := sup_le le_sup_left (hQS.trans le_sup_right)
  have hESn : X ⊔ S ≤ normalizer (E : Set G) :=
    sup_le (le_sup_left.trans E.le_normalizer) hSE
  have hRS : E.pCoreIn 2 ≤ S := by
    obtain ⟨P,hP⟩ := (show Chapter1.IsSylowIn 2 S I from d.sylow_in_escape_for_blocks hI).restrict
      (show S ≤ X ⊔ S from le_sup_right) (sup_le hXI hSI)
    exact (pCoreIn_mono_of_normalizes hES hESn).trans ((pCoreIn_le_sylow _ P).trans_eq hP)
  have hnR : X ⊔ S ≤ normalizer (E.pCoreIn 2 : Set G) :=
    hESn.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hRQ : E.pCoreIn 2 ≤ QI H T ⁅V,B0⁆ :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 E) (hRS.trans le_sup_right)
      ((sup_le (hKX.trans le_sup_left) le_sup_right).trans hnR)
  exact le_inf hRQ (le_centralizer_conjugateSpanBy_of_normalizes _ ⁅V,B0⁆ X
    (le_sup_left.trans hnR) (hRS.trans inf_le_right))

include d in
/-- The action kernel is a two-group because E is the normal supplement XQI. -/
theorem extension_kernel_isTwoGroup
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G))
    (hfaith : X ⊓ centralizer (U X ⁅V,B0⁆ : Set G) ≤ X.pCoreIn 2) :
    IsPGroup 2 ((X ⊔ QI H T ⁅V,B0⁆) ⊓ centralizer (U X ⁅V,B0⁆ : Set G) : Subgroup G) := by
  let E := X ⊔ QI H T ⁅V,B0⁆
  let L := X.subgroupOf E
  let P := (QI H T ⁅V,B0⁆).subgroupOf E
  have hEI : E ≤ I := sup_le hXI
    ((pCoreIn_le 2 _).trans ((d.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right))
  let : L.Normal := normal_subgroupOf_of_le_normalizer (hEI.trans hn)
  let f : E →* MulAut (U X ⁅V,B0⁆) :=
    (U X ⁅V,B0⁆).normalizerMonoidHom.comp (inclusion (U_normalized d hI hn))
  have hk : IsPGroup 2 (f.comp L.subtype).ker := by
    let r : (f.comp L.subtype).ker →* X.pCoreIn 2 :=
      ((E.subtype.comp L.subtype).comp (f.comp L.subtype).ker.subtype).codRestrict _ (by
        intro x
        apply hfaith
        refine ⟨x.val.property,?_⟩
        intro u hu
        have he := congrArg (fun a : MulAut (U X ⁅V,B0⁆) => (a ⟨u,hu⟩ : G)) x.property
        change (x.val.val : G) * u * (x.val.val : G)⁻¹ = u at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm)
    exact (isPGroup_pCoreIn 2 X).of_injective r (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : X.pCoreIn 2 => (x : G)) hab)
  have hgen : L ⊔ P = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show X ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show QI H T ⁅V,B0⁆ ≤ E from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hp := f.kernel_isPGroup_of_normal_supplement L P
    ((isPGroup_pCoreIn 2 (KS H T ⁅V,B0⁆)).comap_subtype) hgen hk
  rw [← conjugation_kernel E (U X ⁅V,B0⁆) (U_normalized d hI hn)]
  exact hp.map E.subtype

include d in
/-- The precise core identity is proved from Sylow geometry and the action kernel. -/
theorem extension_core_eq_seed_kernel
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hfaith : X ⊓ centralizer (U X ⁅V,B0⁆ : Set G) ≤ X.pCoreIn 2) :
    (X ⊔ QI H T ⁅V,B0⁆).pCoreIn 2 =
      QI H T ⁅V,B0⁆ ⊓ centralizer (conjugateSpanBy ⁅V,B0⁆ X : Set G) := by
  apply le_antisymm (extension_core_le_seed_kernel d hI hXI hn hKX)
  have hc : (X ⊔ QI H T ⁅V,B0⁆) ⊓ centralizer (U X ⁅V,B0⁆ : Set G) ≤
      (X ⊔ QI H T ⁅V,B0⁆).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (extension_kernel_isTwoGroup d hI hXI hn hfaith) inf_le_left
      ((le_inf (X ⊔ QI H T ⁅V,B0⁆).le_normalizer
        ((U_normalized d hI hn).trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf)
  exact (inf_le_inf le_sup_right (centralizer_le (U_le_span X ⁅V,B0⁆))).trans hc

include d in
/-- Faithfulness uses the literal X/O₂(X) action, hence gives its actual ambient kernel. -/
theorem U_centralizer_le_core_of_faithful
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hfaith : Function.Injective (U_representation d hI hfit hXI hn)) :
    X ⊓ centralizer (U X ⁅V,B0⁆ : Set G) ≤ X.pCoreIn 2 := by
  let := U_elementary d hI hfit hXI
  intro x hx
  have he : QuotientGroup.mk' (pCore 2 X) ⟨x,hx.1⟩ = 1 := by
    apply hfaith
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [U_representation_apply, map_one]
    change x * (u.toMul : G) * x⁻¹ = (u.toMul : G)
    rw [← hx.2 u.toMul u.toMul.property, mul_inv_cancel_right]
  exact mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff _).mp he)


/-- A genuine best offender on U, with the marked core identity discharged. -/
theorem U_bestOffender_of_faithful
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hfaith : Function.Injective (U_representation d hI hfit hXI hn)) :
    let E := X ⊔ QI H T ⁅V,B0⁆
    let W := (U X ⁅V,B0⁆).subgroupOf E
    let : W.Normal := normal_subgroupOf_of_le_normalizer (U_normalized d hI hn)
    let : IsElementaryAbelian 2 W := by
      let := U_elementary d hI hfit hXI
      exact IsElementaryAbelian.subgroupOf
        ((U_le_QI d hI hfit hXI).trans le_sup_right)
    let q := QuotientGroup.mk' (centralizer (W : Set E))
    ∃ A ∈ elementaryAbelianMaxSubgroups ((QI H T ⁅V,B0⁆).subgroupOf E),
      Representation.BinaryOffender.IsBestOffender
        (Representation.NormalElementaryQuotient.representation W q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) (A.map q) :=
  U_bestOffender d hI hfit hXI hn hout
    (extension_core_eq_seed_kernel d hI hXI hn hKX
      (U_centralizer_le_core_of_faithful d hI hfit hXI hn hfaith))


/-- The orthogonal module data constructs the FF* witness; neither the
marked core identity nor the existence of an offender is an input. -/
theorem U_bestOffender_of_orthogonalSix
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H B0 I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : ResidualInput hsource H B0)
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit hXI
    ∀ (C : Subrepresentation (U_representation d hI hfit hXI hn)),
      ActionEquiv C.quotientRepresentation (alternatingNatural 8) →
      let E := X ⊔ QI H T ⁅V,B0⁆
      let W := (U X ⁅V,B0⁆).subgroupOf E
      let : W.Normal := normal_subgroupOf_of_le_normalizer (U_normalized d hI hn)
      let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf
          ((U_le_QI d hI hfit hXI).trans le_sup_right)
      let q := QuotientGroup.mk' (centralizer (W : Set E))
      ∃ A ∈ elementaryAbelianMaxSubgroups ((QI H T ⁅V,B0⁆).subgroupOf E),
        Representation.BinaryOffender.IsBestOffender
          (Representation.NormalElementaryQuotient.representation W q
            (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) (A.map q) := by
  let := U_elementary d hI hfit hXI
  intro C e
  exact U_bestOffender_of_faithful d hI hfit hXI hn hout hKX
    (faithful_of_orthogonalSix_quotient C e)


/-- The full extension acts on the original U, before any quotient of actors. -/
noncomputable def U_extensionRepresentation (hI : PlaneEscapes Mc ⁅V,B0⁆ I)
    (hn : I ≤ normalizer (X : Set G)) [IsElementaryAbelian 2 (U X ⁅V,B0⁆)] :
    Representation (ZMod 2) (X ⊔ QI H T ⁅V,B0⁆ : Subgroup G) (Additive (U X ⁅V,B0⁆)) := by
  let a := (U X ⁅V,B0⁆).normalizerMonoidHom.comp (inclusion (U_normalized d hI hn))
  exact {
    toFun g := (a g).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      apply LinearMap.ext
      intro v
      change Additive.ofMul (a 1 v.toMul) = v
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro v
      change Additive.ofMul (a (g*h) v.toMul) = _
      rw [map_mul]
      rfl }

theorem U_extensionRepresentation_apply (hI : PlaneEscapes Mc ⁅V,B0⁆ I)
    (hn : I ≤ normalizer (X : Set G)) [IsElementaryAbelian 2 (U X ⁅V,B0⁆)]
    (g : (X ⊔ QI H T ⁅V,B0⁆ : Subgroup G)) (u : Additive (U X ⁅V,B0⁆)) :
    ((U_extensionRepresentation d hI hn g u).toMul : G) =
      (g : G) * (u.toMul : G) * (g : G)⁻¹ := rfl

/-- The marked quotient action extends to XQI with exactly the original
centralizer kernel. It retains the component marking and quotient vector map. -/
theorem exists_orthogonal_permutation_action
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit hXI
    ∀ (C : Subrepresentation (U_representation d hI hfit hXI hn)),
      C.toSubmodule = fixedSpace (U_representation d hI hfit hXI hn) ⊤ →
      ∀ e : ActionEquiv C.quotientRepresentation (alternatingNatural 8),
      ∃ f : (X ⊔ QI H T ⁅V,B0⁆ : Subgroup G) →* Equiv.Perm (Fin 8),
        f.ker = (centralizer (U X ⁅V,B0⁆ : Set G)).subgroupOf (X ⊔ QI H T ⁅V,B0⁆) ∧
        (∀ x : X, f (inclusion le_sup_left x) =
          (e.groupEquiv (QuotientGroup.mk' (pCore 2 X) x)).val) ∧
        ∀ g u, e.linearEquiv (C.toSubmodule.mkQ (U_extensionRepresentation d hI hn g u)) =
          BinaryPermutation.naturalRepresentation (Fin 8) (f g)
            (e.linearEquiv (C.toSubmodule.mkQ u)) := by
  let := U_elementary d hI hfit hXI
  intro C hC e
  let E := X ⊔ QI H T ⁅V,B0⁆
  let L := X.subgroupOf E
  let P := (QI H T ⁅V,B0⁆).subgroupOf E
  have hEI : E ≤ I := sup_le hXI
    ((pCoreIn_le 2 _).trans ((d.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right))
  let : L.Normal := normal_subgroupOf_of_le_normalizer (hEI.trans hn)
  let τ := U_extensionRepresentation d hI hn
  let σ := U_representation d hI hfit hXI hn
  let qX := QuotientGroup.mk' (pCore 2 X)
  have hact (x : X) (u : Additive (U X ⁅V,B0⁆)) :
      τ (inclusion le_sup_left x) u = σ (qX x) u := rfl
  have hfixed : C.toSubmodule = fixedSpace τ L := by
    rw [hC]
    ext u
    constructor
    · intro hu x
      exact hu ⟨qX ⟨x.val.val,x.property⟩,mem_top _⟩
    · intro hu x
      obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (pCore 2 X) x.val
      change σ x.val u = u
      rw [← hy]
      exact hu ⟨inclusion le_sup_left y,y.property⟩
  let W : Subrepresentation τ := {
    toSubmodule := C.toSubmodule
    apply_mem_toSubmodule g := by
      intro u hu
      rw [hfixed] at hu ⊢
      exact (fixedSpace_stable_of_normalizes τ
        (show (⊤ : Subgroup E) ≤ normalizer (L : Set E) by rw [normalizer_eq_top])
        (mem_top g) u).2 hu }
  let a : L →* BinaryPermutation.EightNormalizer.Actor :=
    e.groupEquiv.toMonoidHom.comp (qX.comp (subgroupOfEquivOfLe
      (show X ≤ E from le_sup_left)).toMonoidHom)
  have ha : Function.Surjective a := e.groupEquiv.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe
      (show X ≤ E from le_sup_left)).surjective)
  have hinter (x : L) (v : Additive (U X ⁅V,B0⁆) ⧸ C.toSubmodule) :
      e.linearEquiv (W.quotientRepresentation x v) =
        BinaryPermutation.EightNormalizer.action (a x) (e.linearEquiv v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact e.intertwines (qX ⟨x.val.val,x.property⟩) (C.toSubmodule.mkQ v)
  obtain ⟨f,hfL,hf,hker⟩ := BinaryPermutation.EightNormalizer.exists_ambient_hom
    W.quotientRepresentation L a ha e.linearEquiv hinter
  have hk : IsPGroup 2 (f.comp L.subtype).ker := by
    let r : (f.comp L.subtype).ker →* pCore 2 X :=
      (((subgroupOfEquivOfLe (show X ≤ E from le_sup_left)).toMonoidHom).comp
        (f.comp L.subtype).ker.subtype).codRestrict _ (by
          intro x
          apply (QuotientGroup.eq_one_iff _).mp
          apply e.groupEquiv.injective
          apply Subtype.ext
          have hx := hfL x.val
          have hx1 : f x.val = 1 := x.property
          rw [hx1] at hx
          rw [map_one]
          change (a x.val).val = 1
          exact hx.symm)
    exact (pCore_isPGroup (p := 2) (G := X)).of_injective r (by
      intro x y he
      apply Subtype.ext
      apply (subgroupOfEquivOfLe (show X ≤ E from le_sup_left)).injective
      exact congrArg Subtype.val he)
  have hgen : L ⊔ P = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show X ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show QI H T ⁅V,B0⁆ ≤ E from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hp : IsPGroup 2 f.ker := f.kernel_isPGroup_of_normal_supplement L P
    ((isPGroup_pCoreIn 2 (KS H T ⁅V,B0⁆)).comap_subtype) hgen hk
  have hfle : f.ker ≤ pCore 2 E := le_sSup ⟨inferInstance,hp⟩
  refine ⟨f, ?_, ?_, fun g u => hf g (C.toSubmodule.mkQ u)⟩
  · apply le_antisymm
    · intro g hg
      have hgcore := mem_map_of_mem E.subtype (hfle hg)
      exact centralizer_le (U_le_span X ⁅V,B0⁆)
        ((extension_core_le_seed_kernel d hI hXI hn hKX hgcore).2)
    · intro g hg
      rw [hker]
      apply LinearMap.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | _ v =>
        change C.toSubmodule.mkQ (τ g v) = C.toSubmodule.mkQ v
        congr 1
        apply Additive.toMul.injective
        apply Subtype.ext
        change (g : G) * (v.toMul : G) * (g : G)⁻¹ = v.toMul
        have hc : (v.toMul : G) * (g : G) = (g : G) * (v.toMul : G) :=
          hg v.toMul v.toMul.property
        rw [← hc, mul_inv_cancel_right]
  · intro x
    exact hfL ⟨inclusion le_sup_left x,x.property⟩

/-- The genuine Thompson offender survives on the six-dimensional model.
Both the actor embedding and the quotient map are constructed, retaining the
same maximum elementary subgroup of the original QI. -/
theorem exists_orthogonal_permutation_offender
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit hXI
    ∀ (C : Subrepresentation (U_representation d hI hfit hXI hn)),
      C.toSubmodule = fixedSpace (U_representation d hI hfit hXI hn) ⊤ →
      ∀ e : ActionEquiv C.quotientRepresentation (alternatingNatural 8),
      ∃ f : (X ⊔ QI H T ⁅V,B0⁆ : Subgroup G) →* Equiv.Perm (Fin 8),
        f.ker = (centralizer (U X ⁅V,B0⁆ : Set G)).subgroupOf (X ⊔ QI H T ⁅V,B0⁆) ∧
        (∀ x : X, f (inclusion le_sup_left x) =
          (e.groupEquiv (QuotientGroup.mk' (pCore 2 X) x)).val) ∧
        (∀ g u, e.linearEquiv (C.toSubmodule.mkQ (U_extensionRepresentation d hI hn g u)) =
          BinaryPermutation.naturalRepresentation (Fin 8) (f g)
            (e.linearEquiv (C.toSubmodule.mkQ u))) ∧
        ∃ A ∈ elementaryAbelianMaxSubgroups
          ((QI H T ⁅V,B0⁆).subgroupOf (X ⊔ QI H T ⁅V,B0⁆)),
          IsOffender (BinaryPermutation.naturalRepresentation (Fin 8)) (A.map f) := by
  let := U_elementary d hI hfit hXI
  intro C hC e
  obtain ⟨f,hker,hfX,hf⟩ := exists_orthogonal_permutation_action d hI hfit hXI hn hKX C hC e
  let E := X ⊔ QI H T ⁅V,B0⁆
  let W := (U X ⁅V,B0⁆).subgroupOf E
  have hUE : U X ⁅V,B0⁆ ≤ E := (U_le_QI d hI hfit hXI).trans le_sup_right
  let : W.Normal := normal_subgroupOf_of_le_normalizer (U_normalized d hI hn)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hUE
  let q := QuotientGroup.mk' (centralizer (W : Set E))
  let ρ := Representation.NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hk : f.ker = centralizer (W : Set E) := by
    rw [hker]
    ext g
    constructor
    · intro hg w hw
      exact Subtype.ext (hg w hw)
    · intro hg u hu
      exact congrArg E.subtype (hg ⟨u,hUE hu⟩ hu)
  let F := QuotientGroup.lift (centralizer (W : Set E)) f hk.ge
  have hF : Function.Injective F := by
    apply (MonoidHom.ker_eq_bot_iff F).mp
    apply bot_unique
    intro a ha
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (W : Set E)) a
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← hk]
    exact ha
  let b : Additive W →ₗ[ZMod 2] Additive (U X ⁅V,B0⁆) :=
    (subgroupOfEquivOfLe hUE).toMonoidHom.toAdditive.toZModLinearMap 2
  have hb : Function.Surjective b := (subgroupOfEquivOfLe hUE).surjective
  let β := e.linearEquiv.toLinearMap.comp (C.toSubmodule.mkQ.comp b)
  have hβ : Function.Surjective β :=
    e.linearEquiv.surjective.comp (C.toSubmodule.mkQ_surjective.comp hb)
  have heq (a : E ⧸ centralizer (W : Set E)) (w : Additive W) :
      β (ρ a w) = BinaryPermutation.naturalRepresentation (Fin 8) (F a) (β w) := by
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (W : Set E)) a
    have hbρ : b (ρ (q g) w) = U_extensionRepresentation d hI hn g (b w) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (((ρ (q g) w).toMul : E) : G) = _
      rw [U_extensionRepresentation_apply d hI hn]
      exact congrArg E.subtype
        (Representation.NormalElementaryQuotient.representation_apply W q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g w)
    change e.linearEquiv (C.toSubmodule.mkQ (b (ρ (q g) w))) = _
    rw [hbρ]
    exact hf g (b w)
  obtain ⟨A,hA,hoff⟩ := U_bestOffender_of_orthogonalSix d hI hfit hXI hn hout hKX C e
  have hquot : IsOffender ((BinaryPermutation.naturalRepresentation (Fin 8)).comp F)
      (A.map q) := ⟨hoff.1,
    (fixedCodim_le_of_equivariant_surjection ρ
      ((BinaryPermutation.naturalRepresentation (Fin 8)).comp F) β hβ heq (A.map q)).trans
        (hoff.isOffender ρ).2⟩
  have hmodel := hquot.map_equivariant _ (BinaryPermutation.naturalRepresentation (Fin 8))
    F hF (LinearEquiv.refl _ _) (fun _ _ => rfl)
  have hcomp : F.comp q = f := by ext g; rfl
  rw [Subgroup.map_map,hcomp] at hmodel
  exact ⟨f,hker,hfX,hf,A,hA,hmodel⟩


/-- A nonzero image of the literal seed marks the full permutation stabilizer. -/
theorem exists_orthogonal_seed_marking
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype ≤ planeSylow T ⁅V,B0⁆) :
    letI := U_elementary d hI hfit hXI
    ∀ (C : Subrepresentation (U_representation d hI hfit hXI hn))
      (e : ActionEquiv C.quotientRepresentation (alternatingNatural 8)),
      ∃ u : Additive (U X ⁅V,B0⁆), (u.toMul : G) ∈ ⁅V,B0⁆ ∧
        e.linearEquiv (C.toSubmodule.mkQ u) ≠ 0 ∧
        ∃ r : alternatingGroup (Fin 8), ∀ g : Equiv.Perm (Fin 8),
          BinaryPermutation.naturalRepresentation (Fin 8) g
            (e.linearEquiv (C.toSubmodule.mkQ u)) = e.linearEquiv (C.toSubmodule.mkQ u) ↔
            r.val * g * r.val⁻¹ ∈
              Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer := by
  let := U_elementary d hI hfit hXI
  intro C e
  let σ := U_representation d hI hfit hXI hn
  let Z := AddSubgroup.toZModSubmodule 2 ((⁅V,B0⁆ : Subgroup G).subgroupOf (U X ⁅V,B0⁆)).toAddSubgroup
  have hgen := U_seed_module_generates d hI hfit hXI hn σ
    (U_representation_apply d hI hfit hXI hn)
  obtain ⟨u,hu,hne⟩ : ∃ u ∈ Z, e.linearEquiv (C.toSubmodule.mkQ u) ≠ 0 := by
    by_contra! hz
    have hZC : Z ≤ C.toSubmodule := by
      intro u hu
      apply (Submodule.Quotient.mk_eq_zero _).mp
      apply e.linearEquiv.injective
      change e.linearEquiv (C.toSubmodule.mkQ u) = e.linearEquiv 0
      simpa only [map_zero] using hz u hu
    have hle : (⨆ g : X ⧸ pCore 2 X, Z.map (σ g)) ≤ C.toSubmodule := by
      apply iSup_le
      rintro g _ ⟨u,hu,rfl⟩
      exact C.apply_mem_toSubmodule g (hZC hu)
    rw [hgen] at hle
    have ht := top_unique hle
    have hdim := e.linearEquiv.finrank_eq
    rw [ht] at hdim
    have hmodel := BinaryPermutation.finrank_natural_even (Fin 8) (by decide)
    simp only [Module.finrank_zero_of_subsingleton] at hdim
    simp only [Fintype.card_fin] at hmodel
    omega
  let q := e.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let Q := P.mapSurjective (f := q)
    (e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  have hfix : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      BinaryPermutation.naturalRepresentation (Fin 8) g.val
        (e.linearEquiv (C.toSubmodule.mkQ u)) = e.linearEquiv (C.toSubmodule.mkQ u) := by
    rintro g ⟨x,hx,rfl⟩
    have hxS := hP (mem_map_of_mem X.subtype hx)
    have hxu : σ (QuotientGroup.mk' (pCore 2 X) x) u = u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [U_representation_apply]
      have hc : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) :=
        hxS.2 u.toMul (show (u.toMul : G) ∈ ⁅V,B0⁆ from hu)
      rw [← hc,mul_inv_cancel_right]
    change alternatingNatural 8 (e.groupEquiv (QuotientGroup.mk' (pCore 2 X) x))
      (e.linearEquiv (C.toSubmodule.mkQ u)) = _
    rw [← e.intertwines, Subrepresentation.quotientRepresentation_mk, hxu]
  obtain ⟨r,hr⟩ := BinaryPermutation.TerminalOrthogonal.Eight.alternating_exists_conjugate_stabilizer
    Q (e.linearEquiv (C.toSubmodule.mkQ u)) hne hfix
  exact ⟨u,hu,hne,r,hr⟩


/-- The orthogonal row is impossible on the original quotient action, with
only the earlier component and small-parabolic source clauses explicit. -/
theorem not_orthogonalSix_canonical
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit hXI
    ∀ (C : Subrepresentation (U_representation d hI hfit hXI hn)),
      C.toSubmodule = fixedSpace (U_representation d hI hfit hXI hn) ⊤ →
      ¬ Nonempty (ActionEquiv C.quotientRepresentation (alternatingNatural 8)) := by
  let := U_elementary d hI hfit hXI
  intro C hC ⟨e⟩
  let E := X ⊔ QI H T ⁅V,B0⁆
  let N := (KS H T ⁅V,B0⁆).subgroupOf E
  let R := (QI H T ⁅V,B0⁆).subgroupOf E
  let K := (pResidual 2 H).map H.subtype
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape_for_blocks hI) hXI (inferInstance : (X.subgroupOf I).Normal).isSubnormal
  have hPS : (P : Subgroup X).map X.subtype ≤ planeSylow T ⁅V,B0⁆ := hP.le.trans inf_le_left
  obtain ⟨u,hu,_,r,hr⟩ := exists_orthogonal_seed_marking d hI hfit hXI hn P hPS C e
  obtain ⟨f,hker,hfX,hf,A,hA,hoff⟩ :=
    exists_orthogonal_permutation_offender d hI hfit hXI hn hout hKX C hC e
  let c := (MulAut.conj r.val).toMonoidHom
  let f' := c.comp f
  let J := N.map f'
  let B := R.map f'
  have hJ : J ≤ Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer := by
    rintro _ ⟨g,hg,rfl⟩
    apply (hr (f g)).mp
    have hgZ : (g : G) ∈ centralizer ((⁅V,B0⁆ : Subgroup G) : Set G) :=
      (sup_le d.residual_centralizes_plane inf_le_right) hg
    have hgu : U_extensionRepresentation d hI hn g u = u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [U_extensionRepresentation_apply d hI hn]
      have hc : (u.toMul : G) * (g : G) = (g : G) * (u.toMul : G) :=
        hgZ u.toMul hu
      rw [← hc, mul_inv_cancel_right]
    exact (hf g u).symm.trans (congrArg (fun v => e.linearEquiv (C.toSubmodule.mkQ v)) hgu)
  have hfaith := faithful_of_orthogonalSix_quotient C e
  have hp : IsPGroup 2 (E ⊓ centralizer (U X ⁅V,B0⁆ : Set G) : Subgroup G) :=
    extension_kernel_isTwoGroup d hI hXI hn
      (U_centralizer_le_core_of_faithful d hI hfit hXI hn hfaith)
  have hpker : IsPGroup 2 f'.ker := by
    let j : f'.ker →* (E ⊓ centralizer (U X ⁅V,B0⁆ : Set G) : Subgroup G) :=
      (E.subtype.comp f'.ker.subtype).codRestrict _ (by
        intro x
        refine ⟨x.val.property, ?_⟩
        have hx : f x.val = 1 := (MulAut.conj r.val).map_eq_one_iff.mp x.property
        exact (hker ▸ hx : x.val ∈ (centralizer (U X ⁅V,B0⁆ : Set G)).subgroupOf E))
    exact hp.of_injective j (by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : (E ⊓ centralizer (U X ⁅V,B0⁆ : Set G) : Subgroup G) => (z : G)) he)
  have hKE : K ≤ E := hKX.trans le_sup_left
  have hKN : K.subgroupOf E ≤ N := fun _ hx => mem_sup_left hx
  have hrN : 2 ≤ primeRank 3 N := by
    have h := primeRank_mono 3 hKN
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hKE)] at h
    exact (d.residual_rank_two.ge).trans h
  have hrJ : 2 ≤ primeRank 3 J := by
    rw [show J = N.map f' from rfl,
      ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) f' hpker]
    exact hrN
  have h9 : 9 ∣ Nat.card J := by
    by_contra hh
    have h := primeRank_le_one_of_square_not_dvd (p := 3) hh
    omega
  let q := e.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let Q := P.mapSurjective (f := q)
    (e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  let a := c.comp (alternatingGroup (Fin 8)).subtype
  have ha : Function.Injective a :=
    (MulAut.conj r.val).injective.comp (alternatingGroup (Fin 8)).subtype_injective
  have hQJ : (Q : Subgroup (alternatingGroup (Fin 8))).map a ≤ J := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨inclusion le_sup_left x, ?_, ?_⟩
    · exact mem_sup_right (hPS (mem_map_of_mem X.subtype hx))
    · exact congrArg c (hfX x)
  have h64 : 64 ∣ Nat.card J := by
    have h := card_dvd_of_le hQJ
    rw [card_map_of_injective ha,
      Theory.SpecificGroups.SymmetricEight.CentralPair.sylow_card Q] at h
    exact h
  have hcard : 576 ∣ Nat.card J :=
    (show Nat.Coprime 64 9 by decide).mul_dvd_of_dvd_of_dvd h64 h9
  have hRN : R ≤ N := fun _ hx => pCoreIn_le 2 (KS H T ⁅V,B0⁆) hx
  have hnR : N ≤ normalizer (R : Set E) := by
    have hnQI : KS H T ⁅V,B0⁆ ≤ normalizer (QI H T ⁅V,B0⁆ : Set G) :=
      (KS H T ⁅V,B0⁆).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
    apply le_normalizer_iff.mpr
    intro g hg x hx
    exact (mem_normalizer_iff.mp (hnQI hg) (x : G)).mp hx
  have hnB : J ≤ normalizer (B : Set (Equiv.Perm (Fin 8))) :=
    (map_mono hnR).trans (R.le_normalizer_map f')
  have hB : IsPGroup 2 B :=
    ((isPGroup_pCoreIn 2 (KS H T ⁅V,B0⁆)).comap_subtype).map f'
  have hc := OrthogonalModel.le_fourBlockCore_of_large_normalizer J B hJ hcard
    (map_mono hRN) hB hnB
  have hmodel : IsOffender (BinaryPermutation.naturalRepresentation (Fin 8))
      ((A.map f).map c) := by
    refine ⟨hoff.1.map_conj r.val, ?_⟩
    rw [fixedCodim_map_conj, rank_map_conj]
    exact hoff.2
  rw [Subgroup.map_map] at hmodel
  change IsOffender (BinaryPermutation.naturalRepresentation (Fin 8))
    (A.map f') at hmodel
  exact OrthogonalModel.not_isOffender_of_le_fourBlockCore _
    ((map_mono hA.1).trans hc) hmodel


end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRow.Linear
