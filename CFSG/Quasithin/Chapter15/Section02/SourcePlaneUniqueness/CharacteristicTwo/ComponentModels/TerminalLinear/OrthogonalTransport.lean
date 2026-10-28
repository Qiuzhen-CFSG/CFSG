module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.OrthogonalOffender
public import Theory.Representation.BinaryPermutation.EightNormalizer
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.OrthogonalModel

/-!
# The permutation action on the original orthogonal quotient

Conjugation by E = XQI preserves C_U(X), since X is normal in E. The given
orthogonal coordinates on U/C_U(X) extend to E using the full linear
normalizer of the natural A₈ action. Its kernel is a two-group: E is the
normal supplement XQI and the kernel on X is O₂(X). The source core bound
then makes this kernel centralize U. Consequently the resulting permutation
action has exactly C_E(U) as kernel, even when C_U(X) is nonzero.

Source: Aschbacher--Smith 15.2.23(c), printed p.1117; B.3.2(6).
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

/-- The full extension acts on the original U, before any quotient of actors. -/
noncomputable def U_extensionRepresentation (hI : PlaneEscapes Mc ZS I)
    (hn : I ≤ normalizer (X : Set G)) [IsElementaryAbelian 2 (U X ZS)] :
    Representation (ZMod 2) (X ⊔ QI H T ZS : Subgroup G) (Additive (U X ZS)) := by
  let a := (U X ZS).normalizerMonoidHom.comp (inclusion (U_normalized d hI hn))
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

theorem U_extensionRepresentation_apply (hI : PlaneEscapes Mc ZS I)
    (hn : I ≤ normalizer (X : Set G)) [IsElementaryAbelian 2 (U X ZS)]
    (g : (X ⊔ QI H T ZS : Subgroup G)) (u : Additive (U X ZS)) :
    ((U_extensionRepresentation d hI hn g u).toMul : G) =
      (g : G) * (u.toMul : G) * (g : G)⁻¹ := rfl

/-- The marked quotient action extends to XQI with exactly the original
centralizer kernel. It retains the component marking and quotient vector map. -/
theorem exists_orthogonal_permutation_action
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit hXI
    ∀ (C : Subrepresentation (U_representation d hI hfit hXI hn)),
      C.toSubmodule = fixedSpace (U_representation d hI hfit hXI hn) ⊤ →
      ∀ e : ActionEquiv C.quotientRepresentation (alternatingNatural 8),
      ∃ f : (X ⊔ QI H T ZS : Subgroup G) →* Equiv.Perm (Fin 8),
        f.ker = (centralizer (U X ZS : Set G)).subgroupOf (X ⊔ QI H T ZS) ∧
        (∀ x : X, f (inclusion le_sup_left x) =
          (e.groupEquiv (QuotientGroup.mk' (pCore 2 X) x)).val) ∧
        ∀ g u, e.linearEquiv (C.toSubmodule.mkQ (U_extensionRepresentation d hI hn g u)) =
          BinaryPermutation.naturalRepresentation (Fin 8) (f g)
            (e.linearEquiv (C.toSubmodule.mkQ u)) := by
  let := U_elementary d hI hfit hXI
  intro C hC e
  let E := X ⊔ QI H T ZS
  let L := X.subgroupOf E
  let P := (QI H T ZS).subgroupOf E
  have hEI : E ≤ I := sup_le hXI
    ((pCoreIn_le 2 _).trans ((d.residual_sup_planeSylow_le hI).trans inf_le_right))
  let : L.Normal := normal_subgroupOf_of_le_normalizer (hEI.trans hn)
  let τ := U_extensionRepresentation d hI hn
  let σ := U_representation d hI hfit hXI hn
  let qX := QuotientGroup.mk' (pCore 2 X)
  have hact (x : X) (u : Additive (U X ZS)) :
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
  have hinter (x : L) (v : Additive (U X ZS) ⧸ C.toSubmodule) :
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
      map_subgroupOf_eq_of_le (show QI H T ZS ≤ E from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hp : IsPGroup 2 f.ker := f.kernel_isPGroup_of_normal_supplement L P
    ((isPGroup_pCoreIn 2 (KS H T ZS)).comap_subtype) hgen hk
  have hfle : f.ker ≤ pCore 2 E := le_sSup ⟨inferInstance,hp⟩
  refine ⟨f, ?_, ?_, fun g u => hf g (C.toSubmodule.mkQ u)⟩
  · apply le_antisymm
    · intro g hg
      have hgcore := mem_map_of_mem E.subtype (hfle hg)
      exact centralizer_le (U_le_span X ZS)
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
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit hXI
    ∀ (C : Subrepresentation (U_representation d hI hfit hXI hn)),
      C.toSubmodule = fixedSpace (U_representation d hI hfit hXI hn) ⊤ →
      ∀ e : ActionEquiv C.quotientRepresentation (alternatingNatural 8),
      ∃ f : (X ⊔ QI H T ZS : Subgroup G) →* Equiv.Perm (Fin 8),
        f.ker = (centralizer (U X ZS : Set G)).subgroupOf (X ⊔ QI H T ZS) ∧
        (∀ x : X, f (inclusion le_sup_left x) =
          (e.groupEquiv (QuotientGroup.mk' (pCore 2 X) x)).val) ∧
        (∀ g u, e.linearEquiv (C.toSubmodule.mkQ (U_extensionRepresentation d hI hn g u)) =
          BinaryPermutation.naturalRepresentation (Fin 8) (f g)
            (e.linearEquiv (C.toSubmodule.mkQ u))) ∧
        ∃ A ∈ elementaryAbelianMaxSubgroups
          ((QI H T ZS).subgroupOf (X ⊔ QI H T ZS)),
          IsOffender (BinaryPermutation.naturalRepresentation (Fin 8)) (A.map f) := by
  let := U_elementary d hI hfit hXI
  intro C hC e
  obtain ⟨f,hker,hfX,hf⟩ := exists_orthogonal_permutation_action d hI hfit hXI hn hKX C hC e
  let E := X ⊔ QI H T ZS
  let W := (U X ZS).subgroupOf E
  have hUE : U X ZS ≤ E := (U_le_QI d hI hfit hXI).trans le_sup_right
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
  let b : Additive W →ₗ[ZMod 2] Additive (U X ZS) :=
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

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
