module

public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.RingHom.Flat
public import Theory.AlgebraicGroup.ClosedSubgroup.Invariant
import Theory.AlgebraicGroup.CoordinateRing.FiniteTranslate
import Theory.AlgebraicGroup.CoordinateRing.Hopf.Basic
import Theory.AlgebraicGroup.CoordinateRing.Hopf.Presentation
import Theory.AlgebraicGroup.CoordinateRing.Tensor
import Theory.AlgebraicGroup.Morphism.ClosedImage
import Theory.AlgebraicGroup.Morphism.Reconstruction

universe u

set_option linter.style.haveILetI false

/-! Faithfulness, finite type, and flatness over right-invariant coordinates. -/

/-! The ambient coordinate ring is faithful over its invariant subalgebra. -/

namespace Theory.AlgebraicGroup

section
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateRing_faithfulSMul
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    FaithfulSMul (AlgebraicGroup.rightInvariantCoordinateRing H)
      (Variety.PolynomialFunction G) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact Subtype.val_injective

end

section

variable {R S : Type u} [CommRing R] [CommRing S]

lemma awayMap_flat_of_equivariant
    (f : R →+* S) (eR : R ≃+* R) (eS : S ≃+* S)
    (hcomm : eS.toRingHom.comp f = f.comp eR.toRingHom)
    (r : R) (hflat : RingHom.Flat (Localization.awayMap f r)) :
    RingHom.Flat (Localization.awayMap f (eR r)) := by
  classical
  have hcomm_apply : eS (f r) = f (eR r) := by
    exact DFunLike.congr_fun hcomm r
  have hpowersR :
      Submonoid.map eR.toMonoidHom (Submonoid.powers r) =
        Submonoid.powers (eR r) := by
    exact Submonoid.map_powers eR.toMonoidHom r
  let eRloc : Localization.Away r ≃+* Localization.Away (eR r) :=
    IsLocalization.ringEquivOfRingEquiv _ _ eR hpowersR
  have hpowersS :
      Submonoid.map eS.toMonoidHom (Submonoid.powers (f r)) =
        Submonoid.powers (f (eR r)) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers hcomm_apply
  let eSloc : Localization.Away (f r) ≃+*
      Localization.Away (f (eR r)) :=
    IsLocalization.ringEquivOfRingEquiv _ _ eS hpowersS
  have hpost : RingHom.Flat
      (eSloc.toRingHom.comp (Localization.awayMap f r)) :=
    RingHom.Flat.respectsIso.1 (Localization.awayMap f r) eSloc hflat
  have htransport : RingHom.Flat
      ((eSloc.toRingHom.comp (Localization.awayMap f r)).comp
        eRloc.symm.toRingHom) :=
    RingHom.Flat.respectsIso.2
      (eSloc.toRingHom.comp (Localization.awayMap f r)) eRloc.symm hpost
  convert htransport using 1
  apply IsLocalization.ringHom_ext (Submonoid.powers (eR r))
  ext x
  simp [eRloc, eSloc]
  simp only [Localization.awayMap, IsLocalization.Away.map,
    IsLocalization.map_eq]
  have hER :
      eRloc.symm ((algebraMap R (Localization.Away (eR r))) x) =
        algebraMap R (Localization.Away r) (eR.symm x) := by
    apply eRloc.injective
    rw [eRloc.apply_symm_apply]
    rw [IsLocalization.ringEquivOfRingEquiv_eq hpowersR]
    simp
  have hx : eS (f (eR.symm x)) = f x := by
    simpa using DFunLike.congr_fun hcomm (eR.symm x)
  rw [hER]
  rw [IsLocalization.map_eq, IsLocalization.map_eq]
  exact congrArg (algebraMap S (Localization.Away (f (eR r)))) hx.symm

end

/-! Finite Hopf-stable subalgebras of normal right-invariants. -/

section

open scoped TensorProduct

variable {k : Type u} [Field k]

lemma exists_finite_rightInvariant_twoSidedTranslate_stableSubmodule
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal)
    (t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H)) :
    ∃ W : Submodule k (Variety.PolynomialFunction G), W.FG ∧
      (∀ f ∈ t, f.1 ∈ W) ∧
      W ≤ (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule ∧
      (∀ a q, q ∈ W →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ W) ∧
      (∀ b q, q ∈ W →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ W) := by
  let S : Set (Variety.PolynomialFunction G) :=
    {q | ∃ f ∈ t, ∃ a b : Variety.Point G,
      q = (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom
        ((AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom f.1)}
  let W := Submodule.span k S
  choose U hUfg hU using fun i : t =>
    AlgebraicGroup.exists_finite_twoSidedTranslate_submodule G i.1.1
  let upper : Submodule k (Variety.PolynomialFunction G) := ⨆ i : t, U i
  have hupperfg : upper.FG := by
    apply Submodule.fg_iSup
    intro i
    exact hUfg i
  have hWle : W ≤ upper := by
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨f, hf, a, b, rfl⟩
    let i : t := ⟨f, hf⟩
    exact Submodule.mem_iSup_of_mem i (hU i a b)
  have hWfg : W.FG := hupperfg.of_le hWle
  have htW : ∀ f ∈ t, f.1 ∈ W := by
    intro f hf
    apply Submodule.subset_span
    refine ⟨f, hf, 1, 1, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    change f.1 x = f.1 ((AlgebraicGroup.rightMulMorphism G 1).toFun
      ((AlgebraicGroup.leftMulMorphism G 1).toFun x))
    rw [AlgebraicGroup.leftMulMorphism_apply,
      AlgebraicGroup.rightMulMorphism_apply, one_mul, mul_one]
  have hWinvariant :
      W ≤ (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule := by
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨f, hf, a, b, rfl⟩
    change (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom
      ((AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom f.1) ∈
        AlgebraicGroup.rightInvariantCoordinateRing H
    rw [AlgebraicGroup.mem_rightInvariantCoordinateRing_iff]
    intro g h hh
    have hconj : b⁻¹ * h * b ∈ H.toSubgroup := hN.conj_mem' h hh b
    have hfixed :=
      (AlgebraicGroup.mem_rightInvariantCoordinateRing_iff H f.val).mp
        f.property (a * g * b) (b⁻¹ * h * b) hconj
    change f.val (a * (g * h) * b) = f.val (a * g * b)
    simpa [mul_assoc] using hfixed
  refine ⟨W, hWfg, htW, hWinvariant, ?_, ?_⟩
  · intro a q hq
    let T := (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom.toLinearMap
    refine Submodule.span_induction (p := fun q _ => T q ∈ W) ?_ ?_ ?_ ?_ hq
    · intro q hq
      rcases hq with ⟨f, hf, c, d, rfl⟩
      apply Submodule.subset_span
      refine ⟨f, hf, c * a, d, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      change f.1 ((AlgebraicGroup.rightMulMorphism G d).toFun
        ((AlgebraicGroup.leftMulMorphism G c).toFun
          ((AlgebraicGroup.leftMulMorphism G a).toFun x))) =
        f.1 ((AlgebraicGroup.rightMulMorphism G d).toFun
          ((AlgebraicGroup.leftMulMorphism G (c * a)).toFun x))
      simp only [AlgebraicGroup.leftMulMorphism_apply,
        AlgebraicGroup.rightMulMorphism_apply, mul_assoc]
    · exact W.zero_mem
    · intro x y hx hy hTx hTy
      exact W.add_mem hTx hTy
    · intro r x hx hTx
      rw [T.map_smul]
      exact W.smul_mem r hTx
  · intro b q hq
    let T := (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom.toLinearMap
    refine Submodule.span_induction (p := fun q _ => T q ∈ W) ?_ ?_ ?_ ?_ hq
    · intro q hq
      rcases hq with ⟨f, hf, c, d, rfl⟩
      apply Submodule.subset_span
      refine ⟨f, hf, c, b * d, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      change f.1 ((AlgebraicGroup.rightMulMorphism G d).toFun
        ((AlgebraicGroup.leftMulMorphism G c).toFun
          ((AlgebraicGroup.rightMulMorphism G b).toFun x))) =
        f.1 ((AlgebraicGroup.rightMulMorphism G (b * d)).toFun
          ((AlgebraicGroup.leftMulMorphism G c).toFun x))
      simp only [AlgebraicGroup.leftMulMorphism_apply,
        AlgebraicGroup.rightMulMorphism_apply, mul_assoc]
    · exact W.zero_mem
    · intro x y hx hy hTx hTy
      exact W.add_mem hTx hTy
    · intro r x hx hTx
      rw [T.map_smul]
      exact W.smul_mem r hTx

lemma exists_finite_rightInvariant_translate_antipode_stableSubmodule
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal)
    (t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H)) :
    ∃ W : Submodule k (Variety.PolynomialFunction G), W.FG ∧
      (∀ f ∈ t, f.1 ∈ W) ∧
      W ≤ (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule ∧
      (∀ a q, q ∈ W →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ W) ∧
      (∀ b q, q ∈ W →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ W) ∧
      (∀ q, q ∈ W → AlgebraicGroup.coordinateAntipode G q ∈ W) := by
  obtain ⟨V, hVfg, htV, hVinvariant, hleftV, hrightV⟩ :=
    exists_finite_rightInvariant_twoSidedTranslate_stableSubmodule H hN t
  let S := (AlgebraicGroup.coordinateAntipode G).toLinearMap
  let W := V ⊔ V.map S
  have hSinvolutive : ∀ q, S (S q) = q := by
    intro q
    apply Variety.PolynomialFunction.ext
    intro x
    change q ((x⁻¹)⁻¹) = q x
    simp
  have hSleft : ∀ a q,
      S ((AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q) =
        (AlgebraicGroup.rightMulMorphism G a⁻¹).pullbackAlgHom (S q) := by
    intro a q
    apply Variety.PolynomialFunction.ext
    intro x
    change q (a * x⁻¹) = q ((x * a⁻¹)⁻¹)
    rw [mul_inv_rev, inv_inv]
  have hSright : ∀ b q,
      S ((AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q) =
        (AlgebraicGroup.leftMulMorphism G b⁻¹).pullbackAlgHom (S q) := by
    intro b q
    apply Variety.PolynomialFunction.ext
    intro x
    change q (x⁻¹ * b) = q ((b⁻¹ * x)⁻¹)
    rw [mul_inv_rev, inv_inv]
  have hWfg : W.FG := hVfg.sup (Submodule.FG.map S hVfg)
  have hWinvariant :
      W ≤ (AlgebraicGroup.rightInvariantCoordinateRing H).toSubmodule := by
    apply sup_le hVinvariant
    rintro q ⟨p, hp, rfl⟩
    exact AlgebraicGroup.coordinateAntipode_mem_rightInvariantCoordinateRing
      H hN p (hVinvariant hp)
  refine ⟨W, hWfg, ?_, hWinvariant, ?_, ?_, ?_⟩
  · intro q hq
    exact Submodule.mem_sup_left (htV q hq)
  · intro a q hq
    rcases Submodule.mem_sup.mp hq with ⟨x, hx, y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
    rw [map_add]
    apply Submodule.add_mem_sup
    · exact hleftV a x hx
    · apply Submodule.mem_map.mpr
      refine ⟨(AlgebraicGroup.rightMulMorphism G a⁻¹).pullbackAlgHom z,
        hrightV a⁻¹ z hz, ?_⟩
      rw [hSright, inv_inv]
  · intro b q hq
    rcases Submodule.mem_sup.mp hq with ⟨x, hx, y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
    rw [map_add]
    apply Submodule.add_mem_sup
    · exact hrightV b x hx
    · apply Submodule.mem_map.mpr
      refine ⟨(AlgebraicGroup.leftMulMorphism G b⁻¹).pullbackAlgHom z,
        hleftV b⁻¹ z hz, ?_⟩
      rw [hSleft, inv_inv]
  · intro q hq
    rcases Submodule.mem_sup.mp hq with ⟨x, hx, y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
    change S (x + S z) ∈ W
    rw [map_add, hSinvolutive, add_comm]
    exact Submodule.add_mem_sup hz (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

public lemma ClosedSubgroup.finiteTypeRightInvariantHopfStableSubalgebra_exists_of_finset
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal)
    (t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H)) :
    ∃ C : Subalgebra k (Variety.PolynomialFunction G),
      Algebra.FiniteType k C ∧
      (∀ f ∈ t, f.1 ∈ C) ∧
      C ≤ AlgebraicGroup.rightInvariantCoordinateRing H ∧
      (∀ a q, q ∈ C →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ C) ∧
      (∀ b q, q ∈ C →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ C) ∧
      (∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) ∧
      (∀ q, q ∈ C → ∃ w : C ⊗[k] C,
        TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
          AlgebraicGroup.coordinateComultiplication G q) := by
  obtain ⟨W, hWfg, htW, hWinvariant, hleftW, hrightW, hantipodeW⟩ :=
    exists_finite_rightInvariant_translate_antipode_stableSubmodule H hN t
  obtain ⟨s, hsfinite, hsW⟩ := Submodule.fg_def.mp hWfg
  let C := Algebra.adjoin k s
  have hWleC : W ≤ C.toSubmodule := by
    rw [← hsW]
    exact Submodule.span_le.mpr (fun q hq => Algebra.subset_adjoin hq)
  have hCleInvariant : C ≤ AlgebraicGroup.rightInvariantCoordinateRing H := by
    apply Algebra.adjoin_le
    intro q hq
    exact hWinvariant (hsW ▸ Submodule.subset_span hq)
  have hleftC : ∀ a q, q ∈ C →
      (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ C := by
    intro a q hq
    induction hq using Algebra.adjoin_induction with
    | mem q hqs =>
        exact hWleC (hleftW a q (hsW ▸ Submodule.subset_span hqs))
    | algebraMap r =>
        rw [(AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom.commutes]
        exact C.algebraMap_mem r
    | add x y hx hy hTx hTy =>
        simpa only [map_add] using C.add_mem hTx hTy
    | mul x y hx hy hTx hTy =>
        simpa only [map_mul] using C.mul_mem hTx hTy
  have hrightC : ∀ b q, q ∈ C →
      (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ C := by
    intro b q hq
    induction hq using Algebra.adjoin_induction with
    | mem q hqs =>
        exact hWleC (hrightW b q (hsW ▸ Submodule.subset_span hqs))
    | algebraMap r =>
        rw [(AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom.commutes]
        exact C.algebraMap_mem r
    | add x y hx hy hTx hTy =>
        simpa only [map_add] using C.add_mem hTx hTy
    | mul x y hx hy hTx hTy =>
        simpa only [map_mul] using C.mul_mem hTx hTy
  have hantipodeC : ∀ q, q ∈ C →
      AlgebraicGroup.coordinateAntipode G q ∈ C := by
    intro q hq
    induction hq using Algebra.adjoin_induction with
    | mem q hqs =>
        exact hWleC (hantipodeW q (hsW ▸ Submodule.subset_span hqs))
    | algebraMap r =>
        rw [(AlgebraicGroup.coordinateAntipode G).commutes]
        exact C.algebraMap_mem r
    | add x y hx hy hTx hTy =>
        simpa only [map_add] using C.add_mem hTx hTy
    | mul x y hx hy hTx hTy =>
        simpa only [map_mul] using C.mul_mem hTx hTy
  refine ⟨C, Algebra.FiniteType.adjoin_of_finite hsfinite, ?_, hCleInvariant,
    hleftC, hrightC, hantipodeC, ?_⟩
  · intro f hf
    exact hWleC (htW f hf)
  · intro q hq
    exact AlgebraicGroup.exists_tensorSubalgebra_comultiplication_of_translate_stable
      G C hleftC hrightC q hq

end

/-! Quotient morphisms represented by finite Hopf-stable coordinate subalgebras. -/

section

open scoped TensorProduct

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def leftTranslateAlgEquiv
    (Q : Variety k) [AlgebraicGroup Q] (a : Variety.Point Q) :
    Variety.PolynomialFunction Q ≃ₐ[k] Variety.PolynomialFunction Q := by
  let f := (AlgebraicGroup.leftMulMorphism Q a).pullbackAlgHom
  let g := (AlgebraicGroup.leftMulMorphism Q a⁻¹).pullbackAlgHom
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AlgHom.ext
    intro q
    apply Variety.PolynomialFunction.ext
    intro x
    change q (a⁻¹ * (a * x)) = q x
    rw [inv_mul_cancel_left]
  · apply AlgHom.ext
    intro q
    apply Variety.PolynomialFunction.ext
    intro x
    change q (a * (a⁻¹ * x)) = q x
    rw [mul_inv_cancel_left]

public lemma finiteTypeHopfStableSubalgebra_quotientMorphism_exists
    {G : Variety k} [AlgebraicGroup G]
    (C : Subalgebra k (Variety.PolynomialFunction G))
    [Algebra.FiniteType k C]
    (hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        AlgebraicGroup.coordinateComultiplication G q)
    (hantipode : ∀ q, q ∈ C →
      AlgebraicGroup.coordinateAntipode G q ∈ C) :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
      (e : C ≃ₐ[k] Variety.PolynomialFunction Q)
      (π : AlgebraicGroup.Morphism G Q),
      Function.Surjective π.onPoints ∧
        π.toVariety.pullbackAlgHom.comp e.toAlgHom = C.val := by
  letI : HopfAlgebra k C :=
    AlgebraicGroup.coordinateSubalgebraHopfAlgebra G C hcomul hantipode
  let : IsReduced C :=
    isReduced_of_injective (Subalgebra.val C) Subtype.val_injective
  let P : ReducedFiniteTypeAlgebraPresentation k C :=
    Classical.choice (ReducedFiniteTypeAlgebraPresentation.exists k C)
  let Q := P.toVariety
  letI : AlgebraicGroup Q := by
    dsimp only [Q]
    exact P.algebraicGroup
  let evalC (g : Variety.Point G) : C →ₐ[k] k :=
    (Variety.PolynomialFunction.evalAlgHom G g).comp C.val
  have evalC_one (f : C) :
      evalC 1 f = AlgebraicGroup.coordinateSubalgebraCounit G C f := by
    rfl
  have evalC_mul (g x : Variety.Point G) (f : C) :
      evalC (g * x) f =
        (WithConv.toConv (evalC g) * WithConv.toConv (evalC x)).ofConv f := by
    have ht (t : C ⊗[k] C) :
        polynomialFunctionTensor G G
            (TensorProduct.map C.val.toLinearMap C.val.toLinearMap t)
              ((Variety.prodPointEquiv G G).symm (g, x)) =
          Algebra.TensorProduct.lift
            (evalC g) (evalC x) (fun _ _ => Commute.all _ _) t := by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
          simp only [map_add, Variety.PolynomialFunction.toFun,
            Subring.coe_add, Pi.add_apply]
          exact congrArg₂ (fun a b => a + b) ha hb
      | tmul a b =>
          rw [TensorProduct.map_tmul, polynomialFunctionTensor_tmul,
            Algebra.TensorProduct.lift_tmul]
          rfl
    rw [AlgHom.convMul_apply]
    change f.val (g * x) = _
    rw [← AlgebraicGroup.coordinateComultiplication_apply G f.val g x]
    rw [← AlgebraicGroup.coordinateSubalgebraComultiplication_apply G C hcomul f]
    exact ht (Coalgebra.comul f)
  let pointMap : Variety.Point G →* Variety.Point Q :=
    { toFun := fun g => P.pointCharacterEquiv.symm
        (WithConv.toConv (evalC g))
      map_one' := by
        change P.pointCharacterEquiv.symm
            (WithConv.toConv (evalC 1)) = P.pointCharacterEquiv.symm 1
        apply P.pointCharacterEquiv.injective
        rw [P.pointCharacterEquiv.apply_symm_apply,
          P.pointCharacterEquiv.apply_symm_apply]
        apply WithConv.ofConv_injective
        apply AlgHom.ext
        intro f
        exact evalC_one f
      map_mul' := by
        intro g x
        change P.pointCharacterEquiv.symm
            (WithConv.toConv (evalC (g * x))) =
          @Mul.mul (Variety.Point P.toVariety) P.pointGroup.toMul
            (P.pointCharacterEquiv.symm (WithConv.toConv (evalC g)))
            (P.pointCharacterEquiv.symm (WithConv.toConv (evalC x)))
        apply P.pointCharacterEquiv.injective
        rw [P.pointCharacterEquiv_mul]
        simp only [Equiv.apply_symm_apply]
        apply WithConv.ofConv_injective
        apply AlgHom.ext
        intro f
        exact evalC_mul g x f }
  let α : Variety.PolynomialFunction Q →ₐ[k] Variety.PolynomialFunction G :=
    C.val.comp P.polynomialFunctionAlgEquiv.symm.toAlgHom
  have hα (a : Variety.PolynomialFunction Q) (g : Variety.Point G) :
      α a g = a (pointMap g) := by
    change (P.polynomialFunctionAlgEquiv.symm a).val g = a (pointMap g)
    change evalC g (P.polynomialFunctionAlgEquiv.symm a) = _
    have hchar := congrArg
      (fun φ : WithConv (C →ₐ[k] k) =>
        φ.ofConv (P.polynomialFunctionAlgEquiv.symm a))
      (P.pointCharacterEquiv.apply_symm_apply
        (WithConv.toConv (evalC g)))
    calc
      evalC g (P.polynomialFunctionAlgEquiv.symm a) =
          (P.pointCharacterEquiv
            (P.pointCharacterEquiv.symm
              (WithConv.toConv (evalC g)))).ofConv
            (P.polynomialFunctionAlgEquiv.symm a) := hchar.symm
      _ = a (pointMap g) := by
        change (P.polynomialFunctionAlgEquiv
          (P.polynomialFunctionAlgEquiv.symm a)) (pointMap g) = _
        rw [P.polynomialFunctionAlgEquiv.apply_symm_apply]
  obtain ⟨π, hπpoint⟩ :=
    Morphism.exists_of_pointHom_of_polynomialFunctionAlgHom pointMap α hα
  have hπpull : π.toVariety.pullbackAlgHom = α := by
    apply AlgHom.ext
    intro a
    apply Variety.PolynomialFunction.ext
    intro g
    change a (π.onPoints g) = α a g
    rw [hπpoint]
    exact (hα a g).symm
  have hαinj : Function.Injective α := by
    intro a b hab
    apply P.polynomialFunctionAlgEquiv.symm.injective
    apply Subtype.ext
    exact hab
  have hπsurj : Function.Surjective π.onPoints := by
    have himage : IsZariskiClosed Q (Set.range π.onPoints) := by
      rw [← π.image_carrier]
      exact π.image_isZariskiClosed
    by_contra hnot
    change ¬ ∀ y, ∃ g, π.onPoints g = y at hnot
    obtain ⟨y, hyrange⟩ := not_forall.mp hnot
    change y ∉ Set.range π.onPoints at hyrange
    have hyclosed : ¬ ∀ p ∈ Variety.closedEquations himage,
        evalPolynomial y.val p = 0 := by
      intro hy
      apply hyrange
      rw [Variety.closedEquations_spec himage]
      exact hy
    obtain ⟨p, hp⟩ := not_forall.mp hyclosed
    obtain ⟨hp, hpne⟩ := Classical.not_imp.mp hp
    let a := Variety.PolynomialFunction.ofPolynomial Q p
    have hzero : α a = 0 := by
      apply Variety.PolynomialFunction.ext
      intro g
      rw [← hπpull]
      change a (π.onPoints g) = 0
      have hg : π.onPoints g ∈ Set.range π.onPoints := ⟨g, rfl⟩
      rw [Variety.closedEquations_spec himage] at hg
      exact hg p hp
    have azero : a = 0 := hαinj (by simpa using hzero)
    have := congrArg (fun f : Variety.PolynomialFunction Q => f y) azero
    exact hpne (by simpa [a, Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun] using this)
  refine ⟨Q, inferInstance, P.polynomialFunctionAlgEquiv, π, hπsurj, ?_⟩
  rw [hπpull]
  apply AlgHom.ext
  intro f
  change C.val (P.polynomialFunctionAlgEquiv.symm
    (P.polynomialFunctionAlgEquiv f)) = C.val f
  rw [P.polynomialFunctionAlgEquiv.symm_apply_apply]

public lemma leftTranslate_span_eq_top_of_ne_zero
    (Q : Variety k) [AlgebraicGroup Q]
    (f : Variety.PolynomialFunction Q) (hf : f ≠ 0) :
    Ideal.span (Set.range fun a : Variety.Point Q =>
      (AlgebraicGroup.leftMulMorphism Q a).pullbackAlgHom f) = ⊤ := by
  by_contra hspan
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hspan
  obtain ⟨y, hy⟩ := Variety.exists_pointPrime_eq_of_isMaximal Q m hm
  have hfpoint : ∃ z : Variety.Point Q, f z ≠ 0 := by
    by_contra h
    apply hf
    apply Variety.PolynomialFunction.ext
    intro z
    change f z = 0
    exact not_ne_iff.mp (not_exists.mp h z)
  obtain ⟨z, hz⟩ := hfpoint
  let a : Variety.Point Q := z * y⁻¹
  have htranslate :
      (AlgebraicGroup.leftMulMorphism Q a).pullbackAlgHom f ∈ m :=
    hle (Ideal.subset_span ⟨a, rfl⟩)
  have hzero :
      (AlgebraicGroup.leftMulMorphism Q a).pullbackAlgHom f y = 0 := by
    have hmem :
        (AlgebraicGroup.leftMulMorphism Q a).pullbackAlgHom f ∈
          (Q.pointPrime y).asIdeal := by
      rw [hy]
      exact htranslate
    exact hmem
  change f (a * y) = 0 at hzero
  rw [show a * y = z by simp [a]] at hzero
  exact hz hzero

public lemma pullbackRingHom_flat_of_awayMap_flat
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (π : AlgebraicGroup.Morphism G Q)
    (hπsurj : Function.Surjective π.onPoints)
    (f : Variety.PolynomialFunction Q) (hf : f ≠ 0)
    (hflat : RingHom.Flat
      (Localization.awayMap π.toVariety.pullbackRingHom f)) :
    RingHom.Flat π.toVariety.pullbackRingHom := by
  refine RingHom.Flat.propertyIsLocal.ofLocalizationSpan
    π.toVariety.pullbackRingHom
    (Set.range fun a : Variety.Point Q ↦
      (AlgebraicGroup.leftMulMorphism Q a).pullbackAlgHom f)
    (leftTranslate_span_eq_top_of_ne_zero Q f hf) ?_
  rintro ⟨q, a, rfl⟩
  obtain ⟨g, hg⟩ := hπsurj a
  let eQ := leftTranslateAlgEquiv Q a
  let eG := leftTranslateAlgEquiv G g
  have hcomm :
      eG.toRingEquiv.toRingHom.comp π.toVariety.pullbackRingHom =
        π.toVariety.pullbackRingHom.comp eQ.toRingEquiv.toRingHom := by
    apply RingHom.ext
    intro q
    apply Variety.PolynomialFunction.ext
    intro x
    change q (π.onPoints (g * x)) = q (a * π.onPoints x)
    rw [π.onPoints.map_mul, hg]
  have htransport := awayMap_flat_of_equivariant
    π.toVariety.pullbackRingHom eQ.toRingEquiv eG.toRingEquiv
    hcomm f hflat
  change RingHom.Flat
    (Localization.awayMap π.toVariety.pullbackRingHom
      ((AlgebraicGroup.leftMulMorphism Q a).pullbackAlgHom f)) at htransport
  exact htransport

end

/-! The ambient coordinate algebra is finite type over the invariant coordinate algebra. -/

section
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateRing_finiteType_ambient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Algebra.FiniteType (AlgebraicGroup.rightInvariantCoordinateRing H)
      (Variety.PolynomialFunction G) := by
  let : Algebra.FiniteType k (Variety.PolynomialFunction G) :=
    polynomialFunction_finiteType G
  exact Algebra.FiniteType.of_restrictScalars_finiteType k
    (AlgebraicGroup.rightInvariantCoordinateRing H)
    (Variety.PolynomialFunction G)

end

/-! The finite-ideal criterion for flatness over the invariant coordinate ring. -/

section
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateRing_flat_iff
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Module.Flat (AlgebraicGroup.rightInvariantCoordinateRing H)
        (Variety.PolynomialFunction G) ↔
      ∀ ⦃I : Ideal (AlgebraicGroup.rightInvariantCoordinateRing H)⦄,
        I.FG →
          Function.Injective
            (TensorProduct.lift
              ((LinearMap.lsmul
                (AlgebraicGroup.rightInvariantCoordinateRing H)
                (Variety.PolynomialFunction G)).comp I.subtype)) := by
  exact Module.Flat.iff_lift_lsmul_comp_subtype_injective

end
end Theory.AlgebraicGroup
