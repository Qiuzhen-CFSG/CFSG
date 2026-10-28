module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Inputs
public import Theory.Representation.TensorInvolutionIntertwiners

/-!
# Recovering actual actors from paired SL₃ component coordinates

Interchange on two conjugate half representations induces the same component
automorphism as the original Schur-linear actor. Absolute irreducibility makes
their ratio scalar, and their square-one equations remove that scalar in
characteristic two. A fixed involutory lift of a nonidentity companion acts
diagonally. Faithful scalar extension detects its nontriviality without assuming
that the original SL₃ representation is faithful.

The paired-coordinate comparison is adapted from the checked symplectic
`OuterSchurDegree.Realization.Paired`, keeping its original source intact.
Source: GM, Classification of 2F-modules II, Proposition 4.8 steps 2–5,
manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization

variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]

omit [FiniteDimensional (ZMod 2) V] [IsIrreducible σ] in
/-- The lift intertwines the literal operators over the component Schur field. -/
theorem LiftedInvolution.schur_intertwines {t : linearNormalizer σ}
    (L : LiftedInvolution B σ t) (ht : IsSchurLinear σ t) (g : SL(3,B.Carrier)) :
    schurActor σ t ht * σ.endFieldRep g =
      σ.endFieldRep (L.automorphism g) * schurActor σ t ht := by
  ext v
  apply σ.asModuleEquiv.injective
  exact LinearMap.congr_fun (L.intertwines g) (σ.asModuleEquiv v)

/-- The lifted component action is preserved on the original scalar extension. -/
theorem LiftedInvolution.absolute_intertwines {t : linearNormalizer σ}
    (L : LiftedInvolution B σ t) (ht : IsSchurLinear σ t) (g : SL(3,B.Carrier)) :
    absoluteActor σ (SplittingField σ) t ht *
        extendScalars (SplittingField σ) σ.endFieldRep g =
      extendScalars (SplittingField σ) σ.endFieldRep (L.automorphism g) *
        absoluteActor σ (SplittingField σ) t ht := by
  change LinearMap.baseChange _ _ * LinearMap.baseChange _ _ =
    LinearMap.baseChange _ _ * LinearMap.baseChange _ _
  rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, L.schur_intertwines ht]

/-- A component representative gives exactly the extended component operator. -/
theorem absoluteActor_eq_component (t : linearNormalizer σ) (ht : IsSchurLinear σ t)
    (x : SL(3,B.Carrier)) (hx : t.val = σ.asGroupHom x) :
    absoluteActor σ (SplittingField σ) t ht =
      extendScalars (SplittingField σ) σ.endFieldRep x := by
  have h : schurActor σ t ht = σ.endFieldRep x := by
    ext v
    exact congrArg σ.asModuleEquiv.symm
      (LinearMap.congr_fun (congrArg Units.val hx) (σ.asModuleEquiv v))
  exact congrArg (LinearMap.baseChange (SplittingField σ)) h

/-- Scalar extension cannot turn a nonidentity original operator into identity. -/
theorem eq_one_of_absoluteActor_eq_one (t : linearNormalizer σ)
    (ht : IsSchurLinear σ t)
    (h : absoluteActor σ (SplittingField σ) t ht = 1) : t = 1 := by
  have hs : schurActor σ t ht = 1 := by
    ext v
    apply (Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := SchurField σ) (B := SplittingField σ) σ.asModule)
    exact congrArg (fun f : Module.End (SplittingField σ)
      (SplittingField σ ⊗[SchurField σ] σ.asModule) => f (1 ⊗ₜ[SchurField σ] v)) h
  apply Subtype.ext
  apply Units.ext
  ext v
  exact congrArg σ.asModuleEquiv
    (LinearMap.congr_fun hs (σ.asModuleEquiv.symm v))

/-- Paired component coordinates force the given outer operator to be interchange. -/
theorem PairedTensorCoordinates.outer_action {t : linearNormalizer σ}
    (L : LiftedInvolution B σ t) (ht : IsSchurLinear σ t)
    (P : PairedTensorCoordinates B σ L.automorphism) (v) :
    P.equiv (absoluteActor σ (SplittingField σ) t ht v) =
      TensorInterchange.flip (SplittingField σ) P.size (P.equiv v) := by
  let K := SplittingField σ
  let W := Fin P.size → K
  let τ := extendScalars K σ.endFieldRep
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible τ := IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep K
  let : Nontrivial (K ⊗[SchurField σ] σ.asModule) :=
    Subrepresentation.irreducible_module_nontrivial τ
  let swap := TensorProduct.comm K W W
  let S := P.equiv.trans (swap.trans P.equiv.symm)
  have hS (w) : P.equiv (S w) = swap (P.equiv w) := by simp [S]
  have hSS : S.toLinearMap * S.toLinearMap = 1 := by
    apply LinearMap.ext
    intro w
    apply P.equiv.injective
    change P.equiv (S (S w)) = P.equiv w
    simp only [hS]
    simp [swap]
  have hSi (g : SL(3,B.Carrier)) :
      S.toLinearMap * τ g = τ (L.automorphism g) * S.toLinearMap := by
    apply LinearMap.ext
    intro w
    apply P.equiv.injective
    have hgg : L.automorphism (L.automorphism g) = g :=
      DFunLike.congr_fun L.square g
    change P.equiv (S (τ g w)) = P.equiv (τ (L.automorphism g) (S w))
    rw [hS, P.component_action, P.component_action, hgg, hS]
    exact (TensorProduct.map_comm _ _ _).symm
  have he := TensorInvolutionIntertwiners.same_automorphism_involutions_eq
    τ L.automorphism (absoluteActor σ K t ht) S
    (L.absolute_intertwines ht) hSi
    (by simpa only [pow_two] using absoluteActor_square σ K t ht L.actor_square) hSS
  rw [he]
  exact hS v

/-- A fixed involutory lift supplies a nonidentity diagonal map on the same half. -/
theorem PairedTensorCoordinates.diagonal_action {α : MulAut SL(3,B.Carrier)}
    (P : PairedTensorCoordinates B σ α) (u : linearNormalizer σ)
    (hu : IsSchurLinear σ u) (hne : u ≠ 1)
    (x : SL(3,B.Carrier)) (hx2 : x ^ 2 = 1) (hfix : α x = x)
    (hx : u.val = σ.asGroupHom x) :
    (P.half x) ^ 2 = 1 ∧ P.half x ≠ 1 ∧ ∀ v,
      P.equiv (absoluteActor σ (SplittingField σ) u hu v) =
        TensorProduct.map (P.half x) (P.half x) (P.equiv v) := by
  have hact (v) : P.equiv (absoluteActor σ (SplittingField σ) u hu v) =
      TensorProduct.map (P.half x) (P.half x) (P.equiv v) := by
    rw [absoluteActor_eq_component u hu x hx, P.component_action, hfix]
  refine ⟨by rw [← map_pow, hx2, map_one], ?_, hact⟩
  intro he
  apply hne
  apply eq_one_of_absoluteActor_eq_one u hu
  apply LinearMap.ext
  intro v
  apply P.equiv.injective
  simpa only [he, TensorProduct.map_one, Module.End.one_apply] using hact v

/-- Build the published exchange realization from component geometry and an
actual companion. No faithfulness of the SL₃ cover is assumed. -/
def swapRealization_of_pairedCoordinates {A : Subgroup (linearNormalizer σ)}
    (hs : ∀ t ∈ A, IsSchurLinear σ t) (t : A)
    (L : LiftedInvolution B σ t.val)
    (P : PairedTensorCoordinates B σ L.automorphism)
    (hc : 2 < rank A → HasInnerCompanion B σ A L.automorphism) :
    SwapRealization B σ A hs where
  size := P.size
  three_le := P.three_le
  equiv := P.equiv
  outer := t
  outer_action := P.outer_action L (hs _ t.property)
  pair_action hr := by
    obtain ⟨u, hune, x, hx2, hfix, hx⟩ := hc hr
    exact ⟨u, P.half x, P.diagonal_action u.val (hs _ u.property)
      (fun h => hune (Subtype.ext h)) x hx2 hfix hx⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
