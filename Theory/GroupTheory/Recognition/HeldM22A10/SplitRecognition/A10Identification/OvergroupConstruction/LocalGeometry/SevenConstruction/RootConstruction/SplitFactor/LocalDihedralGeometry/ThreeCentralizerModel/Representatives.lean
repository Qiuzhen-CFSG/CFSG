module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizerModel.BlockCoordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizerModel.TailCoordinates
import Mathlib.Tactic

/-!
# Marked products for both cubic representatives

Combine the six-letter C3 × S3 maps with the four-letter centralizer, and
impose even parity. Since the tail maps preserve sign, the second factor
is exactly the even block model of C_A7((01)(23)). The inverse tail map
proves surjectivity of the resulting homomorphism. Transport through the
block equivalences gives genuine isomorphisms onto both full centralizers,
with the involution and root tracked separately.

Source: Held, DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

public section

open Subgroup Equiv Equiv.Perm
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizer

abbrev C3 := Tail.C3

@[expose] def centralizerEquiv {H K : Type*} [Group H] [Group K] (f : H ≃* K) (c : H) :
    centralizer ({c} : Set H) ≃* centralizer ({f c} : Set K) where
  toFun x := ⟨f x, mem_centralizer_singleton_iff.mpr
    ((show Commute (x : H) c from mem_centralizer_singleton_iff.mp x.property).map f).eq⟩
  invFun x := ⟨f.symm x, mem_centralizer_singleton_iff.mpr (by
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x)
  right_inv x := Subtype.ext (f.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul f (x : H) (y : H))

@[expose] def repPair (t : Bool) : Pair 6 := ⟨(1, Tail.root t), by
  change sign (1 : Perm (Fin 4)) * sign (Tail.root t) = 1
  rw [map_one, one_mul, Tail.root_sign]⟩

abbrev RepCentralizer (t : Bool) := centralizer ({repPair t} : Set (Pair 6))

@[expose] noncomputable def productHom (t : Bool) : C3 × Pair 3 →* Pair 6 where
  toFun x := ⟨(x.2.val.1, (Tail.equiv t (x.1, x.2.val.2)).val), by
    change sign x.2.val.1.val * sign (Tail.equiv t (x.1, x.2.val.2)).val = 1
    rw [Tail.equiv_sign]
    exact x.2.property⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val (map_one (Tail.equiv t))
  map_mul' x y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val (map_mul (Tail.equiv t) (x.1, x.2.val.2) (y.1, y.2.val.2))

@[expose] noncomputable def localHom (t : Bool) : C3 × Pair 3 →* RepCentralizer t :=
  (productHom t).codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply Prod.ext
    · exact mul_one _ |>.trans (one_mul _).symm
    · exact mem_centralizer_singleton_iff.mp (Tail.equiv t (x.1, x.2.val.2)).property)

theorem localHom_injective (t : Bool) : Function.Injective (localHom t) := by
  intro x y h
  have hf : x.2.val.1 = y.2.val.1 := congrArg (fun z : RepCentralizer t => z.val.val.1) h
  have ht : Tail.equiv t (x.1, x.2.val.2) = Tail.equiv t (y.1, y.2.val.2) :=
    Subtype.ext (congrArg (fun z : RepCentralizer t => z.val.val.2) h)
  have he := (Tail.equiv t).injective ht
  exact Prod.ext (Prod.mk.inj he).1 (Subtype.ext (Prod.ext hf (Prod.mk.inj he).2))

theorem localHom_surjective (t : Bool) : Function.Surjective (localHom t) := by
  intro z
  have hc : z.val.val.2 ∈ Tail.Centralizer t := by
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun x : Pair 6 => x.val.2) (mem_centralizer_singleton_iff.mp z.property)
  let p := (Tail.equiv t).symm ⟨z.val.val.2, hc⟩
  have hp : Tail.equiv t p = ⟨z.val.val.2, hc⟩ := (Tail.equiv t).apply_symm_apply _
  have hs : sign p.2 = sign z.val.val.2 := by
    rw [← Tail.equiv_sign t p, hp]
  let q : Pair 3 := ⟨(z.val.val.1, p.2), by
    change sign z.val.val.1.val * sign p.2 = 1
    rw [hs]
    exact z.val.property⟩
  refine ⟨(p.1, q), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val hp

@[expose] noncomputable def localEquiv (t : Bool) : C3 × Pair 3 ≃* RepCentralizer t :=
  MulEquiv.ofBijective (localHom t) ⟨localHom_injective t, localHom_surjective t⟩

@[expose] def representative (t : Bool) : MuModel := muHom (repPair t)

@[expose] noncomputable def productEquiv (t : Bool) : LocalProductModel ≃*
    centralizer ({representative t} : Set MuModel) :=
  (MulEquiv.prodCongr (MulEquiv.refl C3) sevenEquiv.symm).trans
    ((localEquiv t).trans (centralizerEquiv muEquiv (repPair t)))

theorem productEquiv_involution (t : Bool) :
    productEquiv t (1, sevenCentralInvolution) = modelMuAt (representative t) := by
  have hs : sevenEquiv.symm sevenCentralInvolution = muPair 3 :=
    sevenEquiv.symm_apply_eq.mpr sevenEquiv_mark.symm
  apply Subtype.ext
  change muEquiv (productHom t (1, sevenEquiv.symm sevenCentralInvolution)) = modelMu
  rw [hs, ← muEquiv_mark]
  apply congrArg muEquiv
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val (map_one (Tail.equiv t))

theorem productEquiv_root (t : Bool) :
    productEquiv t (Multiplicative.ofAdd 1, 1) = modelRootAt (representative t) := by
  apply Subtype.ext
  change muEquiv (productHom t (Multiplicative.ofAdd 1, sevenEquiv.symm 1)) = muEquiv (repPair t)
  rw [map_one sevenEquiv.symm]
  apply congrArg muEquiv
  apply Subtype.ext
  exact Prod.ext rfl (Tail.equiv_root t)

@[expose] noncomputable def representativeModel (t : Bool) : ModelThreeCentralizer (representative t) where
  equiv := (productEquiv t).symm
  involution := (productEquiv t).symm_apply_eq.mpr (productEquiv_involution t).symm
  root := by
    rw [← productEquiv_root, MulEquiv.symm_apply_apply]

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizer
