module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.NativeFaithfulness

/-!
# Unique refined abstract Ree coordinates

The independently proved internal double-cell reduction and native kernel give a bijection with u*h*n_w*v, restricting the right tuple to the actual inversion subgroup. Angular and native Bruhat uniqueness prove uniqueness of every coordinate.
Source: GLS3 2.3.5--8 and Steinberg section 11, Theorem 33 and Lemma 62.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.Global
open Subgroup Theory.GroupTheory OrderedRootPresentation
open SignedGeometry WeylPresentation CentralCovers.TwoPrimary
open CentralCovers.OddPrimary.Order

/-- Twelve free field coordinates, in the proved angular root order. -/
abbrev PositiveParameters (m : ℕ) := Tuple (AngularPresentation.Parameter m) sourceOrder

def positiveWord (m : ℕ) (p : PositiveParameters m) : Presentation.Group m :=
  word (AngularPresentation.Parameter m) (fun i => Presentation.root m true i) sourceOrder p

@[simp] theorem nativeEval_positiveWord (m : ℕ) (p : PositiveParameters m) :
    nativeEval m (positiveWord m p) = AngularPresentation.nativeWord m p := by
  rw [positiveWord,map_word]
  congr 1
  funext i a
  exact Presentation.eval_root (native m) (native_relations m) true i a

/-- The right tuple is restricted to the literal inversion subgroup
U ∩ n_w⁻¹ U⁻ n_w; an unrestricted positive tail is not a refined form. -/
def TailParameters (m : ℕ) (w : Weyl) :=
  {p : PositiveParameters m // (AngularPresentation.nativeWord m p : Model m) ∈
    fixedRightUnipotent (NormalizerPresentation.weyl m w)}

abbrev RefinedParameters (m : ℕ) :=
  Σ w : Weyl, PositiveParameters m × TorusParameter m × TailParameters m w

def refinedWord (m : ℕ) (z : RefinedParameters m) : Presentation.Group m :=
  positiveWord m z.2.1 * Presentation.torus m (fixedTorusEquiv m z.2.2.1) *
    Presentation.weyl m z.1 * positiveWord m z.2.2.2.val

/-- Native normal forms give refined abstract existence AFTER the independent
internal collection and kernel proof. No uniqueness or kernel callback is an input. -/
theorem refinedWord_surjective (m : ℕ) : Function.Surjective (refinedWord m) := by
  intro g
  obtain ⟨⟨n,u,v⟩,he⟩ := (normalFormMap_bijective m).surjective (nativeEval m g)
  let a := (NormalizerPresentation.nativeEquiv m).symm n
  have hn : (a.left : Model m) * NormalizerPresentation.weyl m a.right = n := by
    exact (NormalizerPresentation.nativeEquiv_apply m a).symm.trans
      (congrArg Subtype.val ((NormalizerPresentation.nativeEquiv m).apply_symm_apply n))
  let p := (AngularPresentation.nativeCoordinates m).symm u
  let vU : Parabolics.unipotent m := ⟨v,v.property.1⟩
  let q := (AngularPresentation.nativeCoordinates m).symm vU
  have hp : AngularPresentation.nativeWord m p = u := (AngularPresentation.nativeCoordinates m).apply_symm_apply u
  have hq : AngularPresentation.nativeWord m q = vU := (AngularPresentation.nativeCoordinates m).apply_symm_apply vU
  have hqmem : (AngularPresentation.nativeWord m q : Model m) ∈
      fixedRightUnipotent (NormalizerPresentation.weyl m a.right) := by
    rw [hq, ← fixedRightUnipotent_torus_mul a.left.property,hn]
    exact v.property
  refine ⟨⟨a.right,p,(fixedTorusEquiv m).symm a.left,⟨q,hqmem⟩⟩,?_⟩
  apply nativeEval_injective m
  simp only [refinedWord,map_mul,nativeEval_positiveWord,nativeEval_torus,nativeEval_weyl,
    MulEquiv.apply_symm_apply,hp,hq]
  change (u : Model m) * a.left * NormalizerPresentation.weyl m a.right * v = nativeEval m g
  rw [mul_assoc (u : Model m),hn]
  exact he

/-- The abstract restricted factors are unique, using native Bruhat uniqueness
and the already proved angular, torus and Weyl coordinate injections. -/
theorem refinedWord_injective (m : ℕ) : Function.Injective (refinedWord m) := by
  intro z z' hz
  let middle (w : Weyl) (t : TorusParameter m) : SectionGeometry.BNPair.normalizerWords m :=
    NormalizerPresentation.nativeEquiv m ⟨fixedTorusEquiv m t,w⟩
  let form (z : RefinedParameters m) :
      Σ n : SectionGeometry.BNPair.normalizerWords m,
        Parabolics.unipotent m × fixedRightUnipotent n.val :=
    ⟨middle z.1 z.2.2.1,AngularPresentation.nativeWord m z.2.1,
      ⟨AngularPresentation.nativeWord m z.2.2.2.val, by
        change (AngularPresentation.nativeWord m z.2.2.2.val : Model m) ∈
          fixedRightUnipotent ((fixedTorusEquiv m z.2.2.1 : Model m) * NormalizerPresentation.weyl m z.1)
        rw [fixedRightUnipotent_torus_mul (fixedTorusEquiv m z.2.2.1).property]
        exact z.2.2.2.property⟩⟩
  have he : normalFormMap m (form z) = normalFormMap m (form z') := by
    have he := congrArg (nativeEval m) hz
    simpa only [refinedWord,map_mul,nativeEval_positiveWord,nativeEval_torus,nativeEval_weyl,
      normalFormMap,form,middle,NormalizerPresentation.nativeEquiv_apply,mul_assoc] using he
  have hf := (normalFormMap_bijective m).injective he
  have hn : middle z.1 z.2.2.1 = middle z'.1 z'.2.2.1 := congrArg Sigma.fst hf
  have hn' := (NormalizerPresentation.nativeEquiv m).injective hn
  have hw : z.1 = z'.1 := congrArg SemidirectProduct.right hn'
  have ht : z.2.2.1 = z'.2.2.1 := (fixedTorusEquiv m).injective (congrArg SemidirectProduct.left hn')
  have hu : z.2.1 = z'.2.1 := (AngularPresentation.nativeWord_bijective m).injective
    (congrArg (fun x => x.2.1) hf)
  have hv : z.2.2.2.val = z'.2.2.2.val := (AngularPresentation.nativeWord_bijective m).injective
    (Subtype.ext (congrArg (fun x => (x.2.2 : Model m)) hf))
  rcases z with ⟨w,p,t,q⟩
  rcases z' with ⟨w',p',t',q'⟩
  dsimp only at hw ht hu hv
  subst w'
  subst t'
  subst p'
  have hq : q = q' := Subtype.ext hv
  subst q'
  rfl

/-- A bijection with the refined u*h*n_w*v coordinate space, uniformly in m. -/
def refinedCoordinates (m : ℕ) : RefinedParameters m ≃ Presentation.Group m :=
  Equiv.ofBijective _ ⟨refinedWord_injective m,refinedWord_surjective m⟩

end ReeF4.RootPresentationRecognition.Global
