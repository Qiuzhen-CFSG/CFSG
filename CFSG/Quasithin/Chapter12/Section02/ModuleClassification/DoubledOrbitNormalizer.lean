module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitLinearCentralizer
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Setup
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Mathlib.Algebra.Module.ZMod

/-!
# The literal full normalizer in the doubled binary branch

Conjugation by N_G(L) acts on the original quotient L/O₂(L). Transport through
the component marking defines the homomorphism to Aut(L_n(2)). The original
conjugation action on W intertwines this homomorphism. The trivial binary
natural-plus-dual centralizer identifies its kernel with the kernel of that
literal W-action. Conversely, faithfulness of the natural summand detects
every component automorphism.

The image contains every inner automorphism. An element moving the original
seed V cannot induce an inner automorphism, since its difference from a
component element would centralize W. The proved inner/graph classification
then makes the image all of Aut(L_n(2)). The resulting quotient equivalence
retains its values on representatives and sends the image of L to Inn(L_n(2)).
No ambient H.9 model is assumed. DoubledOrbitMarking supplies the coordinates
and moving element from the actual FF marked doubled hypotheses.

Source: Aschbacher--Smith, B.5.1(3), H.9 and 12.2.2, printed pp.99,389,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic BinaryNaturalDual
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit

variable {W X : Type*} [Group W] [AddCommGroup X] [Module (ZMod 2) X]

private def coordinateHom (c : W ≃* Multiplicative X) : MulAut W →* (X ≃ₗ[ZMod 2] X) where
  toFun f := by
    let a := (AddEquiv.additiveMultiplicative (G := X)).symm.trans
      (((MulAut.congr c) f).toAdditive.trans (AddEquiv.additiveMultiplicative (G := X)))
    exact { a with map_smul' := ZMod.map_smul a }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change (c (c.symm (Multiplicative.ofAdd v))).toAdd = v
    rw [c.apply_symm_apply]
    rfl
  map_mul' f g := by
    apply LinearEquiv.ext
    intro v
    change (c (f (g (c.symm (Multiplicative.ofAdd v))))).toAdd =
      (c (f (c.symm (c (g (c.symm (Multiplicative.ofAdd v))))))).toAdd
    rw [c.symm_apply_apply]

private theorem coordinateHom_injective (c : W ≃* Multiplicative X) :
    Function.Injective (coordinateHom c) := by
  intro f g h
  apply MulEquiv.ext
  intro w
  have he := LinearEquiv.congr_fun h (c w).toAdd
  change (c (f (c.symm (c w)))).toAdd = (c (g (c.symm (c w)))).toAdd at he
  simpa only [c.symm_apply_apply] using c.injective (Multiplicative.toAdd.injective he)

variable {G : Type*} [Group G] (L : Subgroup G) {n : ℕ}

/-- Conjugation by the original normalizer on the original two-core quotient,
transported through the supplied component marking. -/
def normalizerModelAction (e : (L ⧸ pCore 2 L) ≃* LinearGroup n) :
    normalizer (L : Set G) →* MulAut (LinearGroup n) :=
  (MulAut.congr e).toMonoidHom.comp ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)

/-- Evaluate the marked normalizer action on the original quotient representative. -/
theorem normalizerModelAction_apply (e : (L ⧸ pCore 2 L) ≃* LinearGroup n)
    (x : normalizer (L : Set G)) (l : L) :
    normalizerModelAction L e x (e (QuotientGroup.mk' (pCore 2 L) l)) =
      e (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom x l)) := by
  change e (quotientAut _ _ (e.symm (e _))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]

private theorem modelAction_inner (e : (L ⧸ pCore 2 L) ≃* LinearGroup n) (l : L) :
    normalizerModelAction L e (inclusion L.le_normalizer l) =
      MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) l)) := by
  apply MulEquiv.ext
  intro g
  obtain ⟨a, rfl⟩ := e.surjective g
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) a
  rw [normalizerModelAction_apply]
  change e (QuotientGroup.mk' (pCore 2 L) (l * k * l⁻¹)) = _
  simp only [map_mul, map_inv, MulAut.conj_apply]

open Chapter12.Section01.DoubleNaturalSource
variable (T : Sylow 2 G) (V : Subgroup G)
    (he : componentOrbit V (T : Subgroup G) = componentOrbit V (normalizer (L : Set G)))
    (e : (L ⧸ pCore 2 L) ≃* LinearGroup n)
    (c : componentOrbit V (T : Subgroup G) ≃* Multiplicative (CoordinateSpace n))
    (hc : ∀ (l : L) (w : componentOrbit V (T : Subgroup G)),
      ((c.symm (Multiplicative.ofAdd
        (naturalDualRepresentation (e (QuotientGroup.mk' (pCore 2 L) l))
          (c w).toAdd))) : G) = (l : G) * (w : G) * (l : G)⁻¹)

private def fullCoordinateAction : normalizer (L : Set G) →*
    (CoordinateSpace n ≃ₗ[ZMod 2] CoordinateSpace n) :=
  (coordinateHom c).comp (normalizerAction T L V he)

include hc he

private theorem fullCoordinateAction_inner (l : L) (v : CoordinateSpace n) :
    fullCoordinateAction L T V he c (inclusion L.le_normalizer l) v =
      naturalDualRepresentation (e (QuotientGroup.mk' (pCore 2 L) l)) v := by
  apply Multiplicative.ofAdd.injective
  apply c.symm.injective
  apply Subtype.ext
  have hh := hc l (c.symm (Multiplicative.ofAdd v))
  rw [c.apply_symm_apply] at hh
  change ((c.symm (c ((normalizerAction T L V he) (inclusion L.le_normalizer l)
    (c.symm (Multiplicative.ofAdd v))))) : G) = _
  rw [c.symm_apply_apply]
  exact hh.symm

private theorem fullCoordinateAction_equivariant (x : normalizer (L : Set G))
    (g : LinearGroup n) (v : CoordinateSpace n) :
    fullCoordinateAction L T V he c x (naturalDualRepresentation g v) =
      naturalDualRepresentation (normalizerModelAction L e x g)
        (fullCoordinateAction L T V he c x v) := by
  obtain ⟨q,rfl⟩ := e.surjective g
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  rw [normalizerModelAction_apply, ← fullCoordinateAction_inner L T V he e c hc,
    ← fullCoordinateAction_inner L T V he e c hc]
  change (fullCoordinateAction L T V he c x *
    fullCoordinateAction L T V he c (inclusion L.le_normalizer l)) v =
    (fullCoordinateAction L T V he c (inclusion L.le_normalizer (L.normalizerMonoidHom x l)) *
      fullCoordinateAction L T V he c x) v
  rw [← map_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  change (x : G) * (l : G) = ((x : G) * (l : G) * (x : G)⁻¹) * (x : G)
  group

/-- The model conjugation action has exactly the kernel of the original
normalizer action on the doubled orbit. -/
theorem normalizerModelAction_ker (hn : n = 4 ∨ n = 5) :
    (normalizerModelAction L e).ker = (normalizerAction T L V he).ker := by
  ext x
  change normalizerModelAction L e x = 1 ↔ normalizerAction T L V he x = 1
  constructor
  · intro hx
    apply coordinateHom_injective c
    rw [map_one]
    change fullCoordinateAction L T V he c x = 1
    apply naturalDual_centralizer_trivial hn
    intro g v
    have hh := fullCoordinateAction_equivariant L T V he e c hc x g v
    simpa only [hx, MulAut.one_apply] using hh
  · intro hx
    have hF : fullCoordinateAction L T V he c x = 1 := by
      change coordinateHom c (normalizerAction T L V he x) = 1
      rw [hx,map_one]
    apply MulEquiv.ext
    intro g
    apply LinearEquiv.ext
    intro v
    have hh := fullCoordinateAction_equivariant L T V he e c hc x g (v,0)
    rw [hF] at hh
    change naturalDualRepresentation g (v,0) =
      naturalDualRepresentation (normalizerModelAction L e x g) (v,0) at hh
    have hp := congrArg Prod.fst hh
    simpa only [naturalDualRepresentation_apply, MulAut.one_apply] using hp.symm

/-- An element moving the original seed induces an outer automorphism of the
marked component: an inner action would differ from a component element by
the kernel of the orbit action, which centralizes the seed. -/
theorem normalizerModelAction_outer_of_moves_seed (hn : n = 4 ∨ n = 5)
    (hLV : L ≤ normalizer (V : Set G)) (x : normalizer (L : Set G))
    (hx : (x : G) ∉ normalizer (V : Set G)) :
    normalizerModelAction L e x ∉ MulAut.innerSubgroup (LinearGroup n) := by
  rintro ⟨g,hg⟩
  obtain ⟨q,rfl⟩ := e.surjective g
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  let y := (inclusion L.le_normalizer l)⁻¹ * x
  have hy : y ∈ (normalizerModelAction L e).ker := by
    change normalizerModelAction L e ((inclusion L.le_normalizer l)⁻¹ * x) = 1
    rw [map_mul,map_inv,modelAction_inner,← hg,inv_mul_cancel]
  rw [normalizerModelAction_ker L T V he e c hc hn, normalizerAction_ker] at hy
  have hyW : (y : G) ∈ centralizer (componentOrbit V (T : Subgroup G) : Set G) := hy
  have hyV : (y : G) ∈ centralizer (V : Set G) := by
    apply mem_centralizer_iff.mpr
    intro v hv
    exact mem_centralizer_iff.mp hyW v (le_componentOrbit V (T : Subgroup G) hv)
  have hh := (normalizer (V : Set G)).mul_mem (hLV l.property)
    (centralizer_le_normalizer (V : Set G) hyV)
  apply hx
  change (l : G) * ((l : G)⁻¹ * (x : G)) ∈ normalizer (V : Set G) at hh
  simpa only [mul_inv_cancel_left] using hh

/-- Inner/graph coverage and the actual moving element exhaust the whole
model automorphism group. -/
theorem normalizerModelAction_surjective (hn : n = 4 ∨ n = 5)
    (hLV : L ≤ normalizer (V : Set G))
    (hout : ∃ x : normalizer (L : Set G), (x : G) ∉ normalizer (V : Set G)) :
    Function.Surjective (normalizerModelAction L e) := by
  let A := (normalizerModelAction L e).range
  have hi (g : LinearGroup n) : MulAut.conj g ∈ A := by
    obtain ⟨q,rfl⟩ := e.surjective g
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    exact ⟨inclusion L.le_normalizer l, modelAction_inner L e l⟩
  obtain ⟨x,hx⟩ := hout
  have hxout := normalizerModelAction_outer_of_moves_seed L T V he e c hc hn hLV x hx
  obtain ⟨g,hg | hg⟩ := inner_graph hn (normalizerModelAction L e x)
  · exact (hxout ⟨g,hg.symm⟩).elim
  have ht : graphLinear n ∈ A := by
    have hh := A.mul_mem (show normalizerModelAction L e x ∈ A from ⟨x,rfl⟩)
      (A.inv_mem (hi g))
    simpa only [hg,mul_inv_cancel_right] using hh
  intro a
  obtain ⟨g,rfl | rfl⟩ := inner_graph hn a
  · exact hi g
  · exact A.mul_mem ht (hi g)

/-- The normalizer quotient equivalence induced by literal conjugation on
L/O₂(L), rather than by an abstract comparison of group families. -/
def normalizerFullEquiv (hn : n = 4 ∨ n = 5)
    (hLV : L ≤ normalizer (V : Set G))
    (hout : ∃ x : normalizer (L : Set G), (x : G) ∉ normalizer (V : Set G)) :
    (normalizer (L : Set G) ⧸ (normalizerAction T L V he).ker) ≃*
      MulAut (LinearGroup n) :=
  (QuotientGroup.quotientMulEquivOfEq
    (normalizerModelAction_ker L T V he e c hc hn).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (normalizerModelAction L e)
        (normalizerModelAction_surjective L T V he e c hc hn hLV hout))

/-- The full quotient marking evaluates to the original normalizer's
conjugation action on the original component quotient. -/
theorem normalizerFullEquiv_mk (hn : n = 4 ∨ n = 5)
    (hLV : L ≤ normalizer (V : Set G))
    (hout : ∃ x : normalizer (L : Set G), (x : G) ∉ normalizer (V : Set G))
    (x : normalizer (L : Set G)) :
    normalizerFullEquiv L T V he e c hc hn hLV hout
      (QuotientGroup.mk' (normalizerAction T L V he).ker x) =
        normalizerModelAction L e x := by
  rfl

/-- The full normalizer quotient sends the original component projection
to the inner automorphism for the very same component marking. -/
theorem normalizerFullEquiv_inner (hn : n = 4 ∨ n = 5)
    (hLV : L ≤ normalizer (V : Set G))
    (hout : ∃ x : normalizer (L : Set G), (x : G) ∉ normalizer (V : Set G)) (l : L) :
    normalizerFullEquiv L T V he e c hc hn hLV hout
      (QuotientGroup.mk' (normalizerAction T L V he).ker (inclusion L.le_normalizer l)) =
        MulAut.conj (e (QuotientGroup.mk' (pCore 2 L) l)) :=
  (normalizerFullEquiv_mk L T V he e c hc hn hLV hout _).trans (modelAction_inner L e l)


/-- Under the full quotient marking, the image of the original component
is exactly the inner automorphism subgroup. Both literal quotient maps are
retained by `normalizerFullEquiv_inner`. -/
theorem normalizerFullEquiv_component_image (hn : n = 4 ∨ n = 5)
    (hLV : L ≤ normalizer (V : Set G))
    (hout : ∃ x : normalizer (L : Set G), (x : G) ∉ normalizer (V : Set G)) :
    ((L.subgroupOf (normalizer (L : Set G))).map
      (QuotientGroup.mk' (normalizerAction T L V he).ker)).map
        (normalizerFullEquiv L T V he e c hc hn hLV hout).toMonoidHom =
          MulAut.innerSubgroup (LinearGroup n) := by
  ext a
  constructor
  · rintro ⟨q,⟨l,hl,rfl⟩,rfl⟩
    let l' : L := ⟨l.val,hl⟩
    exact ⟨e (QuotientGroup.mk' (pCore 2 L) l'),
      (normalizerFullEquiv_inner L T V he e c hc hn hLV hout l').symm⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨q,rfl⟩ := e.surjective g
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    exact ⟨QuotientGroup.mk' (normalizerAction T L V he).ker (inclusion L.le_normalizer l),
      ⟨inclusion L.le_normalizer l,l.property,rfl⟩,
      normalizerFullEquiv_inner L T V he e c hc hn hLV hout l⟩

/-- The full original normalizer-action quotient is the automorphism group
of the same marked binary component. -/
theorem normalizer_full_of_marking (hn : n = 4 ∨ n = 5)
    (hLV : L ≤ normalizer (V : Set G))
    (hout : ∃ x : normalizer (L : Set G), (x : G) ∉ normalizer (V : Set G)) :
    Nonempty ((normalizer (L : Set G) ⧸ (normalizerAction T L V he).ker) ≃*
      MulAut (LinearGroup n)) := by
  exact ⟨normalizerFullEquiv L T V he e c hc hn hLV hout⟩

end CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit
