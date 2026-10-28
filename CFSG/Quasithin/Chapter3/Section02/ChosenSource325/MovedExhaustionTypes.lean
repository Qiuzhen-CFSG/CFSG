module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.Models
public import Theory.Representation.BinaryOffender.Homogeneous.QuotientTwist
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Constituent types in the full normalizer orbit

Normalizer conjugation descends through a characteristic action kernel to
an automorphism of the actual constituent model. Two automorphism twists
therefore give two unchanged-L module types on all normalizer conjugates.
If the full orbit exceeds the Sylow orbit, inverse conjugation by the marked
moving Sylow element produces a same-type copy outside the Sylow orbit.
This argument makes no homogeneity or multiplicity assumption on the larger
orbit. Its chosen-seed application is `SeedAlternativesMovedExhaustionTypes`.

Source: Aschbacher--Smith D.3.10, the paragraph following D.3.11, printed
p.201. The later cubic argument excluding repeated copies remains separate.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {G P W : Type*} [Group G] [Group P]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Conjugation transports a module comparison while keeping the actor L fixed. -/
theorem SameConjugationModule.conjugate {L V V' : Subgroup G}
    (he : SameConjugationModule L V V') (g : normalizer (L : Set G)) :
    SameConjugationModule L (V.map (MulAut.conj g.val).toMonoidHom)
      (V'.map (MulAut.conj g.val).toMonoidHom) := by
  obtain ⟨e,he⟩ := he
  let j := (MulAut.conj g.val).subgroupMap V
  let j' := (MulAut.conj g.val).subgroupMap V'
  refine ⟨j.symm.trans (e.trans j'),?_⟩
  intro l v w hw
  have hc : (j.symm w : G) =
      (L.normalizerMonoidHom g⁻¹ l : G) * (j.symm v : G) *
        (L.normalizerMonoidHom g⁻¹ l : G)⁻¹ := by
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv, inv_inv]
    change g.val⁻¹ * w.val * g.val =
      (g.val⁻¹ * l.val * g.val) * (g.val⁻¹ * v.val * g.val) *
        (g.val⁻¹ * l.val * g.val)⁻¹
    rw [hw]
    group
  have hh := he (L.normalizerMonoidHom g⁻¹ l) (j.symm v) (j.symm w) hc
  change g.val * (e (j.symm w) : G) * g.val⁻¹ =
    l.val * (g.val * (e (j.symm v) : G) * g.val⁻¹) * l.val⁻¹
  rw [hh]
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv, inv_inv]
  group

/-- The two original ambient conjugation maps compose in their actual order. -/
theorem map_conj_map_conj (V : Subgroup G) (g h : G) :
    (V.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      V.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  change g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹
  group

/-- Two types in the full normalizer orbit reduce a strict enlargement to an
actual same-type copy outside the Sylow orbit. No full-orbit homogeneity is used. -/
theorem exists_repeated_conjugate_of_larger_orbit
    {L V : Subgroup G} {T : Subgroup G}
    (hTN : T ≤ normalizer (L : Set G)) (t : T)
    (htypes : ∀ g ∈ normalizer (L : Set G),
      SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) ∨
      SameConjugationModule L (V.map (MulAut.conj t.val).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom))
    (hne : Theory.GroupTheory.componentOrbit V (normalizer (L : Set G)) ≠
      Theory.GroupTheory.componentOrbit V T) :
    ∃ g ∈ normalizer (L : Set G),
      SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ Theory.GroupTheory.componentOrbit V T := by
  let U := Theory.GroupTheory.componentOrbit V (normalizer (L : Set G))
  let B := Theory.GroupTheory.componentOrbit V T
  have hBU : B ≤ U := iSup_le fun s => le_iSup_of_le (⟨s.val,hTN s.property⟩ :
    normalizer (L : Set G)) le_rfl
  have hsome : ∃ g : normalizer (L : Set G),
      ¬ V.map (MulAut.conj g.val).toMonoidHom ≤ B := by
    by_contra! hn
    exact hne (le_antisymm (iSup_le hn) hBU)
  obtain ⟨g,hg⟩ := hsome
  rcases htypes g g.property with he | he
  · exact ⟨g,g.property,he,hg⟩
  · let s : normalizer (L : Set G) := ⟨t.val,hTN t.property⟩
    have he' := he.conjugate s⁻¹
    rw [map_conj_map_conj,map_conj_map_conj] at he'
    have hone : V.map (MulAut.conj (t.val⁻¹ * t.val)).toMonoidHom = V := by
      simp only [inv_mul_cancel,map_one]
      exact Subgroup.map_id (K := V)
    change SameConjugationModule L
      (V.map (MulAut.conj (t.val⁻¹ * t.val)).toMonoidHom)
      (V.map (MulAut.conj (t.val⁻¹ * g.val)).toMonoidHom) at he'
    rw [hone] at he'
    refine ⟨t.val⁻¹ * g.val,(normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).inv_mem (hTN t.property)) g.property,he',?_⟩
    intro hh
    have hm := map_mono (f := (MulAut.conj t.val).toMonoidHom) hh
    rw [map_conj_map_conj,mul_inv_cancel_left] at hm
    have hBn : t.val ∈ normalizer (B : Set G) :=
      Theory.GroupTheory.le_normalizer_componentOrbit V T t.property
    exact hg (hm.trans (mem_normalizer_iff_map_conj_eq.mp hBn).le)

/-- Coordinates for the literal L-conjugation action on V, through a specified
actor homomorphism. The intertwiner uses equality in the original group G. -/
structure ConjugationCoordinates (L V : Subgroup G)
    (τ : Representation (ZMod 2) P W) (f : L →* P) where
  normalizes : L ≤ normalizer (V : Set G)
  equiv : V ≃* Multiplicative W
  intertwines : ∀ (l : L) (v w : V),
    (w : G) = (l : G) * (v : G) * (l : G)⁻¹ →
    (equiv w).toAdd = τ (f l) (equiv v).toAdd

namespace ConjugationCoordinates
variable {L V V' : Subgroup G} {τ τ' : Representation (ZMod 2) P W} {f : L →* P}

/-- Change only the module coordinates, preserving the original actor map. -/
def changeModel (c : ConjugationCoordinates L V τ f) (b : τ.Equiv τ') :
    ConjugationCoordinates L V τ' f where
  normalizes := c.normalizes
  equiv := c.equiv.trans b.toLinearEquiv.toAddEquiv.toMultiplicative
  intertwines l v w hw := by
    change b (c.equiv w).toAdd = τ' (f l) (b (c.equiv v).toAdd)
    rw [c.intertwines l v w hw]
    exact IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap (f l) _

/-- Two copies with the same coordinates are isomorphic for the unchanged L. -/
theorem sameModule (c : ConjugationCoordinates L V τ f)
    (d : ConjugationCoordinates L V' τ f) : SameConjugationModule L V V' := by
  let e := c.equiv.trans d.equiv.symm
  refine ⟨e, fun l v w hw => ?_⟩
  let z : V' := ⟨l.val * (e v).val * l.val⁻¹,
    (mem_normalizer_iff.mp (d.normalizes l.property) _).mp (e v).property⟩
  have he : e w = z := by
    apply d.equiv.injective
    apply Multiplicative.toAdd.injective
    change (d.equiv (d.equiv.symm (c.equiv w))).toAdd = (d.equiv z).toAdd
    rw [d.equiv.apply_symm_apply, d.intertwines l (e v) z rfl,
      c.intertwines l v w hw]
    change τ (f l) (c.equiv v).toAdd =
      τ (f l) (d.equiv (d.equiv.symm (c.equiv v))).toAdd
    rw [d.equiv.apply_symm_apply]
  exact congrArg Subtype.val he

/-- The actual automorphism induced by inverse conjugation on the model quotient. -/
def quotientTwist (f : L →* P) (hf : Function.Surjective f) [f.ker.Characteristic]
    (g : normalizer (L : Set G)) : MulAut P :=
  let q := QuotientGroup.quotientKerEquivOfSurjective f hf
  q.symm.trans ((quotientAut f.ker (L.normalizerMonoidHom g⁻¹)).trans q)

/-- The quotient automorphism agrees with the original normalizer action. -/
theorem quotientTwist_apply (hf : Function.Surjective f) [f.ker.Characteristic]
    (g : normalizer (L : Set G)) (l : L) :
    quotientTwist f hf g (f l) = f (L.normalizerMonoidHom g⁻¹ l) := by
  let q := QuotientGroup.quotientKerEquivOfSurjective f hf
  change q (quotientAut f.ker (L.normalizerMonoidHom g⁻¹) (q.symm (f l))) = _
  have hq : f l = q (QuotientGroup.mk' f.ker l) := rfl
  rw [hq,q.symm_apply_apply,quotientAut_apply_mk]
  rfl

/-- A normalizer conjugate has the model twisted by the induced quotient
automorphism, using the actual ambient conjugation equivalence. -/
def conjugate (c : ConjugationCoordinates L V τ f)
    (hf : Function.Surjective f) [f.ker.Characteristic]
    (g : normalizer (L : Set G)) :
    ConjugationCoordinates L (V.map (MulAut.conj g.val).toMonoidHom)
      (τ.comp (quotientTwist f hf g).toMonoidHom) f := by
  let j := (MulAut.conj g.val).subgroupMap V
  refine ⟨?_,j.symm.trans c.equiv,?_⟩
  · rw [← map_equiv_normalizer_eq V (MulAut.conj g.val)]
    exact (mem_normalizer_iff_map_conj_eq.mp g.property).ge.trans (map_mono c.normalizes)
  · intro l v w hw
    change (c.equiv (j.symm w)).toAdd =
      τ (quotientTwist f hf g (f l)) (c.equiv (j.symm v)).toAdd
    rw [quotientTwist_apply]
    apply c.intertwines (L.normalizerMonoidHom g⁻¹ l) (j.symm v) (j.symm w)
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv, inv_inv]
    change g.val⁻¹ * (w : G) * g.val =
      (g.val⁻¹ * l.val * g.val) * (g.val⁻¹ * v.val * g.val) *
        (g.val⁻¹ * l.val * g.val)⁻¹
    rw [hw]
    group

end ConjugationCoordinates

/-- Two automorphism twists give two module types on the entire normalizer
orbit. The second is marked by the supplied nonisomorphic conjugate. -/
theorem two_conjugation_types_of_characteristic_model
    {L V : Subgroup G} {τ τ' : Representation (ZMod 2) P W} {f : L →* P}
    (c : ConjugationCoordinates L V τ f)
    (hf : Function.Surjective f) [f.ker.Characteristic]
    (htypes : ∀ a : MulAut P,
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ'))
    (t : normalizer (L : Set G))
    (hnt : ¬ SameConjugationModule L V (V.map (MulAut.conj t.val).toMonoidHom)) :
    ∀ g : normalizer (L : Set G),
      SameConjugationModule L V (V.map (MulAut.conj g.val).toMonoidHom) ∨
      SameConjugationModule L (V.map (MulAut.conj t.val).toMonoidHom)
        (V.map (MulAut.conj g.val).toMonoidHom) := by
  have ht : Nonempty (ConjugationCoordinates L
      (V.map (MulAut.conj t.val).toMonoidHom) τ' f) := by
    rcases htypes (ConjugationCoordinates.quotientTwist f hf t) with hb | hb
    · obtain ⟨b⟩ := hb
      exact (hnt (c.sameModule ((c.conjugate hf t).changeModel b))).elim
    · obtain ⟨b⟩ := hb
      exact ⟨(c.conjugate hf t).changeModel b⟩
  obtain ⟨d⟩ := ht
  intro g
  rcases htypes (ConjugationCoordinates.quotientTwist f hf g) with hb | hb
  · obtain ⟨b⟩ := hb
    exact Or.inl (c.sameModule ((c.conjugate hf g).changeModel b))
  · obtain ⟨b⟩ := hb
    exact Or.inr (d.sameModule ((c.conjugate hf g).changeModel b))

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
