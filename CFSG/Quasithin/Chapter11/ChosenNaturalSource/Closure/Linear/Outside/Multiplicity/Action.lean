module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Transport
public import Theory.Representation.ScalarMultiplicity
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.GeneralLinearNatural

/-!
# The actual multiplicity action on two natural copies

A marking of W/V₁ by two natural SL₂ copies retains both the original
quotient map and the original K action. The additive scalar-commutant theorem
constructs an F-linear action on the copy indices. Its kernel is exactly the
kernel of conjugation on W/V₁. Thus the literal faithful action quotient
embeds in GL₂(F), with its compatibility equation retained.

Source: Aschbacher--Smith, 11.5.7, printed p.782.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- Compatible two-copy coordinates supplied by the SL₃ block. This contains
no multiplicity action or centralizer-embedding conclusion. -/
structure NaturalPair where
  actor : (E.K ⧸ pCore 2 E.K) ≃* Matrix.SpecialLinearGroup (Fin 2) E.input.field.Carrier
  coordinates : (E.W ⧸ E.V₁.subgroupOf E.W) ≃*
    Multiplicative (Fin 2 → Fin 2 → E.input.field.Carrier)
  natural : ∀ (k : E.K) (w : E.W ⧸ E.V₁.subgroupOf E.W),
    (coordinates (quotientAction E E.K E.K_le_G₁ k w)).toAdd =
      fun i => (actor (QuotientGroup.mk' (pCore 2 E.K) k)).val.mulVec
        ((coordinates w).toAdd i)

namespace NaturalPair
variable {E} (m : NaturalPair E)

/-- A marking on the source image in G₁/V₁ gives the same marking on the
intrinsic quotient, through the original restricted quotient map. -/
def ofTilde
    (actor : (E.K ⧸ pCore 2 E.K) ≃*
      Matrix.SpecialLinearGroup (Fin 2) E.input.field.Carrier)
    (e : E.tilde E.W ≃* Multiplicative (Fin 2 → Fin 2 → E.input.field.Carrier))
    (he : ∀ (k : E.K) (w : E.tilde E.W),
      (e (E.tildeConjugation E.W E.K E.K_le_G₁
        (E.K_le_G₁.trans (le_normalizer_conjugateSpanBy V E.G₁)) k w)).toAdd =
        fun i => (actor (QuotientGroup.mk' (pCore 2 E.K) k)).val.mulVec ((e w).toAdd i)) :
    NaturalPair E where
  actor := actor
  coordinates := (quotientTildeEquiv E).trans e
  natural k w := by
    simp only [MulEquiv.trans_apply, quotientTildeEquiv_action]
    exact he k (quotientTildeEquiv E w)

/-- Conjugation transported through the supplied natural coordinates. -/
def action (A : Subgroup G) (hA : A ≤ E.G₁) :
    Representation (ZMod 2) A (Fin 2 → Fin 2 → E.input.field.Carrier) where
  toFun a :=
    (AddMonoidHom.toMultiplicative.symm
      (m.coordinates.symm.trans ((quotientAction E A hA a).trans m.coordinates)).toMonoidHom).toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro w
    change (m.coordinates (quotientAction E A hA 1
      (m.coordinates.symm (Multiplicative.ofAdd w)))).toAdd = w
    rw [map_one]
    exact congrArg Multiplicative.toAdd (m.coordinates.apply_symm_apply _)
  map_mul' a b := by
    apply LinearMap.ext
    intro w
    change (m.coordinates (quotientAction E A hA (a*b)
      (m.coordinates.symm (Multiplicative.ofAdd w)))).toAdd =
        (m.coordinates (quotientAction E A hA a
          (m.coordinates.symm (m.coordinates (quotientAction E A hA b
            (m.coordinates.symm (Multiplicative.ofAdd w))))))).toAdd
    rw [map_mul]
    rw [m.coordinates.symm_apply_apply]
    rfl

theorem action_apply (A : Subgroup G) (hA : A ≤ E.G₁) (a : A)
    (w : Fin 2 → Fin 2 → E.input.field.Carrier) :
    m.action A hA a w =
      (m.coordinates (quotientAction E A hA a
        (m.coordinates.symm (Multiplicative.ofAdd w)))).toAdd := rfl

/-- The binary kernel in these coordinates is the literal action centralizer. -/
theorem action_kernel (A : Subgroup G) (hA : A ≤ E.G₁) :
    (m.action A hA).ker = actionCentralizer E A hA := by
  ext a
  constructor
  · intro ha
    apply MonoidHom.mem_ker.mpr
    ext w
    apply m.coordinates.injective
    apply Multiplicative.toAdd.injective
    have he := LinearMap.congr_fun ha (m.coordinates w).toAdd
    change (m.coordinates (quotientAction E A hA a (m.coordinates.symm (m.coordinates w)))).toAdd = _ at he
    rwa [m.coordinates.symm_apply_apply] at he
  · intro ha
    apply LinearMap.ext
    intro w
    rw [action_apply, MonoidHom.mem_ker.mp ha]
    exact congrArg Multiplicative.toAdd (m.coordinates.apply_symm_apply _)

include m in
/-- The two-core acts trivially, as follows from the specified natural marking. -/
theorem core_action_eq_one (k : E.K) (hk : k ∈ pCore 2 E.K) :
    quotientAction E E.K E.K_le_G₁ k = 1 := by
  ext w
  apply m.coordinates.injective
  apply Multiplicative.toAdd.injective
  have hkq : QuotientGroup.mk' (pCore 2 E.K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
  rw [m.natural, hkq, map_one]
  simp

include m in
/-- Every actual quotient-centralizer element commutes with the K action. -/
theorem commute (A : Subgroup G) (hA : A ≤ E.G₁)
    (hC : A ≤ coreQuotientCentralizer E.K) (a : A) (k : E.K) :
    Commute (quotientAction E A hA a) (quotientAction E E.K E.K_le_G₁ k) := by
  let α := quotientAction E E.G₁ le_rfl
  let a' : E.G₁ := ⟨a,hA a.property⟩
  let k' : E.G₁ := ⟨k,E.K_le_G₁ k.property⟩
  have hc := coreQuotientCentralizer_commutator (hC a.property) k.property
  obtain ⟨c,hc,hce⟩ := hc
  have he : (⟨c,E.K_le_G₁ c.property⟩ : E.G₁) = ⁅a',k'⁆ := Subtype.ext hce
  have hz : α ⁅a',k'⁆ = 1 := by
    rw [← he]
    have h := m.core_action_eq_one c hc
    rwa [quotientAction_restrict] at h
  have hh : Commute (α a') (α k') := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rwa [← map_commutatorElement]
  rw [quotientAction_restrict E A hA, quotientAction_restrict E E.K E.K_le_G₁]
  exact hh

/-- Scalar commutants construct the multiplicity representation, retaining
its equation on all pure tensors in the original coordinates. -/
theorem exists_multiplicity (A : Subgroup G) (hA : A ≤ E.G₁)
    (hC : A ≤ coreQuotientCentralizer E.K) :
    ∃ μ : Representation E.input.field.Carrier A (Fin 2 → E.input.field.Carrier),
      (∀ a c v, m.action A hA a (fun i => c i • v) = fun i => μ a c i • v) ∧
      μ.ker = actionCentralizer E A hA := by
  let σ := Representation.restrictScalars (k := ZMod 2)
    (Representation.specialLinearNatural (k := E.input.field.Carrier) 2)
  have hs : ∀ (f : (Fin 2 → E.input.field.Carrier) →ₗ[ZMod 2]
      (Fin 2 → E.input.field.Carrier)), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : E.input.field.Carrier, ∀ v, f v = c • v := by
    intro f hf
    exact Representation.SL2NaturalOffenders.centralizer_scalar f.toAddMonoidHom hf
  have hc : ∀ a d x, m.action A hA a (fun i => σ d (x i)) =
      fun i => σ d (m.action A hA a x i) := by
    intro a d x
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 E.K) (m.actor.symm d)
    have hd : m.actor (QuotientGroup.mk' (pCore 2 E.K) k) = d := by rw [hk]; simp
    have hn (w) : m.action E.K E.K_le_G₁ k w = fun i => σ d (w i) := by
      rw [action_apply, m.natural, hd, m.coordinates.apply_symm_apply]
      rfl
    rw [← hn, ← hn]
    have hh := congrArg (fun f : MulAut (E.W ⧸ E.V₁.subgroupOf E.W) =>
      (m.coordinates (f (m.coordinates.symm (Multiplicative.ofAdd x)))).toAdd)
      (m.commute A hA hC a k).eq
    simp only [action_apply]
    change (m.coordinates (quotientAction E A hA a
      (m.coordinates.symm (m.coordinates (quotientAction E E.K E.K_le_G₁ k
        (m.coordinates.symm (Multiplicative.ofAdd x))))))).toAdd =
      (m.coordinates (quotientAction E E.K E.K_le_G₁ k
        (m.coordinates.symm (m.coordinates (quotientAction E A hA a
          (m.coordinates.symm (Multiplicative.ofAdd x))))))).toAdd
    simpa only [m.coordinates.symm_apply_apply, MulAut.mul_apply] using hh
  obtain ⟨μ,he⟩ := Representation.ScalarMultiplicity.exists_multiplicity σ hs
    (m.action A hA) hc
  refine ⟨μ,he,?_⟩
  rw [← m.action_kernel A hA]
  ext a
  constructor
  · intro ha
    apply LinearMap.ext
    intro x
    have hx : x = ∑ i : Fin 2, Pi.single i (x i) := by
      funext i
      fin_cases i <;> simp
    rw [Module.End.one_apply, hx, map_sum]
    change ∑ i : Fin 2, m.action A hA a (Pi.single i (x i)) = _
    apply Finset.sum_congr rfl
    intro i _
    have hi : (fun j => (Pi.single i (1 : E.input.field.Carrier) :
        Fin 2 → E.input.field.Carrier) j • x i) = Pi.single i (x i) := by
      ext j l
      by_cases hij : i = j
      · subst j; simp
      · simp [Ne.symm hij]
    rw [← hi, he, ha]
    rfl
  · intro ha
    apply LinearMap.ext
    intro c
    obtain ⟨v,hv⟩ := exists_ne (0 : Fin 2 → E.input.field.Carrier)
    have hh := he a c v
    rw [ha] at hh
    ext i
    exact (smul_left_injective E.input.field.Carrier hv)
      (congrFun hh i).symm

/-- The faithful GL₂ embedding retains its equation on the marked copies. -/
theorem exists_compatible_plane_embedding (A : Subgroup G) (hA : A ≤ E.G₁)
    (hC : A ≤ coreQuotientCentralizer E.K) :
    ∃ ι : (A ⧸ actionCentralizer E A hA) →* GL (Fin 2) E.input.field.Carrier,
      Function.Injective ι ∧ ∀ (a : A) (c v : Fin 2 → E.input.field.Carrier),
        m.action A hA a (fun i => c i • v) =
          fun i => Representation.generalLinearNatural 2
            (ι (QuotientGroup.mk' (actionCentralizer E A hA) a)) c i • v := by
  obtain ⟨μ,he,hμ⟩ := m.exists_multiplicity A hA hC
  let f : A →* GL (Fin 2) E.input.field.Carrier :=
    Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp μ.asGroupHom
  have hf : f.ker = actionCentralizer E A hA := by
    rw [← hμ]
    ext a
    change Matrix.GeneralLinearGroup.toLin.symm (μ.asGroupHom a) = 1 ↔ μ a = 1
    rw [map_eq_one_iff _ Matrix.GeneralLinearGroup.toLin.symm.injective]
    exact Units.ext_iff
  let e := QuotientGroup.quotientMulEquivOfEq hf.symm
  refine ⟨(QuotientGroup.kerLift f).comp e.toMonoidHom,
    (QuotientGroup.kerLift_injective f).comp e.injective,?_⟩
  intro a c v
  change m.action A hA a (fun i => c i • v) =
    fun i => Representation.generalLinearNatural 2 (f a) c i • v
  have hfa : Representation.generalLinearNatural 2 (f a) = μ a := by
    change ((Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.toLin.symm (μ.asGroupHom a))).val) = μ a
    rw [Matrix.GeneralLinearGroup.toLin.apply_symm_apply]
    rfl
  rw [hfa]
  exact he a c v

include m in
/-- The exact action quotient embeds in GL₂ over the original marking field. -/
theorem exists_plane_embedding (A : Subgroup G) (hA : A ≤ E.G₁)
    (hC : A ≤ coreQuotientCentralizer E.K) :
    ∃ ι : (A ⧸ actionCentralizer E A hA) →* GL (Fin 2) E.input.field.Carrier,
      Function.Injective ι := by
  obtain ⟨ι,hι,_⟩ := m.exists_compatible_plane_embedding A hA hC
  exact ⟨ι,hι⟩

end NaturalPair
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
