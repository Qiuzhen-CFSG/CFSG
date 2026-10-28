module
public import Theory.Representation.PSL3Two.DualResidualPlane
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.Representation.BinaryConjugationSection.FixedMoving
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# Simultaneous natural and dual markings at a binary point

A change of basis sends a nonzero natural vector to the standard point.
Conjugating the actor and applying the inverse dual change to covectors
preserves evaluation. Restriction to the literal subgroup therefore gives
exactly the standard point parabolic and a dual section with its original
kernel. An incident nonzero seed stays in the annihilator plane.

Source application: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1042.
The paired section is input; this module does not recognize it abstractly.
-/

open Subgroup Representation Matrix
open scoped commutatorElement
open BinaryLinear.OuterCyclic
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
@[expose] public noncomputable section
namespace Matrix.PSL3Two.NaturalDualMarking
abbrev Space := Fin 3 → ZMod 2
abbrev NatRep : Representation (ZMod 2) (BinaryLinear.GL Space) Space :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom

def actorEquiv (t : BinaryLinear.GL Space) : BinaryLinear.GL Space ≃* SL :=
  (MulAut.conj t).trans (slEquivLinear 3).symm

def dualCoordinates (t : BinaryLinear.GL Space) : Module.Dual (ZMod 2) Space ≃ₗ[ZMod 2] Space :=
  t.symm.dualMap.trans (dotProductEquiv (ZMod 2) (Fin 3)).symm

private lemma fullDual_pairing (a : SL) (v w : Space) :
    dotProduct (fullDual a v) w = dotProduct v ((slEquivLinear 3 a).symm w) := by
  have ht : inverseTranspose a = SpecialLinearGroup.transpose a⁻¹ := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    change a⁻¹.val.transpose * a.val.transpose = 1
    rw [← Matrix.transpose_mul]
    change (a * a⁻¹).val.transpose = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  change dotProduct ((inverseTranspose a).val.mulVec v) w = _
  rw [ht]
  change dotProduct (a⁻¹.val.transpose.mulVec v) w = dotProduct v ((slEquivLinear 3 a)⁻¹ w)
  rw [← map_inv]
  change dotProduct (a⁻¹.val.transpose.mulVec v) w = dotProduct v (a⁻¹.val.mulVec w)
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

lemma dualCoordinates_pairing (t : BinaryLinear.GL Space) (φ : Module.Dual (ZMod 2) Space)
    (w : Space) : dotProduct (dualCoordinates t φ) w = φ (t.symm w) := by
  exact congrArg (fun f : Module.Dual (ZMod 2) Space => f w)
    ((dotProductEquiv (ZMod 2) (Fin 3)).apply_symm_apply (t.symm.dualMap φ))

private lemma dualCoordinates_equivariant (t g : BinaryLinear.GL Space)
    (φ : Module.Dual (ZMod 2) Space) :
    dualCoordinates t (NatRep.dual g φ) = fullDual (actorEquiv t g) (dualCoordinates t φ) := by
  apply (dotProductEquiv (ZMod 2) (Fin 3)).injective
  apply LinearMap.ext
  intro w
  change dotProduct (dualCoordinates t (NatRep.dual g φ)) w =
    dotProduct (fullDual (actorEquiv t g) (dualCoordinates t φ)) w
  rw [dualCoordinates_pairing, fullDual_pairing, dualCoordinates_pairing]
  change φ (g.symm (t.symm w)) = φ (t.symm ((slEquivLinear 3 (actorEquiv t g)).symm w))
  have he : slEquivLinear 3 (actorEquiv t g) = t * g * t⁻¹ :=
    (slEquivLinear 3).apply_symm_apply _
  rw [he]
  change φ (g.symm (t.symm w)) = φ (t.symm ((t * g * t⁻¹)⁻¹ w))
  simp only [_root_.mul_inv_rev, inv_inv, LinearEquiv.mul_apply]
  rw [LinearEquiv.symm_apply_apply]
  rfl

lemma dualCoordinates_incident (t : BinaryLinear.GL Space) (u : Space)
    (hu : t u = ![1,0,0]) (φ : Module.Dual (ZMod 2) Space) (hφ : φ u = 0) :
    dualCoordinates t φ 0 = 0 := by
  have he := dualCoordinates_pairing t φ (t u)
  rw [LinearEquiv.symm_apply_apply, hφ, hu] at he
  simpa [dotProduct, Fin.sum_univ_three] using he

private lemma pointParabolic_iff (g : SL) :
    g ∈ pointParabolicSL ↔ slEquivLinear 3 g (![1,0,0] : Space) = ![1,0,0] := by
  rw [mem_pointParabolicSL_iff]
  have hn : slEquivLinear 3 g (![1,0,0] : Space) ≠ 0 :=
    fun he => (by decide : (![1,0,0] : Space) ≠ 0)
      ((slEquivLinear 3 g).map_eq_zero_iff.mp he)
  constructor
  · rintro ⟨h1,h2⟩
    have h0 : g.val 0 0 = 1 := by
      have h0 : g.val 0 0 ≠ 0 := by
        intro he
        apply hn
        ext i
        fin_cases i <;> simp [slEquivLinear_apply, mulVec, dotProduct, Fin.sum_univ_three, he,h1,h2]
      exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ h0
    ext i
    fin_cases i <;> simp [slEquivLinear_apply, mulVec, dotProduct, Fin.sum_univ_three, h0,h1,h2]
  · intro he
    constructor
    · simpa [slEquivLinear_apply, mulVec, dotProduct, Fin.sum_univ_three] using congrFun he 1
    · simpa [slEquivLinear_apply, mulVec, dotProduct, Fin.sum_univ_three] using congrFun he 2
end Matrix.PSL3Two.NaturalDualMarking
namespace Matrix.PSL3Two.NaturalDualMarking
lemma actorEquiv_apply (t g : BinaryLinear.GL Space) (v : Space) :
    slEquivLinear 3 (actorEquiv t g) (t v) = t (g v) := by
  have he : slEquivLinear 3 (actorEquiv t g) = t * g * t⁻¹ :=
    (slEquivLinear 3).apply_symm_apply _
  rw [he]
  change t (g (t.symm (t v))) = _
  rw [LinearEquiv.symm_apply_apply]

private lemma normalized_range {J : Type*} [Group J]
    (f : J →* BinaryLinear.GL Space) (v : Space)
    (hf : f.range = MulAction.stabilizer (BinaryLinear.GL Space) v)
    (t : BinaryLinear.GL Space) (ht : t v = ![1,0,0]) :
    ((actorEquiv t).toMonoidHom.comp f).range = pointParabolicSL := by
  have he (g : BinaryLinear.GL Space) :
      actorEquiv t g ∈ pointParabolicSL ↔ g v = v := by
    rw [pointParabolic_iff, ← ht, actorEquiv_apply, t.injective.eq_iff]
  ext g
  constructor
  · rintro ⟨x,rfl⟩
    apply (he (f x)).mpr
    exact (show f x ∈ MulAction.stabilizer (BinaryLinear.GL Space) v by
      rw [← hf]; exact ⟨x,rfl⟩)
  · intro hg
    have hx : (actorEquiv t).symm g ∈ f.range := by
      rw [hf]
      apply (he _).mp
      rwa [(actorEquiv t).apply_symm_apply]
    obtain ⟨x,hx⟩ := hx
    exact ⟨x,by change actorEquiv t (f x) = g; rw [hx, (actorEquiv t).apply_symm_apply]⟩
end Matrix.PSL3Two.NaturalDualMarking
namespace Matrix.PSL3Two.NaturalDualMarking
variable {G : Type*} [Group G] {L P B Z : Subgroup G}

private def restrictedDualSection
    (q : L →* BinaryLinear.GL Space)
    (d : BinaryConjugationSection L B Z (Representation.dual (NatRep.comp q)))
    (hPL : P ≤ L) (hBP : B ≤ P) (t : BinaryLinear.GL Space) :
    BinaryConjugationSection P B Z
      (fullDual.comp ((actorEquiv t).toMonoidHom.comp (q.comp (inclusion hPL)))) where
  section_le := hBP
  kernel_le := d.kernel_le
  normalized := hPL.trans d.normalized
  coordinates := (dualCoordinates t).toAddEquiv.toMultiplicative.toMonoidHom.comp d.coordinates
  onto := (dualCoordinates t).toAddEquiv.toMultiplicative.surjective.comp d.onto
  kernel_eq := by
    ext b
    change dualCoordinates t (d.coordinates b).toAdd = 0 ↔ (b : G) ∈ Z
    rw [← d.coordinates_eq_one_iff b]
    exact (dualCoordinates t).map_eq_zero_iff
  equivariant p b := by
    change dualCoordinates t (d.coordinates _).toAdd =
      fullDual (actorEquiv t (q (inclusion hPL p))) (dualCoordinates t (d.coordinates b).toAdd)
    have he : Representation.dual (NatRep.comp q) (inclusion hPL p) (d.coordinates b).toAdd =
        NatRep.dual (q (inclusion hPL p)) (d.coordinates b).toAdd := by
      apply LinearMap.ext
      intro w
      change (d.coordinates b).toAdd ((q (inclusion hPL p)⁻¹) w) =
        (d.coordinates b).toAdd ((q (inclusion hPL p))⁻¹ w)
      rw [map_inv]
    exact (congrArg (dualCoordinates t) ((d.equivariant (inclusion hPL p) b).trans he)).trans
      (dualCoordinates_equivariant t _ _)

/-- Normalize the natural point and the dual coordinates with the same change
of basis, keeping the actual subgroup inclusion and its full image. -/
lemma normalized_action
    (q : L →* BinaryLinear.GL Space)
    (d : BinaryConjugationSection L B Z (Representation.dual (NatRep.comp q)))
    (hPL : P ≤ L) (hBP : B ≤ P)
    (v : Space) (hv : v ≠ 0)
    (hq : (q.comp (inclusion hPL)).range = MulAction.stabilizer (BinaryLinear.GL Space) v) :
    ∃ t : BinaryLinear.GL Space, t v = ![1,0,0] ∧
      ∃ f : P →* SL, f.range = pointParabolicSL ∧
        (∀ x : P, f x = actorEquiv t (q (inclusion hPL x))) ∧
        ∃ d' : BinaryConjugationSection P B Z (fullDual.comp f),
          ∀ b : B, (d'.coordinates b).toAdd = dualCoordinates t (d.coordinates b).toAdd := by
  obtain ⟨s,hs⟩ := SpecialLinearGroup.exists_mulVec_eq_three v (![1,0,0] : Space) hv (by decide)
  let t := slEquivLinear 3 s
  have ht : t v = ![1,0,0] := hs
  let f := (actorEquiv t).toMonoidHom.comp (q.comp (inclusion hPL))
  exact ⟨t,ht,f,normalized_range _ v hq t ht,fun _ => rfl,
    restrictedDualSection q d hPL hBP t,fun _ => rfl⟩

/-- Incidence and nonvanishing survive this simultaneous coordinate change. -/
lemma normalized_marking
    (q : L →* BinaryLinear.GL Space)
    (d : BinaryConjugationSection L B Z (Representation.dual (NatRep.comp q)))
    (hPL : P ≤ L) (hBP : B ≤ P)
    (v : Space) (hv : v ≠ 0)
    (hq : (q.comp (inclusion hPL)).range = MulAction.stabilizer (BinaryLinear.GL Space) v)
    (b : B) (hb : (d.coordinates b).toAdd v = 0) (hb0 : d.coordinates b ≠ 1) :
    ∃ t : BinaryLinear.GL Space, t v = ![1,0,0] ∧
      ∃ f : P →* SL, f.range = pointParabolicSL ∧
        (∀ x : P, f x = actorEquiv t (q (inclusion hPL x))) ∧
        ∃ d' : BinaryConjugationSection P B Z (fullDual.comp f),
          (∀ b : B, (d'.coordinates b).toAdd = dualCoordinates t (d.coordinates b).toAdd) ∧
          (d'.coordinates b).toAdd 0 = 0 ∧ d'.coordinates b ≠ 1 := by
  obtain ⟨t,ht,f,hf,hcompat,d',hd'⟩ := normalized_action q d hPL hBP v hv hq
  refine ⟨t,ht,f,hf,hcompat,d',hd',?_,?_⟩
  · rw [hd']
    exact dualCoordinates_incident t v ht _ hb
  · intro he
    apply hb0
    have hz : (dualCoordinates t) (d.coordinates b).toAdd = 0 :=
      (hd' b).symm.trans (congrArg Multiplicative.toAdd he)
    exact (dualCoordinates t).map_eq_zero_iff.mp hz
end Matrix.PSL3Two.NaturalDualMarking

namespace Matrix.PSL3Two.NaturalDualMarking
open MarkedAutomorphisms MarkedAutomorphisms.AffineConstituents
variable {J : Type*} [Group J] [Finite J]

lemma dual_sylow_fixed_mem_plane (f : J →* SL) (hf : f.range = pointParabolicSL)
    (S : Sylow 2 J) (v : Space) (hv : ∀ s : J, s ∈ (S : Subgroup J) → fullDual (f s) v = v) :
    v 0 = 0 := by
  let g : J →* pointParabolicSL := f.codRestrict pointParabolicSL (fun x => by
    rw [← hf]; exact ⟨x,rfl⟩)
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y,hy⟩ := (show (x : SL) ∈ f.range by rw [hf]; exact x.property)
    exact ⟨y,Subtype.ext hy⟩
  let S' := S.mapSurjective hg
  have hcore : pointV ≤ (S : Subgroup J).map f := by
    rw [← MarkedProduct.pointParabolic_core]
    have he := map_mono (f := pointParabolicSL.subtype)
      (pCore_isPGroup.le_sylow_of_normal S')
    change (pCore 2 pointParabolicSL).map pointParabolicSL.subtype ≤ _
    simpa only [S',Sylow.coe_mapSurjective,Subgroup.map_map,
      show pointParabolicSL.subtype.comp g = f from rfl] using he
  have ha : Bruhat.upper 1 ∈ pointV := by decide
  obtain ⟨s,hs,he⟩ := hcore ha
  have hfix := hv s hs
  rw [he] at hfix
  have hcalc : ∀ v : Space, fullDual (Bruhat.upper 1) v = v → v 0 = 0 := by decide +kernel
  exact hcalc v hfix

variable {G : Type*} [Group G] [Finite G] {P B Z : Subgroup G}
lemma section_sylow_fixed_mem_plane (f : P →* SL) (hf : f.range = pointParabolicSL)
    (d : BinaryConjugationSection P B Z (fullDual.comp f))
    (S : Sylow 2 P) (b : B)
    (hb : ∀ s : P, s ∈ (S : Subgroup P) → ⁅(b : G),(s : G)⁆ ∈ Z) :
    (d.coordinates b).toAdd 0 = 0 := by
  apply dual_sylow_fixed_mem_plane f hf S
  intro s hs
  exact (d.fixed_coordinate_iff_commutator_mem s b).mpr (hb s hs)
end Matrix.PSL3Two.NaturalDualMarking
