module

public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Stellmacher.Recognition.LargeTerminalFiveFixedInvolution
public import Stellmacher.Recognition.LargeTerminalFiveFixedConjugateGeometry
public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Stellmacher.Recognition.LargeTerminalFixedLayerKernel

/-!
# Transport from a conjugate derived quotient

Write Q for the second local core, R for the first residual, D for R',
and Z for Z(R). The source places a five-fixed involution in C(Z*) and
finds at least eight fixed points on D*/Z*. Kernel detection then puts
the involution in the corresponding conjugate of Q. Its nontrivial
commutator with an element of D* excludes the conjugate of C_Q(D).
Conjugating back gives the required ambient conjugacy.

The full-centralizer kernel test is proved from the original context in
`LargeTerminalFixedLayerKernel`, and `LargeTerminalFiveFixedConjugateGeometry`
constructs the conjugate layer and displacement for every five-fixed
involution outside R. Combining these proves the actual transport theorem.
The order-four and noncyclicity assumptions are needed to produce such an
involution, but transport itself only needs the five-action and its residual
fixed-center bound.

Source: Thompson VI, printed p.630, paragraph beginning “Now Y ∈ C(Z*)”.
The rendered source says |C_{D*/Z*}(Y)| ≥ 2^3; the PDF text extraction
misreads both the inequality and exponent.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven Subgroup
open scoped commutatorElement

universe u

/-- A large layer fixed modulo the residual center and a nonzero derived
displacement suffice for transport, once large fixed layers detect the core
in the full involution centralizer. Both local inputs are explicit here. -/
public theorem LargeTerminalContext.outer_transport_of_fixed_layer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G)
    (hdetect : ∀ (t : G), t ∈ centralizer ({z} : Set G) → orderOf t = 2 →
      ∀ E : Subgroup G, E ≤ DerivedAmbient ctx.firstResidual →
        16 ≤ Nat.card E → ⁅E, zpowers t⁆ ≤ CenterAmbient ctx.firstResidual →
          t ∈ twoCoreIn ctx.second)
    (y : G) (hy : orderOf y = 2)
    (hgeometry : ∃ (g : G) (E : Subgroup G) (v : G),
      y ∈ (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom ∧
      E ≤ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      16 ≤ Nat.card E ∧
      ⁅E, zpowers y⁆ ≤ (CenterAmbient ctx.firstResidual).map
        (MulAut.conj g).toMonoidHom ∧
      v ∈ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      ⁅v, y⁆ ≠ 1) :
    ∃ x : G, x ∈ twoCoreIn ctx.second ∧
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) ∧ IsConj y x := by
  obtain ⟨g, E, v, hyC, hED, hE, hcomm, hvD, hvy⟩ := hgeometry
  let e := MulAut.conj g
  let x := e.symm y
  let E₀ := E.map e.symm.toMonoidHom
  have hinv : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext a
    exact e.symm_apply_apply a
  have hxC : x ∈ centralizer ({z} : Set G) := by
    obtain ⟨t, ht, hty⟩ := hyC
    change e t = y at hty
    change e.symm y ∈ centralizer ({z} : Set G)
    rw [← hty, e.symm_apply_apply]
    exact ht
  have hxorder : orderOf x = 2 :=
    (orderOf_injective e.symm.toMonoidHom e.symm.injective y).trans hy
  have hE₀D : E₀ ≤ DerivedAmbient ctx.firstResidual := by
    change E ≤ (DerivedAmbient ctx.firstResidual).map e.toMonoidHom at hED
    have hh := map_mono (f := e.symm.toMonoidHom) hED
    simpa only [map_map, hinv, map_id] using hh
  have hE₀card : 16 ≤ Nat.card E₀ := by
    rw [show Nat.card E₀ = Nat.card E from card_map_of_injective e.symm.injective]
    exact hE
  have hcomm₀ : ⁅E₀, zpowers x⁆ ≤ CenterAmbient ctx.firstResidual := by
    change ⁅E, zpowers y⁆ ≤ (CenterAmbient ctx.firstResidual).map e.toMonoidHom at hcomm
    have hh := map_mono (f := e.symm.toMonoidHom) hcomm
    rw [map_commutator, MonoidHom.map_zpowers, map_map, hinv, map_id] at hh
    exact hh
  refine ⟨x, hdetect x hxC hxorder E₀ hE₀D hE₀card hcomm₀, ?_, ?_⟩
  · intro hxD
    have hyD : y ∈ centralizer
        ((DerivedAmbient ctx.firstResidual).map e.toMonoidHom : Set G) := by
      have hh := map_centralizer_le_centralizer_image
        (DerivedAmbient ctx.firstResidual : Set G) e.toMonoidHom
        (mem_map_of_mem e.toMonoidHom hxD)
      change e x ∈ centralizer
        ((DerivedAmbient ctx.firstResidual).map e.toMonoidHom : Set G) at hh
      simpa only [x, e.apply_symm_apply] using hh
    exact hvy (commutatorElement_eq_one_iff_commute.mpr
      (mem_centralizer_iff.mp hyD v hvD))
  · exact isConj_iff.mpr ⟨g⁻¹, by simp [x, e, mul_assoc]⟩

/-- At the upper endpoint only the conjugate fixed layer and displacement
are needed: core detection in the full centralizer follows from the context. -/
public theorem LargeTerminalContext.outer_transport_of_conjugate_fixed_layer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hy : orderOf y = 2)
    (hgeometry : ∃ (g : G) (E : Subgroup G) (v : G),
      y ∈ (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom ∧
      E ≤ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      16 ≤ Nat.card E ∧
      ⁅E, zpowers y⁆ ≤ (CenterAmbient ctx.firstResidual).map
        (MulAut.conj g).toMonoidHom ∧
      v ∈ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      ⁅v, y⁆ ≠ 1) :
    ∃ x : G, x ∈ twoCoreIn ctx.second ∧
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) ∧ IsConj y x := by
  apply ctx.outer_transport_of_fixed_layer z (fun t ht htorder E hED hE hcomm => ?_)
    y hy hgeometry
  exact ctx.involution_centralizer_fixed_layer_mem_core hS z hgen t ht
    (htorder ▸ pow_orderOf_eq_one t) E hED hE hcomm

/-- Every five-fixed involution outside the first residual transports into
the second core outside the derived centralizer. The specified omega-center
generator identifies the full involution centralizer used in the proof. -/
public theorem LargeTerminalContext.five_fixed_outer_transport_at_generator
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual)
    (hy : orderOf y = 2) :
    ∃ x : G, x ∈ twoCoreIn ctx.second ∧
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) ∧ IsConj y x := by
  exact ctx.outer_transport_of_conjugate_fixed_layer hS z hgen y hy
    (ctx.five_fixed_conjugate_geometry A hA hAN hfixed z hgen y hy hyQ hyA hyR)

/-- Actual five-fixed involution transport at Sylow order 4096, with no
choice of omega-center generator required. This supplies the transport input
to the subsequent fusion argument; no fusion hypothesis is used here. -/
public theorem LargeTerminalContext.five_fixed_outer_transport
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    ∀ y : G, y ∈ twoCoreIn ctx.second → y ∈ centralizer (A : Set G) →
      y ∉ ctx.firstResidual → orderOf y = 2 →
      ∃ x : G, x ∈ twoCoreIn ctx.second ∧
        x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) ∧ IsConj y x := by
  obtain ⟨z, _, hgen, _⟩ := ctx.involution_centralizer_core
  exact ctx.five_fixed_outer_transport_at_generator hS A hA hAN hfixed z hgen

end Stellmacher.Recognition
