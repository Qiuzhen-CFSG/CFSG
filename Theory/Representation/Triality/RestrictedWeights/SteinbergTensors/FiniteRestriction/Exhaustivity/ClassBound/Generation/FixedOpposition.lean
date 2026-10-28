module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedSubgroups
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.Restriction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusData
public import Theory.AlgebraicGroup.Automorphisms.Lang.CommutativeSurjectivity

/-!
# Lang correction of an ambient D4 opposition representative

A graph-field map preserving the supplied maximal torus restricts to a regular
endomorphism of that torus. Its injectivity on points and connectedness of the
torus make the restriction surjective. Its fixed points are finite for every
positive exponent, so the proved commutative Lang theorem applies.

Suppose an ambient element inverts the whole torus and the torus centralizer
is contained in the torus. The element's square and its graph-field
displacement then lie in the torus. Solving the displacement equation there
corrects the element to a fixed opposition lift, with square in the literal
fixed torus. This supplies precisely the input of
`fixedTorus_le_elementary_of_opposition`, also at exponent one.

The ambient inversion representative, torus-centralizer containment, and
invariance of the chosen torus remain explicit geometric premises. No
unconditional existence theorem is asserted here. The existing actual-torus
geometry contract supplies invariance through `torus_stable_of_torusData`.

Sources: GLS3, `refs/KGroup/GLS3/Chapter1.tex`, 1.8.9 and 1.9.5(e,f);
Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 10.4, 11.1(a), and 12.2--12.4.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The regular restriction to the actual torus, assuming its invariance. -/
def torusRestriction (S : Geometry K) (n : ℕ)
    (hstable : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus) :
    Morphism S.torus.carrierVariety S.torus.carrierVariety :=
  Morphism.codRestrictClosedSubgroup
    ((graphFieldMorphism S n).comp S.torus.inclusion) S.torus (by
      intro t
      change (graphFieldMorphism S n).onPoints (S.torus.inclusion.onPoints t) ∈ _
      rw [graphFieldMorphism_onPoints]
      exact hstable _ (S.torus.pointEquiv t).property)

omit [IsAlgClosed k] in
/-- Inclusion intertwines the torus restriction with the literal graph-field map. -/
theorem torusRestriction_inclusion (S : Geometry K) (n : ℕ)
    (hstable : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus)
    (t : Variety.Point S.torus.carrierVariety) :
    S.torus.inclusion.onPoints ((torusRestriction S n hstable).onPoints t) =
      graphFieldEnd S n (S.torus.inclusion.onPoints t) := by
  rw [torusRestriction, Morphism.codRestrictClosedSubgroup_inclusion_apply]
  change (graphFieldMorphism S n).onPoints (S.torus.inclusion.onPoints t) = _
  rw [graphFieldMorphism_onPoints]
  rfl

omit [IsAlgClosed k] in
/-- Ambient point injectivity restricts to the invariant torus. -/
theorem torusRestriction_injective (S : Geometry K) (n : ℕ)
    (hstable : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus) :
    Function.Injective (torusRestriction S n hstable).onPoints := by
  intro t u h
  apply S.torus.inclusion_injective
  apply (graphFieldEnd_bijective S n).injective
  rw [← torusRestriction_inclusion S n hstable, ← torusRestriction_inclusion S n hstable]
  exact congrArg S.torus.inclusion.onPoints h

/-- The regular injective endomorphism of the connected torus is surjective.
Only forward invariance of the torus is required. -/
theorem torusRestriction_surjective (S : Geometry K) (n : ℕ)
    (hstable : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus) :
    Function.Surjective (torusRestriction S n hstable).onPoints := by
  apply connected_endomorphism_surjective_of_finiteKernel
    (torusRestriction S n hstable) S.maximalTorus.1.isConnected
  change Finite (torusRestriction S n hstable).onPoints.ker
  rw [MonoidHom.ker_eq_bot _ (torusRestriction_injective S n hstable)]
  infer_instance

omit [IsAlgClosed k] in
/-- Torus fixed points inject into the supplied finite graph-field fixed group. -/
theorem torusRestriction_fixed_finite (S : Geometry K) (n : ℕ) (hn : 0 < n)
    (hstable : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus) :
    Finite {t : Variety.Point S.torus.carrierVariety |
      (torusRestriction S n hstable).onPoints t = t} := by
  let := S.fixed_finite n hn
  let f : {t : Variety.Point S.torus.carrierVariety |
      (torusRestriction S n hstable).onPoints t = t} →
      graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n :=
    fun t => ⟨S.torus.inclusion.onPoints t, by
      change graphFieldEnd S n (S.torus.inclusion.onPoints t) = _
      rw [← torusRestriction_inclusion S n hstable, t.property]
      rfl⟩
  exact Finite.of_injective f (by
    intro t u h
    apply Subtype.ext
    apply S.torus.inclusion_injective
    exact congrArg (fun g : graphFieldFixedSubgroup S.diagram.toMulEquiv
      S.frobenius.onPoints n => (g : Variety.Point K)) h)

/-- Lang solutions in the actual invariant torus, for every positive exponent. -/
theorem torus_lang_solution (S : Geometry K) (n : ℕ) (hn : 0 < n)
    (hstable : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus)
    (a : Variety.Point K) (ha : a ∈ S.torus) :
    ∃ c ∈ S.torus, c * (graphFieldEnd S n c)⁻¹ = a := by
  have hLang := langMorphism_surjective_of_connected_commutative
    (torusRestriction S n hstable) S.maximalTorus.1.isConnected
    S.maximalTorus.1.isMulCommutative
    (torusRestriction_fixed_finite S n hn hstable)
  let aT : Variety.Point S.torus.carrierVariety := S.torus.pointEquiv.symm ⟨a, ha⟩
  obtain ⟨c, hc⟩ := hLang aT
  refine ⟨S.torus.inclusion.onPoints c, (S.torus.pointEquiv c).property, ?_⟩
  have h := congrArg S.torus.inclusion.onPoints hc
  simp only [langMorphism_apply, map_mul, map_inv] at h
  change S.torus.inclusion.onPoints c *
    (S.torus.inclusion.onPoints ((torusRestriction S n hstable).onPoints c))⁻¹ = a at h
  rwa [torusRestriction_inclusion] at h

private theorem inverse_inverts {G : Type*} [Group G] (T : Subgroup G) (r : G)
    (hinv : ∀ t ∈ T, r * t * r⁻¹ = t⁻¹) (t : G) (ht : t ∈ T) :
    r⁻¹ * t * r = t⁻¹ := by
  calc
    _ = r⁻¹ * (r * t⁻¹ * r⁻¹) * r := by rw [hinv _ (T.inv_mem ht), inv_inv]
    _ = _ := by group

private theorem inverter_square_mem {G : Type*} [Group G] (T : Subgroup G)
    (hcentralizer : Subgroup.centralizer (T : Set G) ≤ T) (r : G)
    (hinv : ∀ t ∈ T, r * t * r⁻¹ = t⁻¹) : r ^ 2 ∈ T := by
  apply hcentralizer
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  symm
  calc
    r ^ 2 * t = r * (r * t * r⁻¹) * r := by rw [pow_two]; group
    _ = r * t⁻¹ * r := by rw [hinv t ht]
    _ = (r * t⁻¹ * r⁻¹) * r ^ 2 := by group
    _ = t * r ^ 2 := by rw [hinv _ (T.inv_mem ht), inv_inv]

private theorem inverter_displacement_mem {G : Type*} [Group G]
    (T : Subgroup G) (σ : G →* G)
    (honto : ∀ t ∈ T, ∃ u ∈ T, σ u = t)
    (hcentralizer : Subgroup.centralizer (T : Set G) ≤ T) (r : G)
    (hinv : ∀ t ∈ T, r * t * r⁻¹ = t⁻¹) : r⁻¹ * σ r ∈ T := by
  have hσinv : ∀ t ∈ T, σ r * t * (σ r)⁻¹ = t⁻¹ := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := honto t ht
    simpa only [map_mul, map_inv] using congrArg σ (hinv u hu)
  apply hcentralizer
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h : (r⁻¹ * σ r) * t * (r⁻¹ * σ r)⁻¹ = t := by
    calc
      _ = r⁻¹ * (σ r * t * (σ r)⁻¹) * r := by group
      _ = r⁻¹ * t⁻¹ * r := by rw [hσinv t ht]
      _ = t := by rw [inverse_inverts T r hinv _ (T.inv_mem ht), inv_inv]
  calc
    t * (r⁻¹ * σ r) = ((r⁻¹ * σ r) * t * (r⁻¹ * σ r)⁻¹) * (r⁻¹ * σ r) := by rw [h]
    _ = (r⁻¹ * σ r) * t := by group

omit [IsAlgClosed k] in
private theorem torus_commute (S : Geometry K) {t u : Variety.Point K}
    (ht : t ∈ S.torus) (hu : u ∈ S.torus) : Commute t u := by
  obtain ⟨a, rfl⟩ := (Set.ext_iff.mp S.torus.range_inclusion t).mpr ht
  obtain ⟨b, rfl⟩ := (Set.ext_iff.mp S.torus.range_inclusion u).mpr hu
  have h : Commute a b := isMulCommutative_iff.mp S.maximalTorus.1.isMulCommutative a b
  exact h.map S.torus.inclusion.onPoints

/-- Correct an ambient torus inverter by Lang to obtain a fixed opposition lift.
The three geometric premises must be discharged from `Geometry` before this
proves unconditional existence. No elementary membership is assumed. -/
theorem exists_fixed_opposition_of_inverter (S : Geometry K) (n : ℕ) (hn : 0 < n)
    (hstable : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus)
    (hcentralizer : Subgroup.centralizer (S.torus.toSubgroup : Set (Variety.Point K)) ≤
      S.torus.toSubgroup)
    (r : Variety.Point K) (hinv : ∀ t ∈ S.torus, r * t * r⁻¹ = t⁻¹) :
    ∃ w : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n,
      w ^ 2 ∈ fixedTorus S n ∧ ∀ t ∈ fixedTorus S n, w * t * w⁻¹ = t⁻¹ := by
  have honto : ∀ t ∈ S.torus, ∃ u ∈ S.torus, graphFieldEnd S n u = t := by
    intro t ht
    obtain ⟨x, hx⟩ := torusRestriction_surjective S n hstable (S.torus.pointEquiv.symm ⟨t, ht⟩)
    refine ⟨S.torus.inclusion.onPoints x, (S.torus.pointEquiv x).property, ?_⟩
    rw [← torusRestriction_inclusion S n hstable, hx]
    exact congrArg Subtype.val (S.torus.pointEquiv.apply_symm_apply ⟨t, ht⟩)
  have ha := inverter_displacement_mem S.torus.toSubgroup (graphFieldEnd S n)
    honto hcentralizer r hinv
  obtain ⟨c, hc, hcσ⟩ := torus_lang_solution S n hn hstable _ ha
  have hfixed : graphFieldEnd S n (r * c) = r * c := by
    calc
      _ = graphFieldEnd S n r * graphFieldEnd S n c := map_mul _ _ _
      _ = r * (r⁻¹ * graphFieldEnd S n r) * graphFieldEnd S n c := by group
      _ = r * (c * (graphFieldEnd S n c)⁻¹) * graphFieldEnd S n c := by rw [hcσ]; rfl
      _ = _ := by group
  let w : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n := ⟨r * c, hfixed⟩
  refine ⟨w, ?_, ?_⟩
  · change (r * c) ^ 2 ∈ S.torus
    have hsq : (r * c) ^ 2 = r ^ 2 := by
      calc
        _ = r ^ 2 * (r⁻¹ * c * r) * c := by simp only [pow_two]; group
        _ = r ^ 2 * c⁻¹ * c := by rw [inverse_inverts S.torus.toSubgroup r hinv c hc]
        _ = _ := by group
    rw [hsq]
    exact inverter_square_mem S.torus.toSubgroup hcentralizer r hinv
  · intro t ht
    apply Subtype.ext
    change (r * c) * (t : Variety.Point K) * (r * c)⁻¹ = (t : Variety.Point K)⁻¹
    calc
      _ = r * (c * (t : Variety.Point K)) * c⁻¹ * r⁻¹ := by group
      _ = r * ((t : Variety.Point K) * c) * c⁻¹ * r⁻¹ :=
        congrArg (fun z : Variety.Point K => r * z * c⁻¹ * r⁻¹)
          (torus_commute S hc ht).eq
      _ = r * (t : Variety.Point K) * r⁻¹ := by group
      _ = _ := hinv t ht

omit [IsAlgClosed k] in
/-- The existing actual-torus contract supplies the forward invariance used
by the Lang correction, without needing its character or class-count clauses. -/
theorem torus_stable_of_torusData (S : Geometry K) (n : ℕ)
    (D : AmbientCount.TorusData S n) :
    ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus := by
  intro t ht
  obtain ⟨x, rfl⟩ := (Set.ext_iff.mp S.torus.range_inclusion t).mpr ht
  change graphFieldEnd S n (S.torus.includePoint x) ∈ S.torus
  rw [← D.map_ambient x]
  exact (S.torus.pointEquiv (D.map x)).property

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition
