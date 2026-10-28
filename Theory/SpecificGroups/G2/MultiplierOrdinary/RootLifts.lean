module

public import Theory.AtlasPort.LinearGroups.G2.TorusNormalization
public import Theory.GroupTheory.Commutator.ScalarInvariantRoot
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Additive root sections in central extensions of G₂

The six positive roots below are the literal A–F octonion automorphisms.
Their torus characters are surjective onto the field units. Over an even
field of order greater than four, the scalar-invariant commutator pairing
vanishes. Over a prime field, each root is cyclic, so its full preimage in
a central extension is abelian. A torus commutator then supplies an additive
section of each root, with the prescribed projection.

These are local inputs to Aschbacher–Smith I.1.3–I.1.4, printed pp.407–408
(PDF pp.418–419), and GLS III §6.1. The calculation does not assert that
relations between different roots lift, or that the universal kernel is
trivial. In particular the prime-field result also holds at order three,
where those further relations have a genuine obstruction.

The octonion roots and torus formulas are the licensed ATLAS ports imported
above; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. The torus
commutator construction adapts the proof in
Theory.SpecificGroups.SymplecticFour.CentralRootLifts to these root maps.
-/

@[expose] public section

open scoped commutatorElement IsMulCommutative
namespace Atlas.G2.MultiplierOrdinary
variable {F : Type*} [Field F]

def positiveRoot (i : Fin 6) : F → Model F :=
  ![rootA, rootB, rootC, rootD, rootE, rootF] i

theorem positiveRoot_zero (i : Fin 6) : positiveRoot i (0 : F) = 1 := by
  fin_cases i <;> simp [positiveRoot]

theorem positiveRoot_add (i : Fin 6) (a b : F) :
    positiveRoot i (a + b) = positiveRoot i a * positiveRoot i b := by
  fin_cases i <;> simp [positiveRoot, rootA_add, rootB_add, rootC_add,
    rootD_add, rootE_add, rootF_add]

def positiveRootHom (i : Fin 6) : Multiplicative F →* Model F where
  toFun x := positiveRoot i x.toAdd
  map_one' := positiveRoot_zero i
  map_mul' x y := positiveRoot_add i x.toAdd y.toAdd

theorem positiveRoot_injective (i : Fin 6) :
    Function.Injective (positiveRoot (F := F) i) := by
  fin_cases i
  · exact rootA_injective
  · exact rootB_injective
  · exact rootC_injective
  · exact rootD_injective
  · exact rootE_injective
  · exact rootF_injective

def scalarTorus (i : Fin 6) (c : Fˣ) : Model F :=
  ![torus c 1, torus 1 c⁻¹, torus c 1, torus 1 c,
    torus c⁻¹ 1, torus c 1] i

theorem scalarTorus_conjugate (i : Fin 6) (c : Fˣ) (x : F) :
    scalarTorus i c * positiveRoot i x * (scalarTorus i c)⁻¹ =
      positiveRoot i ((c : F) * x) := by
  fin_cases i <;>
    simp [scalarTorus, positiveRoot, torus_rootA, torus_rootB, torus_rootC,
      torus_rootD, torus_rootE, torus_rootF]

theorem even_root_preimage_commute [Finite F] [CharP F 2] (hF : 4 < Nat.card F)
    {E : Type*} [Group E] (f : E →* Model F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (i : Fin 6) {v w : E}
    (hv : f v ∈ (positiveRootHom i).range) (hw : f w ∈ (positiveRootHom i).range) :
    Commute v w := by
  apply CentralExtension.commute_lifts_of_full_scalar_action hF f hf hk
    (positiveRootHom i) ?_ hv hw
  intro c hc
  exact ⟨scalarTorus i (Units.mk0 c hc), scalarTorus_conjugate i (Units.mk0 c hc)⟩

theorem prime_root_preimage_commute [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) {E : Type*} [Group E] (f : E →* Model F)
    (hk : f.ker ≤ Subgroup.center E) (i : Fin 6) {v w : E}
    (hv : f v ∈ (positiveRootHom i).range) (hw : f w ∈ (positiveRootHom i).range) :
    Commute v w := by
  let u := positiveRootHom (F := F) i
  let R := u.range.comap f
  let g : R →* u.range := (f.comp R.subtype).codRestrict u.range (fun x => x.property)
  let : IsCyclic (Multiplicative F) := isCyclic_of_prime_card hF
  let : IsCyclic u.range := isCyclic_of_surjective u.rangeRestrict u.rangeRestrict_surjective
  have hg : g.ker ≤ Subgroup.center R := by
    intro x hx
    have hx' : f (x : E) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hk hx') y
  let : IsMulCommutative R := g.isMulCommutative_of_isCyclic_of_ker_le_center hg
  exact congrArg Subtype.val (mul_comm (⟨v, hv⟩ : R) ⟨w, hw⟩)

private theorem exists_root_lift [Finite F] (hF : 2 < Nat.card F)
    {E : Type*} [Group E] (f : E →* Model F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (i : Fin 6)
    (hcomm : ∀ v w : E, f v ∈ (positiveRootHom i).range →
      f w ∈ (positiveRootHom i).range → Commute v w) :
    ∃ u : Multiplicative F →* E, f.comp u = positiveRootHom i := by
  classical
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨c, hc⟩ := exists_ne (1 : Fˣ)
  have hc1 : (c : F) ≠ 1 := fun h => hc (Units.ext h)
  obtain ⟨a, ha⟩ := hf (scalarTorus i c)
  choose b hb using fun x : F => hf (positiveRoot i x)
  let d : F := (c : F) - 1
  have hd : d ≠ 0 := sub_ne_zero.mpr hc1
  let s : F → E := fun x => ⁅a, b (d⁻¹ * x)⁆
  have hs (x : F) : f (s x) = positiveRoot i x := by
    dsimp [s]
    rw [map_commutatorElement, commutatorElement_def, ha, hb, scalarTorus_conjugate]
    have hinv (z : F) : (positiveRoot i z)⁻¹ = positiveRoot i (-z) :=
      ((positiveRootHom (F := F) i).map_inv (Multiplicative.ofAdd z)).symm
    rw [hinv, ← positiveRoot_add]
    congr 1
    calc
      (c : F) * (d⁻¹ * x) + -(d⁻¹ * x) = d * (d⁻¹ * x) := by dsimp [d]; ring
      _ = x := mul_inv_cancel_left₀ hd x
  have hs0 : s 0 = 1 := by
    dsimp [s]
    rw [mul_zero]
    have h0 : f (b 0) = f 1 := by rw [hb, positiveRoot_zero, map_one]
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl h0]
    simp
  have hsadd (x y : F) : s (x + y) = s x * s y := by
    have hsum : f (b (d⁻¹ * (x + y))) = f (b (d⁻¹ * x) * b (d⁻¹ * y)) := by
      rw [map_mul, hb, hb, hb, ← positiveRoot_add, mul_add]
    have hcomm' : Commute (b (d⁻¹ * x)) (s y) :=
      hcomm _ _ (by rw [hb]; exact ⟨.ofAdd _, rfl⟩)
        (by rw [hs]; exact ⟨.ofAdd _, rfl⟩)
    change ⁅a, b (d⁻¹ * (x + y))⁆ = _
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hsum,
      commutatorElement_mul_right_eq_mul_conj]
    change s x * b (d⁻¹ * x) * s y * (b (d⁻¹ * x))⁻¹ = _
    rw [mul_assoc (s x), hcomm'.eq, ← mul_assoc, mul_assoc (s x * s y),
      mul_inv_cancel, mul_one]
  refine ⟨{
    toFun := fun x => s x.toAdd
    map_one' := hs0
    map_mul' := fun x y => hsadd x.toAdd y.toAdd }, ?_⟩
  exact MonoidHom.ext (fun x => hs x.toAdd)

/-- Six additive sections with their literal octonion projections.
Relations between different roots are deliberately not fields of this structure. -/
structure RootSections {E : Type*} [Group E] (f : E →* Model F) where
  root : Fin 6 → Multiplicative F →* E
  project : ∀ i, f.comp (root i) = positiveRootHom i

theorem even_root_sections [Finite F] [CharP F 2] (hF : 4 < Nat.card F)
    {E : Type*} [Group E] (f : E →* Model F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : Nonempty (RootSections f) := by
  choose x hx using fun i => exists_root_lift (by omega) f hf hk i
    (fun _ _ hv hw => even_root_preimage_commute hF f hf hk i hv hw)
  exact ⟨⟨x, hx⟩⟩

theorem prime_root_sections [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 2 < p)
    {E : Type*} [Group E] (f : E →* Model F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : Nonempty (RootSections f) := by
  choose x hx using fun i => exists_root_lift (by omega) f hf hk i
    (fun _ _ hv hw => prime_root_preimage_commute hF f hk i hv hw)
  exact ⟨⟨x, hx⟩⟩

end Atlas.G2.MultiplierOrdinary

end
