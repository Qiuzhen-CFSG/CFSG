module
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.Collection

/-!
# Torus-equivariant sections of the actual positive G₂ roots

Starting with individual additive sections, commutate with a lift of a
nonidentity root scalar. Centrality of the kernel makes the construction
independent of lifts, and commutativity of each full root preimage makes it
additive. Commutativity of the split torus then proves equivariance under
all of its lifts. This works in both ordinary source ranges.

A second lemma proves uniqueness for additive lifts with a prescribed
nonidentity scalar action. It is intended to compare lifted conjugates
with polynomial words after those words have been proved additive.
Neither normalization nor uniqueness asserts the inter-root relations.

Source: Aschbacher–Smith I.1.3–I.1.4 (PDF pp.418–419), GLS III §6.1;
the torus characters are the actual attributed ATLAS octonion formulas.
-/

@[expose] public section
open scoped commutatorElement
namespace Atlas.G2.MultiplierOrdinary
variable {F E : Type*} [Field F] [Group E]

def positiveWeight (i : Fin 6) (l m : Fˣ) : Fˣ :=
  ![l*m, l^2/m, l, m, m^2/l, l/m] i

theorem torus_positiveRoot (i : Fin 6) (l m : Fˣ) (x : F) :
    torus l m * positiveRoot i x * (torus l m)⁻¹ =
      positiveRoot i ((positiveWeight i l m : F) * x) := by
  fin_cases i <;> simp [positiveRoot, positiveWeight, torus_rootA, torus_rootB,
    torus_rootC, torus_rootD, torus_rootE, torus_rootF]

private theorem torus_commute_scalar (i : Fin 6) (l m c : Fˣ) :
    Commute (torus l m) (scalarTorus i c) := by
  have h (a b : Fˣ) : Commute (torus l m) (torus a b) :=
    (Commute.all (l,m) (a,b)).map torusHom
  fin_cases i <;> simp only [scalarTorus] <;> exact h _ _

namespace RootSections
variable {f : E →* Model F}

def TorusEquivariant (L : RootSections f) : Prop :=
  ∀ (l m : Fˣ) (z : E), f z = torus l m → ∀ (i : Fin 6) (t : F),
    z * L.x i t * z⁻¹ = L.x i ((positiveWeight i l m : F) * t)

theorem project_x (L : RootSections f) (i : Fin 6) (t : F) :
    f (L.x i t) = positiveRoot i t :=
  DFunLike.congr_fun (L.project i) (.ofAdd t)

/-- An additive lift normalized by a nonidentity scalar is unique. This
compares genuine homomorphisms; it does not assume that a candidate polynomial
word is additive. -/
theorem hom_ext_of_scalar_equivariant
    (hk : f.ker ≤ Subgroup.center E) (u v : Multiplicative F →* E)
    (hproj : f.comp u = f.comp v) (z : E) (c : F) (hc : c ≠ 1)
    (hu : ∀ t : F, z * u (.ofAdd t) * z⁻¹ = u (.ofAdd (c*t)))
    (hv : ∀ t : F, z * v (.ofAdd t) * z⁻¹ = v (.ofAdd (c*t))) : u = v := by
  have hd : c-1 ≠ 0 := sub_ne_zero.mpr hc
  have he (w : Multiplicative F →* E)
      (hw : ∀ t : F, z * w (.ofAdd t) * z⁻¹ = w (.ofAdd (c*t))) (t : F) :
      ⁅z, w (.ofAdd ((c-1)⁻¹*t))⁆ = w (.ofAdd t) := by
    rw [commutatorElement_def, hw, ← map_inv, ← map_mul]
    change w (.ofAdd (c*((c-1)⁻¹*t) + -((c-1)⁻¹*t))) = w (.ofAdd t)
    apply congrArg (fun a : F => w (.ofAdd a))
    calc
      c*((c-1)⁻¹*t) + -((c-1)⁻¹*t) = (c-1)*((c-1)⁻¹*t) := by ring
      _ = t := mul_inv_cancel_left₀ hd t
  apply MonoidHom.ext
  intro t
  change u (.ofAdd t.toAdd) = v (.ofAdd t.toAdd)
  rw [← he u hu t.toAdd, ← he v hv t.toAdd]
  exact CentralExtension.commutator_eq_of_image_eq f hk rfl
    (DFunLike.congr_fun hproj _)

/-- Normalize an arbitrary family of additive root sections by a torus
commutator. Every lift of every element of the split torus then acts by
the literal root character. -/
theorem exists_torusEquivariant (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (c : Fˣ) (hc : c ≠ 1)
    (hcomm : ∀ (i : Fin 6) (v w : E), f v ∈ (positiveRootHom i).range →
      f w ∈ (positiveRootHom i).range → Commute v w) :
    ∃ M : RootSections f, M.TorusEquivariant := by
  classical
  choose a ha using fun i : Fin 6 => hf (scalarTorus i c)
  let d : F := (c : F) - 1
  have hd : d ≠ 0 := sub_ne_zero.mpr (fun h => hc (Units.ext h))
  let s : Fin 6 → F → E := fun i x => ⁅a i, L.x i (d⁻¹ * x)⁆
  have hs (i : Fin 6) (x : F) : f (s i x) = positiveRoot i x := by
    dsimp [s]
    rw [map_commutatorElement, commutatorElement_def, ha, L.project_x,
      scalarTorus_conjugate]
    have hi (v : F) : (positiveRoot i v)⁻¹ = positiveRoot i (-v) :=
      ((positiveRootHom (F := F) i).map_inv (Multiplicative.ofAdd v)).symm
    rw [hi, ← positiveRoot_add]
    congr 1
    calc
      (c : F) * (d⁻¹ * x) + -(d⁻¹ * x) = d * (d⁻¹ * x) := by dsimp [d]; ring
      _ = x := mul_inv_cancel_left₀ hd x
  have hadd (i : Fin 6) (x y : F) : s i (x+y) = s i x * s i y := by
    have hh : Commute (L.x i (d⁻¹*x)) (s i y) :=
      hcomm i _ _ (by rw [L.project_x]; exact ⟨.ofAdd _, rfl⟩)
        (by rw [hs]; exact ⟨.ofAdd _, rfl⟩)
    dsimp [s]
    rw [mul_add, L.x_add, commutatorElement_mul_right_eq_mul_conj]
    change s i x * L.x i (d⁻¹*x) * s i y * (L.x i (d⁻¹*x))⁻¹ = _
    rw [mul_assoc (s i x), hh.eq, ← mul_assoc, mul_assoc (s i x * s i y),
      mul_inv_cancel, mul_one]
  let M : RootSections f := {
    root := fun i => {
      toFun := fun x => s i x.toAdd
      map_one' := by simp [s]
      map_mul' := fun x y => hadd i x.toAdd y.toAdd }
    project := fun i => MonoidHom.ext (fun x => hs i x.toAdd) }
  refine ⟨M, ?_⟩
  intro l m z hz i x
  change z * ⁅a i, L.x i (d⁻¹*x)⁆ * z⁻¹ =
    ⁅a i, L.x i (d⁻¹*((positiveWeight i l m : F)*x))⁆
  rw [conjugate_commutatorElement]
  apply CentralExtension.commutator_eq_of_image_eq f hk
  · rw [map_mul, map_mul, map_inv, hz, ha, (torus_commute_scalar i l m c).eq]
    simp only [mul_inv_cancel_right]
  · rw [map_mul, map_mul, map_inv, hz, L.project_x, L.project_x,
      torus_positiveRoot]
    congr 1
    ring

end RootSections

private theorem exists_nonidentity_unit [Finite F] (hF : 2 < Nat.card F) :
    ∃ c : Fˣ, c ≠ 1 := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  exact exists_ne 1

theorem even_torusEquivariant_sections [Finite F] [CharP F 2] (hF : 4 < Nat.card F)
    (f : E →* Model F) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∃ L : RootSections f, L.TorusEquivariant := by
  obtain ⟨L⟩ := even_root_sections hF f hf hk
  obtain ⟨c, hc⟩ := exists_nonidentity_unit (F := F) (by omega)
  exact L.exists_torusEquivariant hf hk c hc
    (fun i _ _ hv hw => even_root_preimage_commute hF f hf hk i hv hw)

theorem prime_torusEquivariant_sections [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 2 < p)
    (f : E →* Model F) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∃ L : RootSections f, L.TorusEquivariant := by
  obtain ⟨L⟩ := prime_root_sections hF hp f hf hk
  obtain ⟨c, hc⟩ := exists_nonidentity_unit (F := F) (by omega)
  exact L.exists_torusEquivariant hf hk c hc
    (fun i _ _ hv hw => prime_root_preimage_commute hF f hk i hv hw)
end Atlas.G2.MultiplierOrdinary
end
