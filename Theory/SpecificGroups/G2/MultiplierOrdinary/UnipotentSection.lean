module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.RootLifts
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer

/-!
# From lifted positive-root multiplication to defining-prime exclusion

The existing six-coordinate bijection identifies the actual G₂ unipotent
subgroup, with its polynomial multiplication law. If the six additive root
sections satisfy that same law, their ordered product defines a homomorphic
section of this subgroup. Its index is prime to the field characteristic;
central Sylow transfer therefore excludes that prime from the kernel of any
finite perfect central cover.

The compatibility equation is an explicit, undischarged local input. The
individual root sections in `RootLifts` alone do not imply it.
Source: Aschbacher–Smith I.1.3–I.1.4, printed pp.407–408 (PDF pp.418–419),
and the finite central-extension calculation cited in GLS III §6.1.
-/

@[expose] public section

namespace Atlas.G2.MultiplierOrdinary

variable {F E : Type*} [Field F] [Group E] {f : E →* Model F}

namespace RootSections

/-- The existing A–F order of the six positive roots, now in the cover. -/
def product (L : RootSections f) (t : Fin 6 → F) : E :=
  L.root 0 (.ofAdd (t 0)) * L.root 1 (.ofAdd (t 1)) *
    L.root 2 (.ofAdd (t 2)) * L.root 3 (.ofAdd (t 3)) *
    L.root 4 (.ofAdd (t 4)) * L.root 5 (.ofAdd (t 5))

theorem project_product (L : RootSections f) (t : Fin 6 → F) :
    f (L.product t) = unipotentProduct t := by
  simp only [product, map_mul, ← MonoidHom.comp_apply, L.project]
  rfl

/-- The exact polynomial product law; proving it is the remaining
compatibility problem between different roots. -/
def ProductCompatible (L : RootSections f) : Prop :=
  ∀ t u, L.product t * L.product u = L.product (unipotentProductParameters t u)

/-- A compatible system constructs a section of the concrete unipotent
subgroup, commuting with its actual inclusion into the octonion group. -/
theorem exists_unipotent_section (L : RootSections f) (hL : L.ProductCompatible) :
    ∃ s : unipotent (K := F) →* E, f.comp s = (unipotent (K := F)).subtype := by
  let e := unipotentEquiv (K := F)
  let j : unipotent (K := F) → E := fun g => L.product (e.symm g)
  have hj (t : Fin 6 → F) : j (e t) = L.product t := by
    dsimp [j]
    rw [e.symm_apply_apply]
  have he0 : e 0 = 1 := Subtype.ext unipotentProduct_zero
  have hemul (t u : Fin 6 → F) :
      e t * e u = e (unipotentProductParameters t u) :=
    Subtype.ext (unipotentProduct_mul t u)
  have hj0 : j 1 = 1 := by
    rw [← he0, hj]
    simp [product]
  have hjmul (a b : unipotent (K := F)) : j (a * b) = j a * j b := by
    obtain ⟨t, rfl⟩ := e.surjective a
    obtain ⟨u, rfl⟩ := e.surjective b
    rw [hemul, hj, hj, hj, hL]
  refine ⟨{
    toFun := j
    map_one' := hj0
    map_mul' := hjmul }, ?_⟩
  apply MonoidHom.ext
  intro a
  obtain ⟨t, rfl⟩ := e.surjective a
  change f (j (e t)) = _
  rw [hj, L.project_product]
  rfl

end RootSections

/-- The index of the literal positive-root subgroup is prime to the
defining characteristic, in even and odd characteristic alike. -/
theorem not_dvd_unipotent_index [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] :
    ¬ p ∣ (unipotent (K := F)).index := by
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F p
  have hpq : p ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self p n.ne_zero
  have hnot (k : ℕ) (hk : k ≠ 0) : ¬ p ∣ Nat.card F ^ k - 1 := by
    intro h
    have hpow : p ∣ Nat.card F ^ k := hpq.trans (dvd_pow_self _ hk)
    have hpos : 1 ≤ Nat.card F ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ Nat.card_pos.ne')
    have hdiv := Nat.dvd_sub hpow h
    rw [Nat.sub_sub_self hpos] at hdiv
    exact (Fact.out : p.Prime).not_dvd_one hdiv
  rw [LieParabolicSetup.unipotent_index]
  exact (Fact.out : p.Prime).not_dvd_mul (hnot 6 (by decide)) (hnot 2 (by decide))

/-- Transfer turns the compatible lifted root multiplication into the
defining-prime exclusion for an arbitrary finite perfect central cover. -/
theorem not_dvd_kernel_of_positive_relations [Finite F] [Finite E]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (c : PerfectCentralCovering.Cover E (Model F))
    (L : RootSections c.toMonoidHom) (hL : L.ProductCompatible) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  obtain ⟨s, hs⟩ := L.exists_unipotent_section hL
  exact PerfectCentralCovering.not_dvd_card_kernel_of_section c
    (unipotent (K := F)) not_dvd_unipotent_index s hs

end Atlas.G2.MultiplierOrdinary

end
