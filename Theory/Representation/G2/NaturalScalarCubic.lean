module
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.Representation.G2.RestrictedModules.NaturalHighestWeight
public import Theory.GroupTheory.PCoreInRestriction

public section
noncomputable section
open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
open scoped commutatorElement MatrixGroups
namespace Atlas.G2.NaturalScalarCubic
variable {F : Type*} [Field F] [CharP F 2]

private theorem quotient_fixed_of_generators {G H : Type*} [Group G] [Group H]
    (K U R : Subgroup G) (w x : G) (hK : K = U ⊔ closure {w})
    (hx : x ∈ normalizer (K : Set G))
    (f : K →* H) (hker : f.ker.map K.subtype = R)
    (hU : ∀ u ∈ U, ⁅x,u⁆ ∈ R) (hw : ⁅x,w⁆ ∈ R) :
    ∀ b ∈ K, ⁅x,b⁆ ∈ R := by
  let a : K →* K :=
    { toFun b := ⟨x * b * x⁻¹, (mem_normalizer_iff.mp hx b).mp b.property⟩
      map_one' := Subtype.ext (by simp)
      map_mul' b c := Subtype.ext (by simp [mul_assoc]) }
  let C := (f.comp a).eqLocus f
  have hmem (b : K) : b ∈ C ↔ ⁅x,b.val⁆ ∈ R := by
    rw [← hker]
    change f (a b) = f b ↔ _
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
    change (a b * b⁻¹) ∈ f.ker ↔ K.subtype (a b * b⁻¹) ∈ f.ker.map K.subtype
    exact (mem_map_iff_mem K.subtype_injective).symm
  have hKC : K ≤ C.map K.subtype := by
    apply hK.le.trans
    apply sup_le
    · intro u hu
      have huK : u ∈ K := hK ▸ mem_sup_left hu
      exact mem_map_of_mem K.subtype ((hmem ⟨u, huK⟩).mpr (hU u hu))
    · apply (closure_le _).mpr
      intro z hz
      have he : z = w := hz
      rw [he]
      have hwK : w ∈ K := hK ▸ mem_sup_right (subset_closure (by simp))
      exact mem_map_of_mem K.subtype ((hmem ⟨w, hwK⟩).mpr hw)
  intro b hb
  obtain ⟨c, hc, he⟩ := hKC hb
  exact he ▸ (hmem c).mp hc

omit [CharP F 2] in
private theorem short_unipotent_commutator (s : Fˣ) (u : Model F) (hu : u ∈ unipotent) :
    ⁅torus s s,u⁆ ∈ radical₁ := by
  rw [unipotent_eq_range] at hu
  obtain ⟨t, rfl⟩ := hu
  refine ⟨unipotentProductParameters (torusUnipotentParameters s s t)
    (unipotentInverseParameters t), ?_, ?_⟩
  · simp [unipotentProductParameters, unipotentInverseParameters,
      torusUnipotentParameters, Units.ne_zero]
  · rw [commutatorElement_def, torus_unipotentProduct, unipotentProduct_inv,
      unipotentProduct_mul]

omit [CharP F 2] in
private theorem long_unipotent_commutator (s : Fˣ) (u : Model F) (hu : u ∈ unipotent) :
    ⁅torus (s ^ 2) s,u⁆ ∈ radical₂ := by
  rw [unipotent_eq_range] at hu
  obtain ⟨t, rfl⟩ := hu
  refine ⟨unipotentProductParameters (torusUnipotentParameters (s ^ 2) s t)
    (unipotentInverseParameters t), ?_, ?_⟩
  · simp [unipotentProductParameters, unipotentInverseParameters,
      torusUnipotentParameters, Units.ne_zero]
  · rw [commutatorElement_def, torus_unipotentProduct, unipotentProduct_inv,
      unipotentProduct_mul]

omit [CharP F 2] in
private theorem short_weyl_commute (s : Fˣ) : Commute (torus s s) (weylS : Model F) := by
  apply (mul_inv_eq_iff_eq_mul).mp
  simpa [torus_identity] using torus_weylS_conjugate s s

omit [CharP F 2] in
private theorem long_weyl_commute (s : Fˣ) : Commute (torus (s ^ 2) s) (weylR : Model F) := by
  change torus (s ^ 2) s * weylR = weylR * torus (s ^ 2) s
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  ext i
  fin_cases i <;>
    simp [torus, torusEquiv, torusLinear, torusWeights, weylR,
      weylREquiv, weylRLinear, weylRApply, pow_two, mul_assoc]

/-- The equal-coordinate torus fixes the entire short local quotient. -/
theorem short_commutators (s : Fˣ) :
    ∀ b ∈ local₁ (F := F), ⁅torus s s,b⁆ ∈ radical₁ := by
  apply quotient_fixed_of_generators local₁ unipotent radical₁ weylS (torus s s) rfl
    (torus_normalizes_local₁ ⟨(s,s),rfl⟩) shortSLHom
  · rw [shortSLHom_ker, map_subgroupOf_eq_of_le radical₁_le_local₁]
  · exact short_unipotent_commutator s
  · rw [(short_weyl_commute s).commutator_eq]
    exact radical₁.one_mem

/-- The torus with l=m² fixes the entire long local quotient. -/
theorem long_commutators (s : Fˣ) :
    ∀ b ∈ local₂ (F := F), ⁅torus (s ^ 2) s,b⁆ ∈ radical₂ := by
  apply quotient_fixed_of_generators local₂ unipotent radical₂ weylR (torus (s ^ 2) s) rfl
    (borel_le_normalizer_local₂ (mem_sup_right ⟨(s^2,s),rfl⟩)) longSLHom
  · rw [longSLHom_ker, map_subgroupOf_eq_of_le radical₂_le_local₂]
  · exact long_unipotent_commutator s
  · rw [(long_weyl_commute s).commutator_eq]
    exact radical₂.one_mem

open Atlas.G2.Restricted.NaturalCoordinates

private theorem common_fixed (v : Space F)
    (hA : action F (rootA 1) v = v) (hB : action F (rootB 1) v = v)
    (hD : action F (rootD 1) v = v) : v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := by
  exact ⟨by simpa using congrFun hD 0, by simpa using congrFun hB 0,
    by simpa using congrFun hA 0, by simpa using congrFun hA 1⟩

private theorem short_fixed (v : Space F)
    (h : ∀ q ∈ radical₁ (F := F), action F q v = v) :
    v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := by
  apply common_fixed v
  · exact h _ ⟨![1,0,0,0,0,0], by simp, by simp [unipotentProduct]⟩
  · exact h _ ⟨![0,1,0,0,0,0], by simp, by simp [unipotentProduct]⟩
  · exact h _ ⟨![0,0,0,1,0,0], by simp, by simp [unipotentProduct]⟩

private theorem long_fixed (v : Space F)
    (h : ∀ q ∈ radical₂ (F := F), action F q v = v) :
    v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := by
  constructor
  · have hf := h (rootF 1) ⟨![0,0,0,0,0,1], by simp, by simp [unipotentProduct]⟩
    simpa using congrFun hf 0
  · apply common_fixed v
    · exact h _ ⟨![1,0,0,0,0,0], by simp, by simp [unipotentProduct]⟩
    · exact h _ ⟨![0,1,0,0,0,0], by simp, by simp [unipotentProduct]⟩
    · exact h _ ⟨![0,0,0,1,0,0], by simp, by simp [unipotentProduct]⟩

private theorem coordinates_intertwine (g : Model F) (v : Natural.Space F) :
    equiv F (Natural.action F g v) = action F g (equiv F v) := by
  change equiv F (Natural.action F g v) =
    equiv F (Natural.action F g ((equiv F).symm (equiv F v)))
  rw [LinearEquiv.symm_apply_apply]

/-- On the short-radical fixed space the equal-parameter torus acts by its parameter. -/
theorem short_scalar_action (s : Fˣ) (v : Natural.Space F)
    (hfix : ∀ q ∈ radical₁ (F := F), Natural.action F q v = v) :
    Natural.action F (torus s s) v = (s : F) • v := by
  have hh := short_fixed (equiv F v) (fun q hq => by
    rw [← coordinates_intertwine, hfix q hq])
  simp only [equiv_apply] at hh
  apply (equiv F).injective
  rw [coordinates_intertwine, map_smul, action_torus]
  ext i
  fin_cases i <;> simp [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2]

/-- On the long-radical fixed line the torus l=m² acts by m². -/
theorem long_scalar_action (s : Fˣ) (v : Natural.Space F)
    (hfix : ∀ q ∈ radical₂ (F := F), Natural.action F q v = v) :
    Natural.action F (torus (s^2) s) v = ((s^2 : Fˣ) : F) • v := by
  have hh := long_fixed (equiv F v) (fun q hq => by
    rw [← coordinates_intertwine, hfix q hq])
  simp only [equiv_apply] at hh
  apply (equiv F).injective
  rw [coordinates_intertwine, map_smul, action_torus]
  ext i
  fin_cases i <;> simp [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2]

omit [CharP F 2] in
private def scalarTorus (n : ℕ) : Fˣ →* Model F :=
  torusHom.comp ((powMonoidHom n).prod (MonoidHom.id _))

omit [CharP F 2] in
private theorem scalarTorus_apply (n : ℕ) (s : Fˣ) : scalarTorus (F := F) n s = torus (s ^ n) s := rfl

omit [CharP F 2] in
private theorem scalarTorus_injective (n : ℕ) : Function.Injective (scalarTorus (F := F) n) := by
  intro s t h
  exact congrArg Prod.snd (torusHom_injective h)

private theorem scalar_moves {s : Fˣ} (hs : s ≠ 1) {v : Natural.Space F} (hv : v ≠ 0)
    {x : Model F} (ha : Natural.action F x v = (s : F) • v) :
    Natural.action F x v ≠ v := by
  intro he
  have hz : ((s : F) - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← ha, he, sub_self]
  exact hs (Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv)))

variable [Finite F]

omit [CharP F 2] in
private theorem scalar_exists (hF : Nat.card F = 4) : ∃ s : Fˣ, orderOf s = 3 := by
  apply exists_prime_orderOf_dvd_card' 3
  rw [Nat.card_units, hF]

/-- A cubic centralizes the short local section and moves any specified nonzero
natural vector fixed by its actual two-core. -/
theorem short_cubic_moves_fixed (hF : Nat.card F = 4)
    (v : Natural.Space F) (hv : v ≠ 0)
    (hfix : ∀ q ∈ (local₁ (F := F)).pCoreIn 2, Natural.action F q v = v) :
    ∃ x : Model F, orderOf x = 3 ∧ x ∈ normalizer (local₁ (F := F) : Set (Model F)) ∧
      (∀ (b : Model F) (_ : b ∈ local₁), ⁅x,b⁆ ∈ local₁.pCoreIn 2) ∧ Natural.action F x v ≠ v := by
  have hcore : (local₁ (F := F)).pCoreIn 2 = radical₁ := local₁_pCore
  obtain ⟨s, hs⟩ := scalar_exists hF
  refine ⟨torus s s, ?_, torus_normalizes_local₁ ⟨(s,s),rfl⟩, ?_, ?_⟩
  · have ho := (orderOf_injective (scalarTorus 1) (scalarTorus_injective 1) s).trans hs
    simpa only [scalarTorus_apply, pow_one] using ho
  · rw [hcore]
    exact short_commutators s
  · exact scalar_moves (x := torus s s) (fun he => by simp [he] at hs) hv
      (short_scalar_action s v (by rwa [hcore] at hfix))

/-- A cubic centralizes the long local section and moves any specified nonzero
natural vector fixed by its actual two-core. -/
theorem long_cubic_moves_fixed (hF : Nat.card F = 4)
    (v : Natural.Space F) (hv : v ≠ 0)
    (hfix : ∀ q ∈ (local₂ (F := F)).pCoreIn 2, Natural.action F q v = v) :
    ∃ x : Model F, orderOf x = 3 ∧ x ∈ normalizer (local₂ (F := F) : Set (Model F)) ∧
      (∀ (b : Model F) (_ : b ∈ local₂), ⁅x,b⁆ ∈ local₂.pCoreIn 2) ∧ Natural.action F x v ≠ v := by
  obtain ⟨s, hs⟩ := scalar_exists hF
  refine ⟨torus (s^2) s, ?_,
    borel_le_normalizer_local₂ (mem_sup_right ⟨(s^2,s),rfl⟩), ?_, ?_⟩
  · exact (orderOf_injective (scalarTorus 2) (scalarTorus_injective 2) s).trans hs
  · rw [local₂_pCoreIn]
    exact long_commutators s
  · exact scalar_moves (x := torus (s^2) s) (pow_ne_one_of_lt_orderOf (by decide) (by rw [hs]; decide)) hv
      (long_scalar_action s v (by rwa [local₂_pCoreIn] at hfix))

end Atlas.G2.NaturalScalarCubic
