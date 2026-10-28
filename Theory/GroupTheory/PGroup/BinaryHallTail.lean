module
public import Theory.GroupTheory.PGroup.CyclicSelfCentralizerClassification
public import Theory.GroupTheory.PGroup.BinaryHallModularReduction

/-!
# Classifying the residual factor in Hall's theorem

The cyclic characteristic subgroup of a Hall core is normal and
self-centralizing inside the residual factor. The cyclic-self-centralizer
dichotomy either recognizes that factor or gives an abelian second omega
with noncyclic first omega in the centralizer of the cyclic subgroup's squares.
In the latter case, the center-of-omega argument in the ambient commuting
product contradicts Hall's characteristic-abelian hypothesis.

All characteristicity arguments take place in the original ambient group;
the residual factor need only be normal. Subtype transport identifies the
local centralizer with its actual embedded intersection in the ambient group.

Source: Gorenstein, *Finite Groups*, Section 5.4, Lemma 4.8 and Theorem 4.9.
-/

open Subgroup

private theorem centralizer_map_subtype
    {P : Type*} [Group P] (D : Subgroup P) (A : Subgroup D) :
    (centralizer (A : Set D)).map D.subtype = D ⊓ centralizer (A.map D.subtype : Set P) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (hy w hw)
  · rintro ⟨hxD, hxC⟩
    refine ⟨⟨x, hxD⟩, ?_, rfl⟩
    intro y hy
    exact Subtype.ext (hxC y (mem_map_of_mem D.subtype hy))

/-- Lemma 4.8 and the modular omega calculation in a Hall core: either the
residual factor is a Hall factor, or the original ambient group has a
noncyclic characteristic abelian subgroup. No characteristicity of the
residual factor is needed. -/
public theorem BinaryHallCore.isBinaryHallFactor_or_exists_noncyclic_characteristic_abelian
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {E D Z : Subgroup P} (h : BinaryHallCore E D Z) :
    IsBinaryHallFactor D ∨
      ∃ A : Subgroup P, A.Characteristic ∧ IsMulCommutative A ∧ ¬ IsCyclic A := by
  let : IsCyclic Z := h.cyclic
  let : Z.Characteristic := h.characteristic
  obtain ⟨a, ha⟩ := Z.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have haD : a ∈ D := h.le_tail (ha ▸ mem_zpowers a)
  let aD : D := ⟨a, haD⟩
  have hZ : zpowers aD = Z.subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [MonoidHom.map_zpowers, map_subgroupOf_eq_of_le h.le_tail]
    exact ha
  let : (zpowers aD).Normal := hZ ▸ inferInstance
  have hC : centralizer (zpowers aD : Set D) ≤ zpowers aD := by
    intro x hx
    rw [hZ]
    change (x : P) ∈ Z
    rw [← h.selfCentralizing]
    have hxmap := mem_map_of_mem D.subtype hx
    rw [centralizer_map_subtype, MonoidHom.map_zpowers, show D.subtype aD = a from rfl, ha] at hxmap
    exact hxmap
  rcases (hP.to_subgroup D).isBinaryHallFactor_or_omega_centralizer_sq aD hC with hD | ⟨hcomm, hncyc⟩
  · exact Or.inl hD
  right
  let M := D ⊓ centralizer (zpowers (a ^ 2) : Set P)
  let C := centralizer (zpowers (aD ^ 2) : Set D)
  have hmap : C.map D.subtype = M := by
    rw [centralizer_map_subtype, MonoidHom.map_zpowers]
    rfl
  let e : C ≃* M := (C.equivMapOfInjective D.subtype D.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  let : IsMulCommutative (omega M (p := 2) 2) := by
    apply IsMulCommutative.of_comm
    intro x y
    apply (e.omega 2 2).symm.injective
    simp only [map_mul]
    exact hcomm.is_comm.comm ((e.omega 2 2).symm x) ((e.omega 2 2).symm y)
  have hnM : ¬ IsCyclic (omega₁ M (p := 2)) := fun hh =>
    hncyc ((e.omega 2 1).isCyclic.mpr hh)
  exact h.exists_noncyclic_characteristic_abelian_of_modular_omega a ha.symm hnM

/-- The residual subgroup of a binary Hall core is cyclic, generalized
quaternion, dihedral, or semidihedral under Hall's ambient hypothesis. -/
public theorem BinaryHallCore.isBinaryHallFactor
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hchar : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A)
    {E D Z : Subgroup P} (h : BinaryHallCore E D Z) :
    IsBinaryHallFactor D := by
  rcases h.isBinaryHallFactor_or_exists_noncyclic_characteristic_abelian hP with
    hD | ⟨A, hAc, hAa, hAn⟩
  · exact hD
  · exact False.elim (hAn (hchar A hAc hAa))
