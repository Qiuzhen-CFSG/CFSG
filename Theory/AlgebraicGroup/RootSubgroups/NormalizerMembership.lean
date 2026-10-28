module

public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.Tori.Semisimple

universe u

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

public lemma mem_rootSubgroup_normalizer_of_mem_torus
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (hD : D.IsRealization)
    (g : Variety.Point K) (hg : g ∈ T) (α : D.Root) :
    g ∈ (D.rootSubgroup α).normalizer := by
  change g ∈ Subgroup.normalizer
    ((D.rootSubgroup α).toSubgroup : Set (Variety.Point K))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  change x ∈ D.rootSubgroup α ↔ g * x * g⁻¹ ∈ D.rootSubgroup α
  constructor
  · intro hx
    have hginv : g⁻¹ ∈ T := T.toSubgroup.inv_mem hg
    simpa only [inv_inv] using
      (hD.2.2.1 α).1.1 g⁻¹ hginv x hx
  · intro hx
    simpa [mul_assoc] using
      (hD.2.2.1 α).1.1 g hg (g * x * g⁻¹) hx

/-- Every torus element normalizes every realized root subgroup. -/
public lemma torus_le_iInf_rootSubgroup_normalizers
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (hD : D.IsRealization) :
    T.toSubgroup ≤
      ⨅ α, Subgroup.normalizer
        ((D.rootSubgroup α).toSubgroup : Set (Variety.Point K)) := by
  intro g hg
  rw [Subgroup.mem_iInf]
  intro α
  exact mem_rootSubgroup_normalizer_of_mem_torus D hD g hg α

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A root weight is nontrivial once the ambient torus is self-centralizing. -/
public lemma IsTorusRootSubgroup.rootWeight_ne_one_of_centralizer_eq
    {K : Variety k} [AlgebraicGroup K] {T X : ClosedSubgroup K}
    (hT : IsSubtorus T)
    (hcentralizer : T.centralizer.toSubgroup = T.toSubgroup)
    (hX : IsTorusRootSubgroup T X) (χ : TorusWeight T)
    (hχ : RootWeightEquation T X χ) : χ ≠ 1 := by
  intro hχone
  have hstructure := hX.invariant_unipotent_ne_bot
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hstructure.2.2
  let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
  let yX : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨y.1, y.2⟩
  let qy : Variety.Point (KPlus k) := x.inv.onPoints yX
  let a : k := Multiplicative.toAdd (additiveGroupPointEquiv k qy)
  have hqya : kPlusPoint a = qy := by
    apply (additiveGroupPointEquiv k).injective
    exact Multiplicative.ofAdd.apply_symm_apply (additiveGroupPointEquiv k qy)
  have hxa : X.includePoint (x.value a) = y.1 := by
    change (X.pointEquiv (x.hom.onPoints (kPlusPoint a))).val = y.1
    rw [hqya, x.inv_hom_id]
    exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨y.1, y.2⟩)
  have hycentralizer : y.1 ∈ T.centralizer.toSubgroup := by
    change y.1 ∈ Subgroup.centralizer (T.toSubgroup : Set (Variety.Point K))
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    let sT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨s, hs⟩
    have heq := hχ x a sT
    rw [hχone] at heq
    have hsval : T.includePoint sT = s := by
      exact congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨s, hs⟩)
    rw [hxa, hsval] at heq
    have hone : (1 : TorusWeight T).pointCharacter sT = 1 := by rfl
    rw [hone, one_mul] at heq
    rw [hxa] at heq
    calc
      s * y.1 = s * (s⁻¹ * y.1 * s) := congrArg (fun z => s * z) heq.symm
      _ = y.1 * s := by simp [mul_assoc]
  have hyT : y.1 ∈ T.toSubgroup := by
    rw [← hcentralizer]
    exact hycentralizer
  let yT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨y.1, hyT⟩
  have hysemisimpleT : IsSemisimpleElement T.carrierVariety yT :=
    hT.all_semisimple yT
  have hysemisimple : IsSemisimpleElement K y.1 := by
    have h := (closedSubgroup_semisimpleElement_iff T hyT).mpr hysemisimpleT
    simpa [yT] using h
  have hyunipotentX : IsUnipotentElement X.carrierVariety yX :=
    hstructure.2.1 yX
  have hyunipotent : IsUnipotentElement K y.1 := by
    have h := (closedSubgroup_unipotentElement_iff X y.2).mpr hyunipotentX
    simpa [yX] using h
  apply hy
  apply Subtype.ext
  exact semisimple_unipotent_eq_one y.1 hysemisimple hyunipotent

end

end Theory.AlgebraicGroup
