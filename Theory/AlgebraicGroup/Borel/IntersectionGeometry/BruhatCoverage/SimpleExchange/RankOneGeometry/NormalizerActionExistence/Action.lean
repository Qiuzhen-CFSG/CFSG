module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.Inputs
public import Theory.AlgebraicGroup.RootSubgroups.MultiplicityOne

/-!
The actual normalizer acts on the indices of any realized root datum.
Restrict conjugation to the torus, pull back characters by inverse conjugation,
and use the bijection between the supplied indices and the actual root weights.
This constructs the action without any rank-one marking or chosen lift.
Subgroup transport still requires the independent same-weight uniqueness theorem.

Source: GLS3, Theorem 1.9.5(c,f), with direct conjugation on subgroups.
-/

universe u
namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence

variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- Ambient conjugation restricted to a normalized closed subgroup. -/
@[expose] public def torusConjugation (n : T.normalizer.toSubgroup) :
    AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety := by
  let c : AlgebraicGroup.Morphism T.carrierVariety G :=
    { toVariety := (AlgebraicGroup.conjugationByMorphism G n.val).comp T.inclusion.toVariety
      map_one := by
        change n.val * T.inclusion.onPoints 1 * n.val⁻¹ = 1
        rw [map_one]
        group
      map_mul := by
        intro x y
        change n.val * T.inclusion.onPoints (x * y) * n.val⁻¹ = _
        rw [map_mul]
        change n.val * (T.inclusion.onPoints x * T.inclusion.onPoints y) * n.val⁻¹ =
          (n.val * T.inclusion.onPoints x * n.val⁻¹) *
          (n.val * T.inclusion.onPoints y * n.val⁻¹)
        group }
  exact c.codRestrictClosedSubgroup T (fun s =>
    (Subgroup.mem_normalizer_iff.mp n.property _).mp (T.pointEquiv s).property)

public theorem torusConjugation_include (n : T.normalizer.toSubgroup)
    (s : Variety.Point T.carrierVariety) :
    T.includePoint ((torusConjugation n).onPoints s) =
      n.val * T.includePoint s * n.val⁻¹ := by
  rfl

private theorem torusConjugation_one (s : Variety.Point T.carrierVariety) :
    (torusConjugation (1 : T.normalizer.toSubgroup)).onPoints s = s := by
  apply T.inclusion_injective
  change T.includePoint _ = T.includePoint _
  rw [torusConjugation_include]
  simp

private theorem torusConjugation_mul (n m : T.normalizer.toSubgroup)
    (s : Variety.Point T.carrierVariety) :
    (torusConjugation (n * m)).onPoints s =
      (torusConjugation n).onPoints ((torusConjugation m).onPoints s) := by
  apply T.inclusion_injective
  change T.includePoint _ = T.includePoint _
  rw [torusConjugation_include, torusConjugation_include, torusConjugation_include]
  change (n.val * m.val) * T.includePoint s * (n.val * m.val)⁻¹ = _
  group

/-- Pullback by inverse conjugation, matching direct conjugation of root groups. -/
@[expose] public noncomputable def weightAction (n : T.normalizer.toSubgroup) :
    TorusWeight T →* TorusWeight T :=
  TorusCharacter.pullback (torusConjugation n⁻¹)

public theorem weightAction_apply (n : T.normalizer.toSubgroup)
    (χ : TorusWeight T) (s : Variety.Point T.carrierVariety) :
    (weightAction n χ).pointCharacter s =
      χ.pointCharacter ((torusConjugation n⁻¹).onPoints s) := rfl

private theorem weightAction_one (χ : TorusWeight T) :
    weightAction 1 χ = χ := by
  apply TorusCharacter.pointCharacter_injective
  ext s
  rw [weightAction_apply]
  simp only [inv_one, torusConjugation_one]

private theorem weightAction_mul (n m : T.normalizer.toSubgroup) (χ : TorusWeight T) :
    weightAction (n * m) χ = weightAction n (weightAction m χ) := by
  apply TorusCharacter.pointCharacter_injective
  ext s
  simp only [weightAction_apply, mul_inv_rev, torusConjugation_mul]

/-- A conjugate root curve has the pulled-back character. This statement does
not require uniqueness of the subgroup associated to a weight. -/
public theorem weightEquation_conjugate (n : T.normalizer.toSubgroup)
    {X : ClosedSubgroup G} {χ : TorusWeight T}
    (hχ : RootWeightEquation T X χ) :
    RootWeightEquation T (X.conjugate n.val) (weightAction n χ) := by
  intro y t s
  let e := X.conjugateIso n.val
  let x : OneParameterParametrization X.carrierVariety :=
    { hom := e.inv.comp y.hom
      inv := y.inv.comp e.hom
      hom_inv_id := by
        intro z
        change y.inv.onPoints (e.hom.onPoints (e.inv.onPoints (y.hom.onPoints z))) = z
        rw [e.inv_hom_id, y.hom_inv_id]
      inv_hom_id := by
        intro z
        change e.inv.onPoints (y.hom.onPoints (y.inv.onPoints (e.hom.onPoints z))) = z
        rw [y.inv_hom_id, e.hom_inv_id] }
  have hy (a : k) : X.includePoint (x.value a) =
      n.val⁻¹ * (X.conjugate n.val).includePoint (y.value a) * n.val :=
    X.conjugateIso_inv_inclusion_apply n.val (y.value a)
  have hs : T.includePoint ((torusConjugation n⁻¹).onPoints s) =
      n.val⁻¹ * T.includePoint s * n.val := by
    simpa using torusConjugation_include n⁻¹ s
  apply (MulAut.conj n.val⁻¹).injective
  simp only [MulAut.conj_apply, inv_inv]
  calc
    _ = (T.includePoint ((torusConjugation n⁻¹).onPoints s))⁻¹ *
        X.includePoint (x.value t) *
        T.includePoint ((torusConjugation n⁻¹).onPoints s) := by
      rw [hs, hy]
      group
    _ = X.includePoint (x.value
        (χ.pointCharacter ((torusConjugation n⁻¹).onPoints s) * t)) := hχ x t _
    _ = _ := hy _

public theorem weightAction_isRoot (n : T.normalizer.toSubgroup)
    {χ : TorusWeight T} (hχ : IsTorusRoot T χ) :
    IsTorusRoot T (weightAction n χ) := by
  obtain ⟨X, hX, hχ⟩ := hχ
  exact ⟨X.conjugate n.val,
    hX.conjugate_of_mem_normalizer n.val n.property, weightEquation_conjugate n hχ⟩

variable {D : RootGroupData G T} (hD : D.IsRealization)

include hD in
private theorem exists_root_image (n : T.normalizer.toSubgroup) (α : D.Root) :
    ∃ β, D.rootWeight β = weightAction n (D.rootWeight α) := by
  change weightAction n (D.rootWeight α) ∈ Set.range D.rootWeight
  rw [hD.2.1]
  apply weightAction_isRoot n
  exact ⟨D.rootSubgroup α, hD.2.2.1 α⟩

private noncomputable def rootImage (n : T.normalizer.toSubgroup) (α : D.Root) : D.Root :=
  Classical.choose (exists_root_image hD n α)

private theorem rootImage_spec (n : T.normalizer.toSubgroup) (α : D.Root) :
    D.rootWeight (rootImage hD n α) = weightAction n (D.rootWeight α) :=
  Classical.choose_spec (exists_root_image hD n α)

private theorem rootImage_one (α : D.Root) : rootImage hD 1 α = α := by
  apply hD.1
  rw [rootImage_spec, weightAction_one]

private theorem rootImage_mul (n m : T.normalizer.toSubgroup) (α : D.Root) :
    rootImage hD (n * m) α = rootImage hD n (rootImage hD m α) := by
  apply hD.1
  rw [rootImage_spec, rootImage_spec, rootImage_spec, weightAction_mul]

/-- The canonical action of the actual normalizer on all realized root indices. -/
public noncomputable def rootAction : T.normalizer.toSubgroup →* Equiv.Perm D.Root where
  toFun n :=
    { toFun := rootImage hD n
      invFun := rootImage hD n⁻¹
      left_inv := fun α => by rw [← rootImage_mul, inv_mul_cancel, rootImage_one]
      right_inv := fun α => by rw [← rootImage_mul, mul_inv_cancel, rootImage_one] }
  map_one' := by
    ext α
    exact rootImage_one hD α
  map_mul' n m := by
    ext α
    exact rootImage_mul hD n m α

public theorem rootAction_weight (n : T.normalizer.toSubgroup) (α : D.Root) :
    D.rootWeight (rootAction hD n α) = weightAction n (D.rootWeight α) :=
  rootImage_spec hD n α

public theorem rootAction_neg (n : T.normalizer.toSubgroup) (α : D.Root) :
    rootAction hD n (D.neg α) = D.neg (rootAction hD n α) := by
  apply hD.1
  rw [rootAction_weight, hD.2.2.2.1, hD.2.2.2.1, rootAction_weight, map_inv]

/-- Same-weight uniqueness identifies the chosen root subgroup with its actual
conjugate. The independent fixed-radical theorem supplies this premise. -/
public theorem rootAction_transport
    (hmult : ∀ α, RootWeightSpaceMultiplicityOne T (D.rootWeight α))
    (n : T.normalizer.toSubgroup) (α : D.Root) :
    (D.rootSubgroup α).conjugate n.val = D.rootSubgroup (rootAction hD n α) := by
  apply RootWeightSpaceMultiplicityOne.rootSubgroup_eq (hmult (rootAction hD n α))
    ((hD.2.2.1 α).1.conjugate_of_mem_normalizer n.val n.property) _
    (hD.2.2.1 (rootAction hD n α)).1 (hD.2.2.1 (rootAction hD n α)).2
  rw [rootAction_weight]
  exact weightEquation_conjugate n (hD.2.2.1 α).2

/-- Root addition is transported by the actual normalizer action. -/
public theorem rootAction_add (hadd : D.IsRootAdditionComplete)
    (n : T.normalizer.toSubgroup) (α β γ : D.Root)
    (h : D.add α β = some γ) :
    D.add (rootAction hD n α) (rootAction hD n β) = some (rootAction hD n γ) := by
  apply hadd
  rw [rootAction_weight, rootAction_weight, rootAction_weight,
    hD.2.2.2.2.1 α β γ h, map_mul]

/-- Pulling a positive system back by an actual normalizer action preserves
all three positive-system clauses. -/
public theorem rootAction_positive_preimage (hadd : D.IsRootAdditionComplete)
    {P : Set D.Root} (hP : IsPositiveSystem D P) (n : T.normalizer.toSubgroup) :
    IsPositiveSystem D ((rootAction hD n) ⁻¹' P) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro α hα
    have hneg : D.neg (rootAction hD n α) ∈ P := by
      rw [← rootAction_neg]
      exact hα.2
    have hmem : rootAction hD n α ∈ P ∩ D.neg ⁻¹' P := ⟨hα.1, hneg⟩
    rw [hP.1] at hmem
    exact hmem
  · apply Set.eq_univ_of_forall
    intro α
    have hmem : rootAction hD n α ∈ P ∪ D.neg ⁻¹' P := by rw [hP.2.1]; trivial
    rcases hmem with h | h
    · exact Or.inl h
    · apply Or.inr
      change rootAction hD n (D.neg α) ∈ P
      rwa [rootAction_neg]
  · intro α hα β hβ γ hγ
    exact hP.2.2 _ hα _ hβ _ (rootAction_add hD hadd n α β γ hγ)

/-- The action kernel is detected by fixing each actual root character. -/
public theorem mem_kernel_iff (n : T.normalizer.toSubgroup) :
    n ∈ (rootAction hD).ker ↔
      ∀ α, weightAction n (D.rootWeight α) = D.rootWeight α := by
  change rootAction hD n = 1 ↔ _
  constructor
  · intro hn α
    rw [← rootAction_weight hD, hn]
    rfl
  · intro hn
    ext α
    apply hD.1
    exact (rootAction_weight hD n α).trans (hn α)

/-- The torus acts trivially. This is relative containment inside its actual
normalizer, and does not assert ambient normality of the torus. -/
public theorem torus_le_kernel (hT : IsSubtorus T) :
    T.toSubgroup.subgroupOf T.normalizer.toSubgroup ≤ (rootAction hD).ker := by
  intro n hn
  apply (mem_kernel_iff hD n).mpr
  intro α
  apply TorusCharacter.pointCharacter_injective
  ext s
  rw [weightAction_apply]
  congr 1
  have hcomm := isMulCommutative_iff.mp hT.isMulCommutative
  let t : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨n.val, hn⟩
  have ht : T.includePoint t = n.val := congrArg Subtype.val
    (T.pointEquiv.apply_symm_apply ⟨n.val, hn⟩)
  apply T.inclusion_injective
  change T.includePoint _ = T.includePoint s
  rw [torusConjugation_include]
  simp only [Subgroup.coe_inv, inv_inv]
  calc
    _ = T.inclusion.onPoints (t⁻¹ * s * t) := by
      rw [map_mul, map_mul, map_inv]
      change _ = (T.includePoint t)⁻¹ * T.includePoint s * T.includePoint t
      rw [ht]
    _ = _ := by
      have hc : t⁻¹ * s * t = s := by
        rw [hcomm t⁻¹ s, mul_assoc, inv_mul_cancel, mul_one]
      exact congrArg T.inclusion.onPoints hc

private theorem conjugation_maps_borel (hD : D.IsRealization)
    (hmult : ∀ α, RootWeightSpaceMultiplicityOne T (D.rootWeight α))
    {P : Set D.Root} {B : ClosedSubgroup G} (hBP : IsBorelOfPositiveSystem D P B)
    (n : T.normalizer.toSubgroup)
    (hpos : ∀ α ∈ P, rootAction hD n α ∈ P) :
    B.toSubgroup ≤ B.toSubgroup.comap (MulAut.conj n.val).toMonoidHom := by
  rw [hBP.torus_unipotent_generate]
  apply sup_le
  · intro t ht
    change n.val * t * n.val⁻¹ ∈ T.toSubgroup ⊔ hBP.unipotent.toSubgroup
    exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp n.property t).mp ht)
  · rw [hBP.root_generated]
    apply (RootSubgroupGenerated_le_iff D P _).mpr
    intro α hα x hx
    change n.val * x * n.val⁻¹ ∈ T.toSubgroup ⊔ RootSubgroupGenerated D P
    apply Subgroup.mem_sup_right
    apply rootSubgroup_le_RootSubgroupGenerated D (hpos α hα)
    rw [← rootAction_transport hD hmult n α]
    apply (D.rootSubgroup α).mem_conjugate_iff n.val _ |>.mpr
    simpa [mul_assoc] using hx

/-- A normalizer action preserving the positive roots normalizes their actual
Borel. This uses the literal root-generated radical in the Borel witness. -/
public theorem mem_borel_normalizer_of_preserves_positive
    (hmult : ∀ α, RootWeightSpaceMultiplicityOne T (D.rootWeight α))
    {P : Set D.Root} {B : ClosedSubgroup G} (hBP : IsBorelOfPositiveSystem D P B)
    (n : T.normalizer.toSubgroup)
    (hpos : ∀ α, rootAction hD n α ∈ P ↔ α ∈ P) :
    n.val ∈ B.normalizer.toSubgroup := by
  have hinv : ∀ α ∈ P, rootAction hD n⁻¹ α ∈ P := by
    intro α hα
    apply (hpos _).mp
    rw [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    exact hα
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    exact conjugation_maps_borel hD hmult hBP n (fun α hα => (hpos α).mpr hα) hx
  · intro hx
    have h := conjugation_maps_borel hD hmult hBP n⁻¹ hinv hx
    change (n⁻¹).val * (n.val * x * n.val⁻¹) * (n⁻¹).val⁻¹ ∈ B.toSubgroup at h
    simpa [mul_assoc] using h

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
