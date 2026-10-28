module

public import Stellmacher.DirectProductDerived
public import Stellmacher.SectionOne.OneSevenModuleProduct

/-!
# Module decomposition for the derived canonical factors

For a finite internal family of distinct canonical SL₂(2) factors, their
derived order-three subgroups form the derived internal product. The
whole elementary-two module is the product of the derived product's
fixed subgroup and the four-element supports of the derived factors.

Take derived subgroups in the existing internal product. Each canonical
factor has the same action commutator as its derived subgroup and fixes
the latter's fixed space. Consequently the derived product and full
product have identical fixed spaces. These equalities transport the
existing canonical module-product theorem to the order-three factors.

This is the precise factor-and-module form of (1.7) used in Stellmacher
(9.10)(3)--(4), printed p.57 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne

universe u

public theorem oneSevenFactor_derived_module_product
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hyp : Hypotheses G V) {n : ℕ} (D : Fin n → Subgroup G)
    (hD : ∀ i, IsOneSevenFactor (V := V) (D i)) (hinj : Function.Injective D)
    (E : Subgroup G) (hproduct : IsInternalDirectProductFamily E D) :
    let R := (commutator E).map E.subtype
    let F := fun i => (commutator (D i)).map (D i).subtype
    IsInternalDirectProductFamily R F ∧
      (∀ i, Nat.card (F i) = 3 ∧ Nat.card (commutatorAction (F i) V) = 4) ∧
      IsInternalDirectProductFamily (⊤ : Subgroup V)
        (fun i : Option (Fin n) => match i with
          | none => FixedPoints.subgroup R V
          | some i => commutatorAction (F i) V) := by
  let R := (commutator E).map E.subtype
  let F := fun i => (commutator (D i)).map (D i).subtype
  have hderived := hproduct.derived
  have hFE (i : Fin n) : F i ≤ R := by
    change F i ≤ (commutator E).map E.subtype
    rw [hderived.1]
    exact le_iSup F i
  have hfix : FixedPoints.subgroup R V = FixedPoints.subgroup E V := by
    apply le_antisymm
    · intro point hpoint
      have hEfix : E ≤ fixingSubgroup G ({point} : Set V) := by
        rw [hproduct.1]
        refine iSup_le fun i => ?_
        intro actor hactor
        rw [mem_fixingSubgroup_iff]
        intro other hother
        have heq : other = point := Set.mem_singleton_iff.mp hother
        subst other
        apply oneSevenFactor_fixes_derived_fixedPoints (D i) (hD i) actor hactor point
        rw [FixedPoints.mem_subgroup]
        intro oddActor
        exact (FixedPoints.mem_subgroup (M := R) (a := point)).mp hpoint
          ⟨oddActor, hFE i oddActor.property⟩
      rw [FixedPoints.mem_subgroup]
      intro actor
      exact (mem_fixingSubgroup_iff (M := G)).mp (hEfix actor.property) point
        (Set.mem_singleton point)
    · intro point hpoint
      rw [FixedPoints.mem_subgroup]
      intro actor
      exact (FixedPoints.mem_subgroup (M := E) (a := point)).mp hpoint
        ⟨actor, Subgroup.map_subtype_le _ actor.property⟩
  refine ⟨hderived, fun i => ⟨(hD i).2.1.2.1, (hD i).2.1.2.2⟩, ?_⟩
  have hmodule := oneSevenFactor_module_product hyp D hD hinj E hproduct.1
  have hfull (i : Fin n) : commutatorAction (F i) V = commutatorAction (D i) V :=
    (oneSevenFactor_full_commutator_eq_derived (D i) (hD i)).symm
  change IsInternalDirectProductFamily (⊤ : Subgroup V)
    (fun i : Option (Fin n) => match i with
      | none => FixedPoints.subgroup R V
      | some i => commutatorAction (F i) V)
  have hfamily : (fun i : Option (Fin n) => match i with
        | none => FixedPoints.subgroup R V
        | some i => commutatorAction (F i) V) =
      (fun i : Option (Fin n) => match i with
        | none => FixedPoints.subgroup E V
        | some i => commutatorAction (D i) V) := by
    funext i
    cases i with
    | none => exact hfix
    | some i => exact hfull i
  rw [hfamily]
  exact hmodule

end Stellmacher.SectionOne
