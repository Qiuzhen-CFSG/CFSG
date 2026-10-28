module

public import Theory.SpecificGroups.Triality.ElementaryCentralKernel
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Injectivity
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.SpecificGroups.Triality.LeviIdentification

/-!
# A nonabelian two-subgroup in genuine binary triality

The checked twelve-root normal form makes the split positive subgroup a
two-group. Restricting to elementary fixed points preserves this property.
The central positive root and folded three-arm root do not commute: their
products differ in matrix entry (0,10) of the numbered Geck basis. The proved
central-kernel theorem makes their image in the actual triality carrier
faithful. Binary PSL₂ has abelian Sylow two-subgroups, since these are
conjugate to the additive upper-transvection group, so it cannot be isomorphic
to this carrier. The argument includes the binary endpoint q = 2.

Source: GLS3 §§2.3–2.6 (`refs/KGroup/GLS3/chapter2.tex`), applied to the
model separation in Aschbacher–Smith 1.2.1(3), printed p.504, and E.6.8,
printed p.247 (`refs/quasithin.pdf`).
-/

public section

open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ElementaryCentralKernel
open Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
open Matrix
open scoped MatrixGroups
noncomputable section
namespace Triality.Standard.ModelSeparation

private theorem central_folded_not_commute (P : Parameters) (hp : P.prime = 2) :
    ¬ Commute (simpleRoot P true 1 1) (foldedRoot P true 1) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hroot (i : Fin 4) : coordinateHom P (simpleRoot P true i 1) =
      rootMatrix i true (1 : ExtensionField P) := positiveMatrix_coordinates i 1
  intro hc
  have he := congrArg (fun x : SplitGroup P => coordinateHom P x 0 10) hc.eq
  simp only [foldedRoot, map_one, map_mul, hroot, ← Matrix.mul_assoc] at he
  simp [mul_root_entry, rootCols, quadraticPosition, rootMatrix, linearSupport] at he

/-- The actual elementary positive fixed-point subgroup is a two-group. -/
theorem elementaryPositive_isPGroup (n : ℕ) (hn : 0 < n) :
    IsPGroup 2 (elementaryPositive (binaryParameters n hn)) := by
  let P := binaryParameters n hn
  have hP : IsPGroup 2 (positiveSubgroup P) :=
    PositiveCoordinates.isPGroup_positiveSubgroup_of_normalForm P
      (PositiveCoordinates.orderedProduct_injective P)
      (PositiveCoordinates.range_orderedProduct_binary n hn)
  let g : elementaryPositive P →* positiveSubgroup P :=
    ((elementaryInclusion P).comp (elementaryPositive P).subtype).codRestrict _
      (fun x => x.property)
  apply hP.of_injective g
  intro a b h
  have he := congrArg (fun z : positiveSubgroup P => (z : SplitGroup P)) h
  exact Subtype.ext (Subtype.ext (Subtype.ext he))

/-- Two explicit fixed root elements witness noncommutativity upstairs. -/
theorem elementaryPositive_not_commutative (P : Parameters) (hp : P.prime = 2) :
    ¬ IsMulCommutative (elementaryPositive P) := by
  let x := centralElementary P true 1 (map_one _)
  let y := foldedElementary P hp true 1
  have hx : x ∈ elementaryPositive P := Subgroup.subset_closure ⟨1, 1, rfl⟩
  have hy : y ∈ elementaryPositive P := by
    change foldedRoot P true 1 ∈ positiveSubgroup P
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.subset_closure ⟨0, 1, rfl⟩)
        (Subgroup.subset_closure ⟨2, fieldFrobenius P 1, rfl⟩))
      (Subgroup.subset_closure ⟨3, fieldFrobenius P (fieldFrobenius P 1), rfl⟩)
  intro h
  have hc := h.is_comm.comm (⟨x, hx⟩ : elementaryPositive P) ⟨y, hy⟩
  exact central_folded_not_commute P hp
    (congrArg (fun z : elementaryPositive P => elementaryInclusion P z.val) hc)

private theorem commutative_of_twoGroup_embedding {A F : Type*} [Group A] [Field F]
    [Finite F] [CharP F 2] (hA : IsPGroup 2 A)
    (f : A →* SL(2, F)) (hf : Function.Injective f) : IsMulCommutative A := by
  obtain ⟨S, hS⟩ := (hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let g : A →* S := f.codRestrict (S : Subgroup _) (fun a => hS ⟨a, rfl⟩)
  let e := Sylow.equiv S (SpecialLinearGroup.upperUnipotentSylow F 2)
  let u := MonoidHom.ofInjective (SpecialLinearGroup.upperUnipotentHom_injective F)
  let j : A →* Multiplicative F := u.symm.toMonoidHom.comp (e.toMonoidHom.comp g)
  have hj : Function.Injective j := by
    intro a b h
    exact hf (congrArg Subtype.val (e.injective (u.symm.injective h)))
  exact ⟨⟨fun a b => hj (by simp only [map_mul, mul_comm])⟩⟩

/-- The genuine binary triality carrier is never a binary PSL₂ matrix group. -/
theorem not_equiv_binary_psl2 (n : ℕ) (hn : 0 < n) (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : Carrier (binaryParameters n hn) ≃* PSL(2,F)) : False := by
  let P := binaryParameters n hn
  let g : elementaryPositive P →* SL(2,F) :=
    (Theory.PSL2.sl2QuotientEquiv F).symm.toMonoidHom.comp
      (e.toMonoidHom.comp (positiveToCarrier P))
  have hg : Function.Injective g := (Theory.PSL2.sl2QuotientEquiv F).symm.injective.comp
    (e.injective.comp (positiveToCarrier_injective P rfl))
  exact elementaryPositive_not_commutative P rfl
    (commutative_of_twoGroup_embedding (elementaryPositive_isPGroup n hn) g hg)

end Triality.Standard.ModelSeparation
