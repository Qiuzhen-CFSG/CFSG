module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModelsSmall
public import Theory.SpecificGroups.SymplecticFour.SylowComponentUnique
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.SylowComponentUnique
public import Theory.SpecificGroups.G2.SylowComponentUnique
public import Theory.SpecificGroups.Triality.SylowComponentUnique
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Transporting the higher rank-two component calculations

The actual model isomorphisms transport the intrinsic PSL₃, PSp₄, G₂ and
graph-field triality results. The field cardinalities supply characteristic
two; simplicity and perfectness are inherited from the original source group.
The triality specialization retains every positive binary exponent.
Source: Aschbacher--Smith A.3.12, pp.47--48; 1.2.8(1), p.506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]
theorem linear_three_even_sylow_overgroup_component_unique {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSL G 3 (2^n)) : SylowOvergroupComponentUnique G := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact SylowOvergroupComponentUnique.of_equiv e
    (Matrix.PSL3.LinearThree.sylow_overgroup_component_unique F hF hn)

theorem symplectic_even_sylow_overgroup_component_unique {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp G 2 (2^n)) : SylowOvergroupComponentUnique G := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  let : IsSimpleGroup (Theory.SpecificGroups.SymplecticFour.Sp F) := a.symm.isSimpleGroup
  let : Group.IsPerfect (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  exact SylowOvergroupComponentUnique.of_equiv a
    (Theory.SpecificGroups.SymplecticFour.sylow_overgroup_component_unique F hF (by omega))

theorem g2_even_sylow_overgroup_component_unique {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At G (2^n)) : SylowOvergroupComponentUnique G := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : IsSimpleGroup (Atlas.G2.Model F) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Atlas.G2.Model F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply SylowOvergroupComponentUnique.of_equiv e
  apply Atlas.G2.sylow_overgroup_component_unique F
  rw [hF]
  exact (show (2 : ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) (by omega))

omit [IsSimpleGroup G] in
theorem triality_even_sylow_overgroup_component_unique {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2^n) G) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n (by omega)).mp hm
  let : Group.IsPerfect (Triality.Standard.BinaryCarrier n (by omega)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact SylowOvergroupComponentUnique.of_equiv e
    (Triality.Standard.binary_sylow_overgroup_component_unique n (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
