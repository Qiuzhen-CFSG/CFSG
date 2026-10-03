module

public import Theory.GroupAction.RegularWreathFunctionModule
public import Theory.Representation.FourGroupMatrixCoordinates
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Cardinal bound for an action permuting complementary four-groups

A faithful action on two complementary elementary four-groups embeds into
SL₂(2) wr C₂ when it permutes the two supports. Consequently its order divides
72, without any prior assumption on the actor order. The coordinate and wreath
construction follows `ComplementaryFourWreathAction`, but stops at an injective
homomorphism instead of assuming equal cardinalities to obtain an equivalence.

This is the counting half of the faithful elementary-nine support-pair argument.
The construction of the support pair is a separate representation-theoretic step.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionOne

private theorem support_aut_preserving {A : Type*} [Group A]
    (automorphism : MulAut (A × A))
    (hfirst : ∀ value : A, (automorphism (value, 1)).2 = 1)
    (hsecond : ∀ value : A, (automorphism (1, value)).1 = 1) :
    ∃ first second : MulAut A, ∀ value : A × A,
      automorphism value = (first value.1, second value.2) := by
  let first : A →* A := (MonoidHom.fst A A).comp
    (automorphism.toMonoidHom.comp (MonoidHom.inl A A))
  let second : A →* A := (MonoidHom.snd A A).comp
    (automorphism.toMonoidHom.comp (MonoidHom.inr A A))
  have hformula (value : A × A) : automorphism value = (first value.1, second value.2) := by
    have hsplit : value = (value.1, 1) * (1, value.2) := by ext <;> simp
    calc
      automorphism value = automorphism (value.1, 1) * automorphism (1, value.2) := by
        rw [← map_mul, ← hsplit]
      _ = (first value.1, second value.2) := by
        ext <;> simp [first, second, hfirst, hsecond]
  have hfirstbij : Function.Bijective first := by
    constructor
    · intro left right hequal
      have hpair : automorphism (left, 1) = automorphism (right, 1) := by
        simpa [hformula] using congrArg (fun value : A => (value, (1 : A))) hequal
      exact congrArg Prod.fst (automorphism.injective hpair)
    · intro value
      obtain ⟨pair, hpair⟩ := automorphism.surjective (value, 1)
      exact ⟨pair.1, by simpa [hformula] using congrArg Prod.fst hpair⟩
  have hsecondbij : Function.Bijective second := by
    constructor
    · intro left right hequal
      have hpair : automorphism (1, left) = automorphism (1, right) := by
        simpa [hformula] using congrArg (fun value : A => ((1 : A), value)) hequal
      exact congrArg Prod.snd (automorphism.injective hpair)
    · intro value
      obtain ⟨pair, hpair⟩ := automorphism.surjective (1, value)
      exact ⟨pair.2, by simpa [hformula] using congrArg Prod.snd hpair⟩
  exact ⟨MulEquiv.ofBijective first hfirstbij, MulEquiv.ofBijective second hsecondbij,
    hformula⟩

private theorem support_aut_swapping {A : Type*} [Group A]
    (automorphism : MulAut (A × A))
    (hfirst : ∀ value : A, (automorphism (value, 1)).1 = 1)
    (hsecond : ∀ value : A, (automorphism (1, value)).2 = 1) :
    ∃ first second : MulAut A, ∀ value : A × A,
      automorphism value = (first value.2, second value.1) := by
  let swap : MulAut (A × A) := MulEquiv.prodComm
  obtain ⟨first, second, hformula⟩ :=
    support_aut_preserving (swap.trans automorphism) hsecond hfirst
  exact ⟨first, second, fun value => by simpa [swap] using hformula (value.2, value.1)⟩

private theorem support_pair_coordinates {V A : Type*} [Group V] [IsMulCommutative V]
    [Group A] (first second : Subgroup V) (hcompl : IsCompl first second)
    (firstEquiv : first ≃* A) (secondEquiv : second ≃* A) :
    ∃ coordinates : V ≃* (A × A),
      (∀ value, value ∈ first ↔ (coordinates value).2 = 1) ∧
      (∀ value, value ∈ second ↔ (coordinates value).1 = 1) := by
  let product := first.subtype.noncommCoprod second.subtype (fun _ _ => Commute.all _ _)
  have hinjective : Function.Injective product :=
    Subgroup.mul_injective_of_disjoint hcompl.disjoint
  have hsurjective : Function.Surjective product := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    exact hcompl.sup_eq_top
  let productEquiv := MulEquiv.ofBijective product ⟨hinjective, hsurjective⟩
  let coordinates := productEquiv.symm.trans (firstEquiv.prodCongr secondEquiv)
  have hformula (left : first) (right : second) :
      coordinates ((left : V) * (right : V)) = (firstEquiv left, secondEquiv right) :=
    congrArg (firstEquiv.prodCongr secondEquiv) (productEquiv.symm_apply_apply (left, right))
  refine ⟨coordinates, ?_, ?_⟩
  · intro value
    obtain ⟨⟨left, right⟩, rfl⟩ := hsurjective value
    change ((left : V) * (right : V) ∈ first ↔
      (coordinates ((left : V) * (right : V))).2 = 1)
    rw [hformula]
    change ((left : V) * (right : V) ∈ first ↔ secondEquiv right = 1)
    rw [secondEquiv.map_eq_one_iff]
    constructor
    · intro hmember
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hcompl.disjoint
        (by simpa using first.mul_mem (first.inv_mem left.property) hmember) right.property
    · intro hequal
      simp [hequal]
  · intro value
    obtain ⟨⟨left, right⟩, rfl⟩ := hsurjective value
    change ((left : V) * (right : V) ∈ second ↔
      (coordinates ((left : V) * (right : V))).1 = 1)
    rw [hformula]
    change ((left : V) * (right : V) ∈ second ↔ firstEquiv left = 1)
    rw [firstEquiv.map_eq_one_iff]
    constructor
    · intro hmember
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hcompl.disjoint left.property
        (by simpa using second.mul_mem hmember (second.inv_mem right.property))
    · intro hequal
      simp [hequal]

private theorem support_action_coordinates {G V A : Type*} [Group G] [Group V]
    [Group A] [MulDistribMulAction G V]
    (first second : Subgroup V) (coordinates : V ≃* (A × A))
    (hfirst : ∀ value, value ∈ first ↔ (coordinates value).2 = 1)
    (hsecond : ∀ value, value ∈ second ↔ (coordinates value).1 = 1)
    (element : G)
    (hperm :
      (first.map (MulDistribMulAction.toMulAut G V element).toMonoidHom = first ∧
       second.map (MulDistribMulAction.toMulAut G V element).toMonoidHom = second) ∨
      (first.map (MulDistribMulAction.toMulAut G V element).toMonoidHom = second ∧
       second.map (MulDistribMulAction.toMulAut G V element).toMonoidHom = first)) :
    (∃ left right : MulAut A, ∀ value : V,
      coordinates (element • value) = (left (coordinates value).1, right (coordinates value).2)) ∨
    (∃ left right : MulAut A, ∀ value : V,
      coordinates (element • value) = (left (coordinates value).2, right (coordinates value).1)) := by
  let automorphism : MulAut (A × A) := coordinates.symm.trans
    ((MulDistribMulAction.toMulAut G V element).trans coordinates)
  have hmember {source target : Subgroup V}
      (hequal : source.map (MulDistribMulAction.toMulAut G V element).toMonoidHom = target)
      {value : V} (hvalue : value ∈ source) : element • value ∈ target := by
    rw [← hequal]
    exact ⟨value, hvalue, rfl⟩
  rcases hperm with hperm | hperm
  · obtain ⟨left, right, hformula⟩ := support_aut_preserving automorphism
      (fun value => (hfirst _).mp (hmember hperm.1 ((hfirst _).mpr (by simp))))
      (fun value => (hsecond _).mp (hmember hperm.2 ((hsecond _).mpr (by simp))))
    exact Or.inl ⟨left, right, fun value => by
      simpa [automorphism] using hformula (coordinates value)⟩
  · obtain ⟨left, right, hformula⟩ := support_aut_swapping automorphism
      (fun value => (hsecond _).mp (hmember hperm.1 ((hfirst _).mpr (by simp))))
      (fun value => (hfirst _).mp (hmember hperm.2 ((hsecond _).mpr (by simp))))
    exact Or.inr ⟨left, right, fun value => by
      simpa [automorphism] using hformula (coordinates value)⟩

private def support_pair_function (A : Type*) [Group A] :
    (A × A) ≃* (Multiplicative (ZMod 2) → A) where
  toFun pair index := if index = 1 then pair.1 else pair.2
  invFun values := (values 1, values (Multiplicative.ofAdd 1))
  left_inv pair := by simp
  right_inv values := by
    funext index
    have hcases : ∀ index : Multiplicative (ZMod 2),
        index = 1 ∨ index = Multiplicative.ofAdd 1 := by decide
    rcases hcases index with rfl | rfl <;>
      simp [show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 from by decide]
  map_mul' left right := by
    funext index
    by_cases hequal : index = 1 <;> simp [hequal]

private theorem support_exists_wreath_action {G V A D : Type*} [Group G] [Group V]
    [Group A] [Group D] [MulDistribMulAction G V] [MulDistribMulAction D A]
    (coordinates : V ≃* (A × A))
    (hrepresent : ∀ automorphism : MulAut A, ∃ element : D,
      ∀ value, element • value = automorphism value)
    (element : G)
    (hperm :
      (∃ left right : MulAut A, ∀ value : V,
        coordinates (element • value) = (left (coordinates value).1, right (coordinates value).2)) ∨
      (∃ left right : MulAut A, ∀ value : V,
        coordinates (element • value) = (left (coordinates value).2, right (coordinates value).1))) :
    letI := RegularWreathProduct.functionModule D (Multiplicative (ZMod 2)) A
    ∃ wreath : RegularWreathProduct D (Multiplicative (ZMod 2)), ∀ value,
      support_pair_function A (coordinates (element • value)) =
        wreath • support_pair_function A (coordinates value) := by
  let _ := RegularWreathProduct.functionModule D (Multiplicative (ZMod 2)) A
  have hcases : ∀ index : Multiplicative (ZMod 2),
      index = 1 ∨ index = Multiplicative.ofAdd 1 := by decide
  have hnontrivial : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
  rcases hperm with ⟨left, right, hformula⟩ | ⟨left, right, hformula⟩
  · obtain ⟨first, hfirst⟩ := hrepresent left
    obtain ⟨second, hsecond⟩ := hrepresent right
    refine ⟨⟨(fun index => if index = 1 then first else second), 1⟩, ?_⟩
    intro value
    funext index
    rw [RegularWreathProduct.functionModule_smul_apply, hformula]
    rcases hcases index with rfl | rfl <;>
      simp [support_pair_function, hnontrivial, hfirst, hsecond]
  · obtain ⟨first, hfirst⟩ := hrepresent left
    obtain ⟨second, hsecond⟩ := hrepresent right
    refine ⟨⟨(fun index => if index = 1 then first else second), Multiplicative.ofAdd 1⟩, ?_⟩
    intro value
    funext index
    rw [RegularWreathProduct.functionModule_smul_apply, hformula]
    have hinverse : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide
    have hsquare : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases hcases index with rfl | rfl <;>
      simp [support_pair_function, hnontrivial, hinverse, hsquare, hfirst, hsecond]

private theorem support_card_dvd_wreath {G V A D : Type*} [Group G] [Group V]
    [Group A] [Group D] [Nontrivial A]
    [MulDistribMulAction G V] [MulDistribMulAction D A]
    [FaithfulSMul G V] [FaithfulSMul D A]
    (coordinates : V ≃* (A × A))
    (hrepresent : ∀ automorphism : MulAut A, ∃ element : D,
      ∀ value, element • value = automorphism value)
    (hperm : ∀ element : G,
      (∃ left right : MulAut A, ∀ value : V,
        coordinates (element • value) = (left (coordinates value).1, right (coordinates value).2)) ∨
      (∃ left right : MulAut A, ∀ value : V,
        coordinates (element • value) = (left (coordinates value).2, right (coordinates value).1))) :
    Nat.card G ∣ Nat.card (RegularWreathProduct D (Multiplicative (ZMod 2))) := by
  classical
  let _ := RegularWreathProduct.functionModule D (Multiplicative (ZMod 2)) A
  let _ := RegularWreathProduct.functionModule_faithful D (Multiplicative (ZMod 2)) A
  let moduleEquiv := coordinates.trans (support_pair_function A)
  have hexists (element : G) : ∃ wreath : RegularWreathProduct D (Multiplicative (ZMod 2)),
      ∀ value, moduleEquiv (element • value) = wreath • moduleEquiv value :=
    support_exists_wreath_action coordinates hrepresent element (hperm element)
  choose represent hrepresent using hexists
  have hequal {left right : RegularWreathProduct D (Multiplicative (ZMod 2))}
      (haction : ∀ value : V, left • moduleEquiv value = right • moduleEquiv value) :
      left = right := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Multiplicative (ZMod 2) → A)
    intro value
    obtain ⟨value, rfl⟩ := moduleEquiv.surjective value
    exact haction value
  let representation : G →* RegularWreathProduct D (Multiplicative (ZMod 2)) :=
    { toFun := represent
      map_one' := hequal (fun value => by rw [← hrepresent, one_smul, one_smul])
      map_mul' := fun left right => hequal (fun value => by
        rw [← hrepresent, mul_smul, hrepresent, hrepresent, mul_smul]) }
  have hinjective : Function.Injective representation := by
    intro left right heq
    apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
    intro value
    apply moduleEquiv.injective
    rw [hrepresent, hrepresent]
    exact congrArg (fun wreath => wreath • moduleEquiv value) heq
  exact Subgroup.card_dvd_of_injective representation hinjective

private theorem support_elementary_subgroup {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (support : Subgroup V) : IsElementaryAbelian 2 support := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro value
  apply Subtype.ext
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 V) value

public theorem nineCoreSupport_card_dvd_of_complementary_four
    {K V : Type*} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (first second : Subgroup V) (hcompl : IsCompl first second)
    (hfirstcard : Nat.card first = 4) (hsecondcard : Nat.card second = 4)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥)
    (hperm : ∀ element : K,
      (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first ∧
       second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second) ∨
      (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second ∧
       second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first)) :
    Nat.card K ∣ 72 := by
  let _ : IsElementaryAbelian 2 first := support_elementary_subgroup first
  let _ : IsElementaryAbelian 2 second := support_elementary_subgroup second
  obtain ⟨firstEquiv, _⟩ :=
    FourGroupMatrixCoordinates.exists_four_group_matrix_coordinates hfirstcard
  obtain ⟨secondEquiv, _⟩ :=
    FourGroupMatrixCoordinates.exists_four_group_matrix_coordinates hsecondcard
  obtain ⟨coordinates, hfirst, hsecond⟩ :=
    support_pair_coordinates first second hcompl firstEquiv secondEquiv
  let _ : FaithfulSMul K V := by
    rw [faithfulSMul_iff]
    intro element hfixed
    have hmember : element ∈ fixingSubgroup K (Set.univ : Set V) :=
      (mem_fixingSubgroup_iff K).mpr (fun value _ => hfixed value)
    simpa [hfaith] using hmember
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := FourGroupMatrixCoordinates.naturalAction_faithful
  have hdivides := support_card_dvd_wreath coordinates
    FourGroupMatrixCoordinates.naturalAction_surjective
    (fun element => support_action_coordinates first second coordinates hfirst hsecond
      element (hperm element))
  have hcard : Nat.card (RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))) = 72 := by
    obtain ⟨matrixEquiv⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [RegularWreathProduct.card, Nat.card_congr matrixEquiv.toEquiv, Nat.card_perm]
    norm_num [Nat.factorial]
  exact hcard ▸ hdivides

end Stellmacher.SectionOne
