module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSporadic
public import Theory.SpecificGroups.SymplecticSix.BinarySylowAutomorphisms
public import Theory.GroupTheory.FrattiniFlagQuotientPair
public import Theory.SpecificGroups.SymmetricFourSolvable
import all Theory.GroupTheory.FrattiniFlagQuotientPair
import all Theory.SpecificGroups.SymplecticSix.BinarySylowAutomorphisms

/-!
# The binary symplectic outer exclusion for the original binary-three residual

In the actual Sp₆(2) Sylow coordinates, the double centralizer of the
Frattini subgroup consists exactly of the elements with first and third
coordinates zero. Its image in the order-sixteen Frattini quotient has
order four, as does the quotient by that image. Both sections are invariant
under every Sylow automorphism. Their automorphism groups are solvable,
and the common action kernel is a two-group by the Burnside basis theorem.
Thus the full Sylow automorphism group is solvable.

Sylow restriction and descent through the entire component center exclude
the actual SL₃(2) outer section. Four odd-field outer families remain in
the original catalogue; the Chapter12 application retains the same H-star
actor, component and residual.

The proof-only imports extend the existing Sylow coordinates and invariant
flag kernel without changing their public boundaries. This source-specific
application introduces no new model assumption. Source: Aschbacher--Smith
4.4.10--11, 7.3.4 and 7.6.1, printed pp.621,699,702, refs/quasithin.pdf.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSymplectic
open Theory.SpecificGroups.SymplecticSix
open BinarySylowAutomorphisms

private theorem centralizer_coordinates (x : Parameters)
    (hx : x ∈ centralizer (frattini Parameters : Set Parameters)) :
    x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 7 = 0 ∧ x 8 = 0 := by
  let a : Parameters := ⟨![0,1,0,0,0,0,0,0,0]⟩
  let b : Parameters := ⟨![0,0,0,0,0,1,0,0,0]⟩
  let c : Parameters := ⟨![0,0,0,0,0,0,1,1,0]⟩
  have ha : a ∈ frattini Parameters := by rw [frattini_eq_kernel,kernel_mem]; decide
  have hb : b ∈ frattini Parameters := by rw [frattini_eq_kernel,kernel_mem]; decide
  have hc : c ∈ frattini Parameters := by rw [frattini_eq_kernel,kernel_mem]; decide
  have h0 := centralizer_first_zero x hx
  have h1 := congrArg (fun z : Parameters => z 4) ((mem_centralizer_iff.mp hx) c hc)
  have h2 := congrArg (fun z : Parameters => z 4) ((mem_centralizer_iff.mp hx) b hb)
  have h7 := congrArg (fun z : Parameters => z 4) ((mem_centralizer_iff.mp hx) a ha)
  have h8 := congrArg (fun z : Parameters => z 5) ((mem_centralizer_iff.mp hx) a ha)
  change (product c x) 4 = (product x c) 4 at h1
  change (product b x) 4 = (product x b) 4 at h2
  change (product a x) 4 = (product x a) 4 at h7
  change (product a x) 5 = (product x a) 5 at h8
  have h2' : x 2 = 0 := by simpa [product,b] using h2
  have h7' : x 7 = 0 := by simpa [product,a] using h7.symm
  have h8' : x 8 = 0 := by simpa [product,a] using h8.symm
  have h1' : x 1 = 0 := by simpa [product,c,h0,h2'] using h1
  exact ⟨h0,h1',h2',h7',h8'⟩

private abbrev doubleCentralizer : Subgroup Parameters :=
  centralizer (centralizer (frattini Parameters : Set Parameters) : Set Parameters)

private theorem doubleCentralizer_mem (x : Parameters) :
    x ∈ doubleCentralizer ↔ x 0 = 0 ∧ x 2 = 0 := by
  constructor
  · intro hx
    let b : Parameters := ⟨![0,0,0,0,0,1,0,0,0]⟩
    have hb : b ∈ centralizer (frattini Parameters : Set Parameters) := by
      rw [mem_centralizer_iff]
      intro y hy
      rw [frattini_eq_kernel] at hy
      have hy := (kernel_mem y).mp hy
      change product y b = product b y
      apply Parameters.ext
      funext i
      fin_cases i <;> simp [product,b,hy.1,hy.2.1,add_comm]
    have h0 := congrArg (fun z : Parameters => z 4)
      ((mem_centralizer_iff.mp hx) centralElement centralElement_mem)
    have h2 := congrArg (fun z : Parameters => z 4) ((mem_centralizer_iff.mp hx) b hb)
    change (product centralElement x) 4 = (product x centralElement) 4 at h0
    change (product b x) 4 = (product x b) 4 at h2
    exact ⟨by simpa [product,centralElement] using h0, by simpa [product,b] using h2⟩
  · rintro ⟨h0,h2⟩
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨hy0,hy1,hy2,hy7,hy8⟩ := centralizer_coordinates y hy
    change product y x = product x y
    apply Parameters.ext
    funext i
    fin_cases i <;> simp [product,h0,h2,hy0,hy1,hy2,hy7,hy8,add_comm]

private abbrev flag : Subgroup (Parameters ⧸ frattini Parameters) :=
  doubleCentralizer.map (QuotientGroup.mk' (frattini Parameters))

private theorem flag_invariant (a : MulAut Parameters) :
    flag.map (quotientAut (frattini Parameters) a).toMonoidHom = flag := by
  apply le_antisymm
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    change quotientAut (frattini Parameters) a (QuotientGroup.mk' (frattini Parameters) x) ∈ flag
    rw [quotientAut_apply_mk]
    exact mem_map_of_mem _
      ((characteristic_iff_map_le.mp (inferInstance : doubleCentralizer.Characteristic) a)
        (mem_map_of_mem _ hx))
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨QuotientGroup.mk' (frattini Parameters) (a.symm x),?_,?_⟩
    · exact mem_map_of_mem _
        ((characteristic_iff_map_le.mp (inferInstance : doubleCentralizer.Characteristic) a.symm)
          (mem_map_of_mem _ hx))
    · change quotientAut (frattini Parameters) a (QuotientGroup.mk' (frattini Parameters) (a.symm x)) = _
      rw [quotientAut_apply_mk,a.apply_symm_apply]

private def frattiniEquiv : Parameters ⧸ frattini Parameters ≃* E :=
  (QuotientGroup.quotientMulEquivOfEq frattini_eq_kernel).trans
    (QuotientGroup.quotientKerEquivOfSurjective quotientMap quotientMap_surjective)

private theorem frattiniEquiv_apply (x : Parameters) :
    frattiniEquiv (QuotientGroup.mk' (frattini Parameters) x) = quotientMap x := rfl

private def flagEquiv : flag ≃ (Fin 2 → ZMod 2) where
  toFun v := ![(frattiniEquiv v.val).toAdd 2,(frattiniEquiv v.val).toAdd 3]
  invFun v := ⟨QuotientGroup.mk' (frattini Parameters)
    (⟨![0,0,0,0,0,0,v 1,0,v 0]⟩ : Parameters),
    mem_map_of_mem _ ((doubleCentralizer_mem _).mpr ⟨rfl,rfl⟩)⟩
  left_inv := by
    rintro ⟨v,x,hx,rfl⟩
    apply Subtype.ext
    apply frattiniEquiv.injective
    have hx := (doubleCentralizer_mem x).mp hx
    dsimp only
    simp only [frattiniEquiv_apply]
    apply Equiv.injective Multiplicative.toAdd
    funext i
    change (![0,0,(![x 0,x 2,x 8,x 6+x 7] : Fin 4 → ZMod 2) 2,
      (![x 0,x 2,x 8,x 6+x 7] : Fin 4 → ZMod 2) 3+0] : Fin 4 → ZMod 2) i =
      (![x 0,x 2,x 8,x 6+x 7] : Fin 4 → ZMod 2) i
    fin_cases i <;> simp [hx.1,hx.2]
  right_inv v := by
    funext i
    dsimp only
    simp only [frattiniEquiv_apply]
    fin_cases i <;> simp [quotientMap]

private theorem flag_card : Nat.card flag = 4 := by
  rw [Nat.card_congr flagEquiv]
  simp

private theorem flag_quotient_card : Nat.card ((Parameters ⧸ frattini Parameters) ⧸ flag) = 4 := by
  have h := card_eq_card_quotient_mul_card_subgroup flag
  rw [frattini_card,flag_card] at h
  omega

private theorem small_mulAut_solvable {X : Type*} [Group X] [Finite X]
    (hX : Nat.card X = 4) : Group.IsSolvable (MulAut X) := by
  let e : X ≃ Fin 4 := Finite.equivFinOfCardEq hX
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm X) := Group.isSolvable_of_isSolvable_injective
    (f := (Equiv.permCongrHom e).toMonoidHom) (Equiv.permCongrHom e).injective
  exact Group.isSolvable_of_isSolvable_injective
    (f := MulAut.toPerm X) (fun a b he => MulEquiv.ext (fun x => Equiv.congr_fun he x))

private theorem parameters_aut_solvable : Group.IsSolvable (MulAut Parameters) := by
  let : Fact (IsPGroup 2 Parameters) := ⟨parameters_two⟩
  let : IsElementaryAbelian 2 (Parameters ⧸ frattini Parameters) :=
    isElementaryAbelian_quotient_frattini
  let ρ := quotientAut (frattini Parameters)
  let r := flagRestriction ρ flag flag_invariant
  let q := flagQuotient ρ flag flag_invariant
  let f := r.prod q
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_prod]
    exact flag_kernel_isPGroup ρ (isPGroup_quotientAut_frattini_kernel parameters_two)
      flag flag_invariant
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsSolvable (MulAut flag) := small_mulAut_solvable flag_card
  let : Group.IsSolvable (MulAut ((Parameters ⧸ frattini Parameters) ⧸ flag)) :=
    small_mulAut_solvable flag_quotient_card
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

/-- The actual binary symplectic Sylow automorphism group is solvable:
the double-centralizer flag has two sections of order four. -/
theorem binary_sylow_aut_solvable (P : Sylow 2 (Sp (ZMod 2))) :
    Group.IsSolvable (MulAut P) := by
  let e : P ≃* Parameters := (P.equiv sylow).trans sylowEquiv.symm
  let : Group.IsSolvable (MulAut Parameters) := parameters_aut_solvable
  exact Group.isSolvable_of_isSolvable_injective (f := (MulAut.congr e).toMonoidHom)
    (MulAut.congr e).injective

/-- The calculation uses the literal projective and field equivalences. -/
theorem binary_sylow_aut_solvable_of_equiv {A F : Type*}
    [Group A] [Finite A] [Field F] [Finite F]
    (hF : Nat.card F = 2) (e : A ≃* PSp F) (P : Sylow 2 A) :
    Group.IsSolvable (MulAut P) := by
  let a : A ≃* Sp (ZMod 2) :=
    (e.trans (pspFieldEquivZModTwo F hF)).trans EvenProjective.equiv.symm
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : P ≃* Q := a.subgroupMap (P : Subgroup A)
  let : Group.IsSolvable (MulAut Q) := binary_sylow_aut_solvable Q
  exact Group.isSolvable_of_isSolvable_injective (f := (MulAut.congr b).toMonoidHom)
    (MulAut.congr b).injective

/-- Every simple group with the literal PSp₆(2) marking has solvable outer
automorphisms, using the full Sylow double-centralizer flag. -/
theorem binary_outer_solvable {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ClassicalGroup.IsPSp Q 3 2) : Group.IsSolvable (MulAut.Outer Q) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (MulAut P) := binary_sylow_aut_solvable_of_equiv hF e P
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  exact MulAut.outer_isSolvable_of_sylow_aut P

private instance : IsSimpleGroup BinaryLinearThree.Group := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup
private instance : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)

/-- The actual binary-three simple section cannot survive on the binary
symplectic outer automorphism group. -/
theorem binary_no_outer_section {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ClassicalGroup.IsPSp Q 3 2)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* BinaryLinearThree.Group) :
    ¬ Function.Surjective f := by
  let := binary_outer_solvable hm
  intro hf
  exact Group.IsPerfect.not_isSolvable BinaryLinearThree.Group
    (Group.isSolvable_of_surjective hf)

/-- The exclusion preserves the full center of the original quasisimple component. -/
theorem binary_cover_exclusion {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) : ¬ ClassicalGroup.IsPSp (K ⧸ center K) 3 2 := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro hm
  exact binary_no_outer_section hm _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

/-- The four remaining outer models retain their actual field and group markings. -/
inductive RemainingOuterModel (Q : Type*) [Group Q] : Prop
  | symplectic_odd (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (iso : ClassicalGroup.IsPSp Q 2 p)
  | g2_odd (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : ClassificationModels.IsG2At Q p)
  | linear_four (p : ℕ) (hp : p.Prime) (hf : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1)
      (iso : ClassicalGroup.IsPSL Q 4 p)
  | unitary_four (p : ℕ) (hp : p.Prime) (hm : ∃ k : ℕ, p + 1 = 2 ^ k)
      (iso : ClassicalGroup.IsPSU Q 4 p)

/-- Inspect the same component's catalogue after the binary symplectic exclusion. -/
theorem remaining_outer_models {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) : RemainingOuterModel (K ⧸ center K) := by
  cases DoubledBinaryOddSporadic.remaining_outer_models hm ho with
  | symplectic_odd p hp hq e => exact .symplectic_odd p hp hq e
  | g2_odd p hp hq e => exact .g2_odd p hp hq e
  | linear_four p hp hf e => exact .linear_four p hp hf e
  | unitary_four p hp hf e => exact .unitary_four p hp hf e
  | symplectic_binary e => exact (binary_cover_exclusion ho e).elim

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSymplectic
