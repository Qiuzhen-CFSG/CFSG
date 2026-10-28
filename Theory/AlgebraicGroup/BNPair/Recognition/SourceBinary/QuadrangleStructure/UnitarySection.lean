module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryLinearActions
public import Theory.Representation.SU3.BinaryDegree
public import Theory.Representation.SubspaceQuotient

/-!
# The unitary-side Frattini section of a source quadrangle

The actual unitary root coordinates identify its intrinsic center with the
fixed field. The special-radical identity consequently gives the literal
unitary Frattini quotient order q to the sixth. A root reflection moves a
nonzero coset, since its two roots are separated by the other radical.
These conclusions include q = 2 and either endpoint orientation.

For q > 2, any surjective SU3 cover acts nontrivially on that section.
The binary minimum degree forces irreducibility: a proper nonzero submodule
and its quotient would both have trivial actions, contradicting perfectness.
No injectivity of the cover or natural coordinates are assumed here.
The CFSG UnitaryCover adapter uses this action to select the full cover.

Source: Fong--Seitz I (4D), (6A)(c), pp.21--23,37;
DGS (11.8)(f), p.176. The nonperfect q = 2 irreducibility step is separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.External BorelTorus BorelTorus.EvenCenterAction
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The intrinsic center of each conjugate unitary root has fixed-field order. -/
theorem unitary_cross_center_card
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (j : Fin 2) (w : Weyl Q)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Nat.card (center (rootAt Q split j w)) = 2^n := by
  let a : simpleRoot Q split j ≃* rootAt Q split j w :=
    ((MulAut.conj (representative w : X ⧸ Q.D)).symm.subgroupMap _).trans
      (MulEquiv.subgroupCongr (by
        simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl))
  let b := a.symm.trans (simpleRootUnitaryEquiv J Q split hn hE hfixed hJ j hVj ν)
  let c : center (hermitianUnipotentCoord J) ≃* Multiplicative (fixedField J) :=
    (MulEquiv.subgroupCongr (binary_coord_center J hn hE hfixed)).trans
      (MonoidHom.ofInjective (centralCoord_injective J)).symm
  exact (Nat.card_congr (Subgroup.centerCongr b).toEquiv).trans
    ((Nat.card_congr c.toEquiv).trans ((Nat.card_congr Multiplicative.toAdd).trans hfixed))

/-- The literal special radical has a Frattini quotient of order q to the sixth. -/
theorem unitary_frattini_section_card
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (i j : Fin 2)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hphi : (frattini (simpleRemainder Q split j)).map
        (simpleRemainder Q split j).subtype =
      (center (rootAt Q split j (Q.simple i))).map
        (rootAt Q split j (Q.simple i)).subtype)
    (hcard : Nat.card (simpleRemainder Q split j) = (2^n)^7) :
    Nat.card (frattini (simpleRemainder Q split j)) = 2^n ∧
      Nat.card ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)) = (2^n)^6 := by
  have hc : Nat.card (frattini (simpleRemainder Q split j)) = 2^n := by
    rw [←card_map_of_injective (simpleRemainder Q split j).subtype_injective,
      hphi,card_map_of_injective (rootAt Q split j (Q.simple i)).subtype_injective]
    exact unitary_cross_center_card Q split J hn hE hfixed hJ j (Q.simple i) hVj ν
  refine ⟨hc,?_⟩
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (frattini (simpleRemainder Q split j))
  rw [hcard,hc] at he
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (by decide : 0 < (2 : ℕ)) n)
  exact he.symm.trans (by ring)

/-- A coherent root reflection acts nontrivially on the literal Frattini quotient. -/
theorem remainderFrattiniAction_nontrivial_of_cross_center
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (hphi : (frattini (simpleRemainder Q split j)).map
        (simpleRemainder Q split j).subtype ≤ rootAt Q split j (Q.simple i)) :
    ∃ r, remainderFrattiniAction Q split j hVj r ≠ 1 := by
  by_contra! hh
  obtain ⟨a,ha,ha1⟩ := (simpleRoot Q split i).bot_or_exists_ne_one.resolve_left
    (simpleRoot_ne_bot Q split i)
  let v : simpleRemainder Q split j :=
    ⟨a,(opposite_roots_le_remainder Q split i j hij).1 ha⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  let v' := remainderRankOneAction Q split j hVj r⁻¹ v
  have he := congrArg (fun f : MulAut
      ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)) =>
    f (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v)) (hh r⁻¹)
  rw [remainderFrattiniAction_mk] at he
  have he' : QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v' =
      QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v := he
  have hv' : (v' : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
    rw [rootAt_eq Q split i (Q.simple j) s.val s.class_eq,rightConjugate]
    change (s.val : X ⧸ Q.D) * ((s.val : X ⧸ Q.D)⁻¹ * a *
      ((s.val : X ⧸ Q.D)⁻¹)⁻¹) * (s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i
    simpa only [inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ha
  have hdiff := mem_map_of_mem (simpleRemainder Q split j).subtype (QuotientGroup.eq.mp he')
  have hdiffV : ((v' : X ⧸ Q.D)⁻¹ * a) ∈ simpleRemainder Q split i := by
    apply (show rootAt Q split j (Q.simple i) ≤ simpleRemainder Q split i from ?_) (hphi hdiff)
    rw [remainder_eq_three_roots Q split hm i j hij]
    exact le_sup_right
  have haV : a ∈ simpleRemainder Q split i := by
    have hh := (simpleRemainder Q split i).mul_mem
      (cross_root_le_own_remainder Q split hm i j hij hv') hdiffV
    simpa only [mul_inv_cancel_left] using hh
  exact ha1 ((disjoint_iff.mp (simpleRoot_disjoint_remainder Q split i)).le ⟨ha,haV⟩)
private theorem unitary_trivial_of_small_degree
    {E V : Type*} [Field E] [Finite E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V)
    (hd : Module.finrank (ZMod 2) V < 6*n) : ρ = 1 := by
  apply MonoidHom.ext
  intro g
  by_contra hg
  exact (not_lt_of_ge (Representation.SU3.BinaryDegree.finrank_ge J hn hE hconj ρ ⟨g,hg⟩)) hd

/-- Every nontrivial action at the minimum unitary degree is irreducible,
without assuming semisimplicity. The nonperfect degree-one case is excluded. -/
theorem minimal_unitary_irreducible
    {E V : Type*} [Field E] [Finite E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V)
    (hnt : ∃ g, ρ g ≠ 1) (hd : Module.finrank (ZMod 2) V ≤ 6*n) :
    ρ.IsIrreducible := by
  let : Group.IsPerfect J.specialSubgroup :=
    Representation.SU3.BinaryDegree.isPerfect_specialSubgroup J hn hE hconj
  have : Nontrivial V := by
    by_contra! hs
    let : Subsingleton V := hs
    obtain ⟨g,hg⟩ := hnt
    exact hg (by ext v; exact Subsingleton.elim _ _)
  refine ⟨?_⟩
  intro W
  by_contra! hw
  have hb : W.toSubmodule ≠ ⊥ := fun h => hw.1 (Subrepresentation.toSubmodule_injective h)
  have ht : W.toSubmodule ≠ ⊤ := fun h => hw.2 (Subrepresentation.toSubmodule_injective h)
  have hp : 0 < Module.finrank (ZMod 2) W.toSubmodule :=
    Nat.pos_of_ne_zero (fun hz => hb (Submodule.finrank_eq_zero.mp hz))
  have hlt := Submodule.finrank_lt ht
  have hsum := Submodule.finrank_quotient_add_finrank W.toSubmodule
  have hW := unitary_trivial_of_small_degree J hn hE hconj W.toRepresentation (by omega)
  have hQ := unitary_trivial_of_small_degree J hn hE hconj W.quotientRepresentation (by omega)
  have hfix (g : J.specialSubgroup) (v : V) (hv : v ∈ W) : ρ g v = v :=
    congrArg Subtype.val (DFunLike.congr_fun (DFunLike.congr_fun hW g) (⟨v,hv⟩ : W))
  have hdiff (g : J.specialSubgroup) (v : V) : ρ g v - v ∈ W := by
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    change W.toSubmodule.mkQ (ρ g v - v) = 0
    rw [map_sub,←W.quotientRepresentation_mk]
    exact sub_eq_zero.mpr (DFunLike.congr_fun (DFunLike.congr_fun hQ g) (W.toSubmodule.mkQ v))
  have hc (g k : J.specialSubgroup) : ρ g * ρ k = ρ k * ρ g := by
    ext v
    have hg := hfix g (ρ k v - v) (hdiff k v)
    have hk := hfix k (ρ g v - v) (hdiff g v)
    simp only [map_sub] at hg hk
    change ρ g (ρ k v) = ρ k (ρ g v)
    rw [sub_eq_iff_eq_add] at hg hk
    rw [hg,hk]
    abel
  let f := ρ.toHomUnits
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : IsMulCommutative f.range := ⟨⟨by
    rintro ⟨_,g,rfl⟩ ⟨_,k,rfl⟩
    apply Subtype.ext
    exact Units.ext (hc g k)⟩⟩
  let : Subsingleton f.range := inferInstance
  obtain ⟨g,hg⟩ := hnt
  exact hg (congrArg (fun x : f.range => (x.val : Module.End (ZMod 2) V))
    (Subsingleton.elim (f.rangeRestrict g) 1))

/-- A surjective SU cover acts irreducibly on the literal unitary Frattini
section. Injectivity of that cover is not assumed. -/
theorem unitary_frattini_irreducible_of_cover
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
    (hphi : (frattini (simpleRemainder Q split j)).map
        (simpleRemainder Q split j).subtype =
      (center (rootAt Q split j (Q.simple i))).map
        (rootAt Q split j (Q.simple i)).subtype)
    (hcard : Nat.card (simpleRemainder Q split j) = (2^n)^7) :
    (elementaryRepresentation (p := 2)
      (remainderFrattiniAction Q split j hVj)).IsIrreducible := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hE hconj
  have hcardF := (unitary_frattini_section_card Q split J (by omega) hE hf hJ i j hVj ν hphi hcard).2
  let V := (simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
  have hnt := remainderFrattiniAction_nontrivial_of_cross_center Q split hm i j hij hVj s
    (hphi.le.trans (map_subtype_le _))
  have hnρ : ∃ g, (ρ.comp π) g ≠ 1 := by
    obtain ⟨r,hr⟩ := hnt
    obtain ⟨g,rfl⟩ := hπ r
    refine ⟨g,fun he => hr ?_⟩
    ext v
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive V) => f (Additive.ofMul v)) he)
  have hd : Module.finrank (ZMod 2) (Additive V) ≤ 6*n := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at hc
    have he : 2 ^ Module.finrank (ZMod 2) (Additive V) = 2^(6*n) := by
      rw [←hc]
      change Nat.card V = _
      rw [hcardF,←pow_mul,Nat.mul_comm n 6]
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) he).le
  exact (irreducible_comp_surjective_iff π hπ ρ).mp
    (minimal_unitary_irreducible J hn hE hconj (ρ.comp π) hnρ hd)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
