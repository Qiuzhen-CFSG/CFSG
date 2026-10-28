module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryOppositeCommutator
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Theory.SpecificGroups.SU3.EvenInvolutionResidual

/-!
# The linear radical layers in the unitary-five quadrangle

The exact mixed-root commutator makes the linear radical the join of its
two unitary roots. Each unitary root is special, including the quaternion
root at q = 2. The intervening linear root centralizes both factors.
The three-subgroups lemma then makes the whole derived subgroup central
and identifies it with the product of the two root-derived layers and
the intervening root. All three factors are elementary, of orders at most
q, q squared, and q. The radical-derived layer therefore has order at most
q to the fourth. Its equality with the intrinsic Frattini subgroup follows
by passing the two generating roots to the abelianization.

The source local marking supplies actual Hermitian coordinates on each
unitary root; it is not an identification of the full actor with PSU3.
UnitaryLinearActions uses these literal layers and their order bound to
prove both required SL2 irreducibilities. All groups lie in the same
marked quotient, and both endpoint orientations are retained.

Source: Fong--Seitz I (6A)(c), p.37; Huppert II.10.12 for the root groups.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure

private theorem derived_join_central {G : Type*} [Group G]
    (A B : Subgroup G)
    (hA : ⁅A,A⁆ ≤ centralizer (A : Set G))
    (hB : ⁅B,B⁆ ≤ centralizer (B : Set G))
    (hAB : ⁅A,B⁆ ≤ centralizer ((A ⊔ B : Subgroup G) : Set G)) :
    ⁅A ⊔ B,A ⊔ B⁆ = ⁅A,A⁆ ⊔ ⁅A,B⁆ ⊔ ⁅B,B⁆ ∧
      ⁅A ⊔ B,A ⊔ B⁆ ≤ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hABA : ⁅⁅A,B⁆,A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hAB.trans (centralizer_le (show A ≤ A ⊔ B from le_sup_left)))
  have hABB : ⁅⁅A,B⁆,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hAB.trans (centralizer_le (show B ≤ A ⊔ B from le_sup_right)))
  have hAAB : ⁅⁅A,A⁆,B⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hABA (by rwa [commutator_comm B A])
  have hBBA : ⁅⁅B,B⁆,A⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate (by rwa [commutator_comm B A]) hABB
  have hc : ⁅A,A⁆ ⊔ ⁅A,B⁆ ⊔ ⁅B,B⁆ ≤ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    refine sup_le (sup_le ?_ hAB) ?_
    · apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp hA)
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hAAB))
    · apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBBA))
        (le_centralizer_iff.mp hB)
  have hn : A ⊔ B ≤ normalizer ((⁅A,A⁆ ⊔ ⁅A,B⁆ ⊔ ⁅B,B⁆ : Subgroup G) : Set G) :=
    (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hAA : ⁅A,A⁆ ≤ ⁅A,A⁆ ⊔ ⁅A,B⁆ ⊔ ⁅B,B⁆ := le_sup_left.trans le_sup_left
  have hAB' : ⁅A,B⁆ ≤ ⁅A,A⁆ ⊔ ⁅A,B⁆ ⊔ ⁅B,B⁆ := le_sup_right.trans le_sup_left
  have hBB : ⁅B,B⁆ ≤ ⁅A,A⁆ ⊔ ⁅A,B⁆ ⊔ ⁅B,B⁆ := le_sup_right
  have he : ⁅A ⊔ B,A ⊔ B⁆ = ⁅A,A⁆ ⊔ ⁅A,B⁆ ⊔ ⁅B,B⁆ := by
    apply le_antisymm
    · apply commutator_sup_le_of_relative_normal (A ⊔ B) A B (A ⊔ B) _ hn le_sup_left le_sup_right
      · rw [commutator_comm]
        exact commutator_sup_le_of_relative_normal (A ⊔ B) A B A _ hn le_sup_left le_sup_right
          hAA (by rwa [commutator_comm])
      · rw [commutator_comm]
        exact commutator_sup_le_of_relative_normal (A ⊔ B) A B B _ hn le_sup_left le_sup_right hAB' hBB
    · exact sup_le (sup_le (commutator_mono le_sup_left le_sup_left)
        (commutator_mono le_sup_left le_sup_right)) (commutator_mono le_sup_right le_sup_right)
  exact ⟨he,he ▸ hc⟩

private theorem derived_join_elementary {G : Type*} [Group G]
    (A B : Subgroup G)
    (hA : ⁅A,A⁆ ≤ centralizer (A : Set G))
    (hB : ⁅B,B⁆ ≤ centralizer (B : Set G))
    (hAB : ⁅A,B⁆ ≤ centralizer ((A ⊔ B : Subgroup G) : Set G))
    [IsElementaryAbelian 2 (⁅A,A⁆ : Subgroup G)]
    [IsElementaryAbelian 2 (⁅B,B⁆ : Subgroup G)]
    [IsElementaryAbelian 2 (⁅A,B⁆ : Subgroup G)] :
    IsElementaryAbelian 2 (⁅A ⊔ B,A ⊔ B⁆ : Subgroup G) := by
  obtain ⟨he,hc⟩ := derived_join_central A B hA hB hAB
  have hC : ⁅A,A⁆ ⊔ ⁅A,B⁆ ⊔ ⁅B,B⁆ ≤ centralizer ((A ⊔ B : Subgroup G) : Set G) := he ▸ hc
  have hd : ⁅A,A⁆ ≤ centralizer ((⁅A,B⁆ : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left : ⁅A,A⁆ ≤ ⁅A,A⁆ ⊔ ⁅A,B⁆ ⊔ ⁅B,B⁆).trans
      (hC.trans (centralizer_le (show (⁅A,B⁆ : Subgroup G) ≤ A ⊔ B from Subgroup.commutator_le_sup _ _)))
  let : IsElementaryAbelian 2 (⁅A,A⁆ ⊔ ⁅A,B⁆ : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hd)
  rw [he]
  apply IsElementaryAbelian.sup_of_le_centralizer
  exact le_centralizer_iff.mp ((le_sup_left : ⁅A,A⁆ ⊔ ⁅A,B⁆ ≤ ⁅A,A⁆ ⊔ ⁅A,B⁆ ⊔ ⁅B,B⁆).trans
    (hC.trans (centralizer_le ((commutator_le_self B).trans le_sup_right))))

private theorem frattini_join_eq_derived {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hV : IsPGroup 2 (A ⊔ B : Subgroup G))
    (hA : frattini A = _root_.commutator A)
    (hB : frattini B = _root_.commutator B) :
    frattini (A ⊔ B : Subgroup G) = _root_.commutator (A ⊔ B : Subgroup G) := by
  let V := A ⊔ B
  let : IsMulCommutative (V ⧸ _root_.commutator V) :=
    (Normal.quotient_commutative_iff_commutator_le (N := _root_.commutator V)).mpr le_rfl
  let q := QuotientGroup.mk' (_root_.commutator V)
  let a := q.comp (inclusion (show A ≤ V from le_sup_left))
  let b := q.comp (inclusion (show B ≤ V from le_sup_right))
  have elementary_image (C : Subgroup G) (hCV : C ≤ V)
      (hC : frattini C = _root_.commutator C) :
      IsElementaryAbelian 2 (q.comp (inclusion hCV)).range := by
    let : Fact (IsPGroup 2 C) := ⟨hV.of_injective (inclusion hCV) (inclusion_injective _)⟩
    refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
    rintro ⟨x,⟨c,rfl⟩⟩
    apply Subtype.ext
    change q (inclusion hCV c)^2 = 1
    rw [←map_pow,←map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hc : c^2 ∈ _root_.commutator C := hC ▸ pth_power_mem_frattini_of_isPGroup (p := 2) c
    have hm := mem_map_of_mem (inclusion hCV) hc
    rw [map_commutator_eq] at hm
    exact commutator_mono le_top le_top hm
  let : IsElementaryAbelian 2 a.range := elementary_image A le_sup_left hA
  let : IsElementaryAbelian 2 b.range := elementary_image B le_sup_right hB
  let : IsElementaryAbelian 2 (a.range ⊔ b.range : Subgroup (V ⧸ _root_.commutator V)) :=
    IsElementaryAbelian.sup_of_le_centralizer (by intro x _; exact mem_centralizer_iff.mpr (fun y _ => mul_comm _ _))
  have htop : a.range ⊔ b.range = ⊤ := by
    rw [MonoidHom.range_comp,MonoidHom.range_comp,inclusion_range,inclusion_range,←Subgroup.map_sup]
    rw [←subgroupOf_sup (show A ≤ V from le_sup_left) (show B ≤ V from le_sup_right),subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 2 (⊤ : Subgroup (V ⧸ _root_.commutator V)) := htop ▸ inferInstance
  let : IsElementaryAbelian 2 (V ⧸ _root_.commutator V) :=
    IsElementaryAbelian.of_surjective (topEquiv (G := V ⧸ _root_.commutator V)).toMonoidHom topEquiv.surjective
  let : Fact (IsPGroup 2 V) := ⟨hV⟩
  exact le_antisymm (frattini_le_of_elementary_quotient hV _ inferInstance)
    (commutator_le_frattini_of_isPGroup (p := 2))


private theorem special_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hB : frattini B = _root_.commutator B ∧ _root_.commutator B = center B) :
    frattini A = _root_.commutator A ∧ _root_.commutator A = center A := by
  constructor
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [frattini_map_equiv,map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective]
    exact hB.1
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,center_map_equiv]
    exact hB.2

open BenderSuzuki.External BenderSuzuki.MatrixGroups BenderSuzuki.MatrixGroups.HermitianForm
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The intrinsic unitary root is special, retaining fixed-field order two. -/
theorem unitary_simpleRoot_special
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (j : Fin 2) (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    frattini (simpleRoot Q split j) = _root_.commutator (simpleRoot Q split j) ∧
      _root_.commutator (simpleRoot Q split j) = center (simpleRoot Q split j) := by
  apply special_equiv (simpleRootUnitaryEquiv J Q split hn hE hfixed hJ j hVj ν)
  let : Fact (IsPGroup 2 (hermitianUnipotentCoord J)) := ⟨BinaryRootFrattini.isTwoGroup J⟩
  have hcz := (SU3.EvenInvolutionResidual.root_structure J (2^n) hE hfixed hJ).2.2
  have hpc := BinaryRootFrattini.frattini_central J hE hfixed
  have hdp := commutator_le_frattini_of_isPGroup (p := 2) (R := hermitianUnipotentCoord J)
  exact ⟨le_antisymm (hpc.trans hcz) hdp,le_antisymm (hdp.trans hpc) hcz⟩

private theorem ambient_class_two {G : Type*} [Group G] (A : Subgroup G)
    (hA : _root_.commutator A = center A) :
    ⁅A,A⁆ ≤ centralizer (A : Set G) := by
  rw [←map_subtype_commutator,hA]
  rintro x ⟨a,ha,rfl⟩
  apply mem_centralizer_iff.mpr
  intro y hy
  exact congrArg Subtype.val (mem_center_iff.mp ha ⟨y,hy⟩)

private theorem commuting_sup_card {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hc : A ≤ centralizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B
    ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
  have hp : 0 < Nat.card (A ⊓ B : Subgroup G) := Nat.card_pos
  nlinarith

/-- The linear radical is generated by its two unitary roots. -/
theorem unitary_remainder_eq_two_roots (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hc : ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = rootAt Q split i (Q.simple j)) :
    simpleRemainder Q split i = simpleRoot Q split j ⊔ rootAt Q split j (Q.simple i) := by
  rw [remainder_eq_three_roots Q split hm i j hij,←hc]
  apply le_antisymm
  · exact sup_le (sup_le le_sup_left (Subgroup.commutator_le_sup _ _)) le_sup_right
  · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right

/-- The exact derived and Frattini layers of the U5 linear radical. -/
theorem unitary_linear_layers
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hAi : IsElementaryAbelian 2 (simpleRoot Q split i))
    (hcard : Nat.card (simpleRoot Q split i) = (2^n)^2)
    (hcomm : ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = rootAt Q split i (Q.simple j)) :
    frattini (simpleRemainder Q split i) = _root_.commutator (simpleRemainder Q split i) ∧
      ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ =
        ⁅simpleRoot Q split j,simpleRoot Q split j⁆ ⊔ rootAt Q split i (Q.simple j) ⊔
        ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i)⁆ ∧
      IsElementaryAbelian 2 (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) ∧
      Nat.card (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) ≤ (2^n)^4 := by
  let A := simpleRoot Q split j
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j)
  let eB : A ≃* B :=
    ((MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).symm.subgroupMap A).trans
      (MulEquiv.subgroupCongr (by simp only [B,rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl))
  have hA := unitary_simpleRoot_special Q split J hn hE hfixed hJ j hVj ν
  have hB := special_equiv eB.symm hA
  have hAC := adjacent_roots_commute Q split hm j i hij.symm hVj hVi
  have hCB := middle_roots_commute Q split hm i j hij hVi hVj
  have hAB : ⁅A,B⁆ ≤ centralizer ((A ⊔ B : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
    rw [hcomm]
    apply le_centralizer_iff.mpr
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hAC)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hCB))
  have hV := unitary_remainder_eq_two_roots Q split hm i j hij hcomm
  obtain ⟨hd,hcentral⟩ := derived_join_central A B (ambient_class_two A hA.2) (ambient_class_two B hB.2) hAB
  have hprod : ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ = ⁅A,A⁆ ⊔ C ⊔ ⁅B,B⁆ := by
    rw [hV,hd,hcomm]
  obtain ⟨heA,hcA,_⟩ := simpleRoot_unitary_derived J hn hE hfixed hJ Q split j hVj ν
  let := heA
  have heB : ⁅B,B⁆ = rightConjugate ⁅A,A⁆ (representative (Q.simple i) : X ⧸ Q.D) := by
    simp only [B,A,rootAt,rightConjugate,comap_equiv_eq_map_symm',map_commutator]
  let : IsElementaryAbelian 2 (⁅B,B⁆ : Subgroup (X ⧸ Q.D)) := by
    rw [heB,rightConjugate,comap_equiv_eq_map_symm']
    exact IsElementaryAbelian.map _
  let := hAi
  let : IsElementaryAbelian 2 C := by
    rw [show C = rightConjugate (simpleRoot Q split i) (representative (Q.simple j) : X ⧸ Q.D) from rfl,
      rightConjugate,comap_equiv_eq_map_symm']
    exact IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (⁅A,B⁆ : Subgroup (X ⧸ Q.D)) := hcomm.symm ▸ inferInstanceAs (IsElementaryAbelian 2 C)
  have he := derived_join_elementary A B (ambient_class_two A hA.2) (ambient_class_two B hB.2) hAB
  have htwo : IsPGroup 2 (A ⊔ B : Subgroup (X ⧸ Q.D)) := by
    rw [←hV]
    exact split.isTwo.to_le inf_le_left
  refine ⟨?_,hprod,?_,?_⟩
  · rw [hV]
    exact frattini_join_eq_derived A B htwo hA.1 hB.1
  · rw [hV]
    exact he
  · have hcB : Nat.card (⁅B,B⁆ : Subgroup (X ⧸ Q.D)) ≤ 2^n := by
      rw [heB,card_rightConjugate]
      exact hcA
    have hcC : Nat.card C = (2^n)^2 := by
      rw [show C = rightConjugate (simpleRoot Q split i) (representative (Q.simple j) : X ⧸ Q.D) from rfl,
        card_rightConjugate,hcard]
    have hsubset : ⁅A,A⁆ ⊔ C ⊔ ⁅B,B⁆ ≤ A ⊔ B := by
      rw [show C = ⁅A,B⁆ from hcomm.symm,←hd]
      exact commutator_le_self _
    have hcent : ⁅A,A⁆ ⊔ C ⊔ ⁅B,B⁆ ≤ centralizer ((A ⊔ B : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
      rw [show C = ⁅A,B⁆ from hcomm.symm,←hd]
      exact hcentral
    have h1 := commuting_sup_card ⁅A,A⁆ C
      ((le_sup_left.trans le_sup_left : ⁅A,A⁆ ≤ ⁅A,A⁆ ⊔ C ⊔ ⁅B,B⁆).trans
        (hcent.trans (centralizer_le (show C ≤ A ⊔ B from
          (le_sup_right.trans le_sup_left).trans hsubset))))
    have h2 := commuting_sup_card (⁅A,A⁆ ⊔ C) ⁅B,B⁆
      ((le_sup_left : ⁅A,A⁆ ⊔ C ≤ ⁅A,A⁆ ⊔ C ⊔ ⁅B,B⁆).trans
        (hcent.trans (centralizer_le (show (⁅B,B⁆ : Subgroup (X ⧸ Q.D)) ≤ A ⊔ B from
          le_sup_right.trans hsubset))))
    rw [hprod]
    calc
      Nat.card (⁅A,A⁆ ⊔ C ⊔ ⁅B,B⁆ : Subgroup (X ⧸ Q.D)) ≤
          (Nat.card (⁅A,A⁆ : Subgroup (X ⧸ Q.D)) * Nat.card C) * Nat.card (⁅B,B⁆ : Subgroup (X ⧸ Q.D)) :=
        h2.trans (Nat.mul_le_mul_right _ h1)
      _ ≤ (2^n * (2^n)^2) * 2^n := Nat.mul_le_mul (Nat.mul_le_mul hcA hcC.le) hcB
      _ = (2^n)^4 := by ring



end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
