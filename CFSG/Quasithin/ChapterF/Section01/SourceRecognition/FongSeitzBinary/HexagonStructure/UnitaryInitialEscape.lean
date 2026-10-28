module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryMinimumModule
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryPropagation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.DerivedCoordinates

/-!
# Initial escape and exclusion of the regular unitary pair

The actual derived radical D has its outside coordinates in the derived
subgroups of the first and last roots. If D intersect the three middle
roots were contained in Z(A₁) A₂ Z(A₃), these coordinates would bound
|D| by q^7. Parameter equality and the existing lower bound |[D,V]| >= q
then bound the literal effective section D/[D,V] by q^6.

The center of the first root lies in D, has order q, is normalized by the
full source Cartan, and survives modulo [D,V], since that denominator is
contained in the middle roots. The sharp degree-6n unitary module theorem
excludes this nonzero Cartan-invariant image. Hence the initial escape is
constructed, and its lower-central propagation contradicts nilpotence.

Every cover, quotient denominator and Cartan action is on the original
marked carrier. Both SU3/PSU3 conventions, arbitrary Hermitian forms and
both orientations are retained. The SourceQuotient application uses the
literal original marked isomorphism, with no added geometric or module
premises. Earlier HypothesisF11, marked quotient, split and rotation-six
inputs retain their source producers.

Source: Fong--Seitz I (4D), pp.21--23, and (6D), pp.42--43.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem small_cartan_image_false
    {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (j : Fin 2) {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (hroot : Nat.card (simpleRoot Q split j)=(2^n)^3)
    (d : RootSection Q split j) (hmove : d.action≠1)
    (hd : Nat.card d.EffectiveCarrier ≤ 2^(6*n))
    (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ d.numerator)
    (hcardA : Nat.card A ≤ 2^n)
    (hHA : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D)))
    (x : X ⧸ Q.D) (hx : x∈A)
    (hxn : (⟨x,hA hx⟩ : d.numerator)∉d.effectiveDenominator) : False := by
  let f : A →* d.EffectiveCarrier :=
    (QuotientGroup.mk' d.effectiveDenominator).comp (inclusion hA)
  let W : Set (Additive d.EffectiveCarrier) := Set.range (fun a : A => Additive.ofMul (f a))
  have hcW : Nat.card W ≤ 2^n := by
    apply le_trans _ hcardA
    exact Nat.card_le_card_of_surjective
      (fun a : A => (⟨Additive.ofMul (f a),a,rfl⟩ : W)) (by
        rintro ⟨w,a,rfl⟩
        exact ⟨a,rfl⟩)
  let v : Additive d.EffectiveCarrier := Additive.ofMul (f ⟨x,hx⟩)
  have hv : v≠0 := by
    intro he
    apply hxn
    apply (QuotientGroup.eq_one_iff _).mp
    exact Additive.ofMul.injective he
  apply unitary_effective_section_small_cartan_subset_false J hJ Q split j hn hcard hconj
    σ hσ hK hroot d hmove hd W hcW v hv ⟨⟨x,hx⟩,rfl⟩
  intro r hr w hw
  obtain ⟨a,rfl⟩:=hw
  let a' : A := ⟨(r : X ⧸ Q.D)*a*(r : X ⧸ Q.D)⁻¹,
    (mem_normalizer_iff.mp (hHA hr) _).mp a.property⟩
  refine ⟨a',?_⟩
  change Additive.ofMul (QuotientGroup.mk ((inclusion hA) a')) =
    d.effectiveRepresentation r (Additive.ofMul (QuotientGroup.mk ((inclusion hA) a)))
  rw [RootSection.effectiveRepresentation_mk]
  rfl


open MarkedLocal
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
  {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
  (hconj : ∀ x, J.conj x=x^(2^n))

include e h split hn hcard hconj in
private theorem unitary_seed_inputs (j : Fin 2)
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
      Nat.card (simpleRoot Q split j) = (2^n)^3 := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · exact ⟨projectiveUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ,
      projectiveUnitary_simpleRoot_card Q e h split j T hT J (by omega) hcard hconj μ⟩
  · exact ⟨specialUnitary_remainder_le_kernel Q e h split j T hT J hn hcard hconj μ,
      specialUnitary_simpleRoot_card Q e h split j T hT J (by omega) hcard hconj μ⟩

variable {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
  {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
  (hconjE : ∀ x, I.conj x=x^(2^m))

include e h split hn hcard hconj hm hE hconjE in
private theorem original_unitary_pair_excluded_of_derived_card_le
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hDcard : Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
      Subgroup (X ⧸ Q.D)) ≤ 2^(7*n)) : False := by
  have hmn := original_unitary_pair_parameters_eq Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj
  have hKi := (unitary_seed_inputs Q split e h I hm hE hconjE i hi).1
  have hrootj := (unitary_seed_inputs Q split e h J hn hcard hconj j hj).2
  obtain ⟨hKj,hel,hden,heff,hmove,hbound⟩ := original_unitary_pair_derivedCentral_section
    Q e h split J hn hcard hconj I hm hE hconjE hhex i j hij hi hj
  let d := derivedCentralSection Q split j hKj
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  let T := ⁅D,V⁆
  have hTcard : 2^n ≤ Nat.card T := by
    have hh := (original_unitary_pair_cartan_lower_bounds Q e h split J hn hcard hconj
      I hm hE hconjE hhex i j hij hmn.le hi hj).1
    rwa [hmn] at hh
  have heD : d.effectiveDenominator=d.denominator := hden
  have hdenCard : Nat.card d.effectiveDenominator=Nat.card T := by
    rw [heD]
    exact Nat.card_congr (subgroupOfEquivOfLe (radical_triple_le_derived Q split j)).toEquiv
  have hd : Nat.card d.EffectiveCarrier ≤ 2^(6*n) := by
    have hp := d.effectiveDenominator.index_mul_card
    change Nat.card d.EffectiveCarrier * Nat.card d.effectiveDenominator = Nat.card D at hp
    rw [hdenCard] at hp
    have hh := (Nat.mul_le_mul_left (Nat.card d.EffectiveCarrier) hTcard).trans
      (le_of_eq hp |>.trans hDcard)
    rw [show 7*n=6*n+n by omega,pow_add] at hh
    exact Nat.le_of_mul_le_mul_right hh (Nat.pow_pos (by decide : 0<(2:ℕ)))
  let A := simpleRoot Q split i
  let Z := (center A).map A.subtype
  have hz := original_unitary_root_center_eq_commutator Q e h split I hm hE hconjE i hi
  have hclass := original_unitary_root_classTwo Q e h split I hm hE hconjE i hi
  have hZD : Z ≤ d.numerator := by
    change (center A).map A.subtype ≤ D
    rw [hz,map_subtype_commutator]
    exact commutator_mono (simpleRoot_le_other_remainder Q split hhex i j hij)
      (simpleRoot_le_other_remainder Q split hhex i j hij)
  have hZcard : Nat.card Z ≤ 2^n := by
    rw [show Nat.card Z=Nat.card (center A) from card_map_of_injective A.subtype_injective]
    have hh := original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i 1 hi
    have hc := hh.1 ▸ hh.2.1
    rw [rootAt_one,hmn] at hc
    exact hc.le
  have hZH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (Z : Set (X ⧸ Q.D)) :=
    (torus_normalizes_simpleRoot Q split i).trans
      (normalizer_le_normalizer_characteristic_image A (center A))
  have hZne : Z≠⊥ := by
    change (center A).map A.subtype≠⊥
    rw [hz,map_subtype_commutator]
    exact hclass.2
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have ha0 : (a : X ⧸ Q.D)≠1 := fun he => ha (Subtype.ext he)
  have han : (⟨a,hZD a.property⟩ : d.numerator)∉d.effectiveDenominator := by
    intro he
    rw [heD] at he
    have hT : (a : X ⧸ Q.D)∈T := he
    have hVi := middleRoots_le_other_remainder Q split hhex i j hij
      (radical_triple_le_middle Q split hhex i j hij hKi hclass.1 hT)
    have hAi : (a : X ⧸ Q.D)∈A := by
      obtain ⟨z,_,hez⟩ := a.property
      exact hez ▸ z.property
    exact ha0 (mem_bot.mp ((disjoint_iff.mp (simpleRoot_disjoint_remainder Q split i)).le
      ⟨hAi,hVi⟩))
  obtain ⟨_,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J (by omega) hcard hconj
    j hKj hj.symm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let : Algebra (ZMod 2) F := ZMod.algebra _ _
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨C,hC⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis
    J (2^n) hcard hf
  let μ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC
  exact small_cartan_image_false Q split J₀ rfl j hn hcard hconj
    (σ.comp μ.symm.toMonoidHom) (hσ.comp μ.symm.surjective) hKj hrootj d hmove hd
    Z hZD hZcard hZH a a.property han


include e h split hn hcard hconj hm hE hconjE in
private theorem original_unitary_pair_derived_card_le_of_no_escape
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hproj : ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
        Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) ⊆
      ((⁅simpleRoot Q split i,simpleRoot Q split i⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) *
      (middleRoots Q split i j : Set (X ⧸ Q.D)) *
      ((⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j)⁆ :
        Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)))
    (hesc : ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ⊓
      middleRoots Q split i j : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) ⊆
        middleCentralProduct Q split i j) :
    Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
      Subgroup (X ⧸ Q.D)) ≤ 2^(7*n) := by
  have hmn := original_unitary_pair_parameters_eq Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  let A := simpleRoot Q split i
  let E₀ := rootAt Q split i (Q.simple j)
  let B := ⁅A,A⁆
  let C := middleCentralProduct Q split i j
  let K := ⁅E₀,E₀⁆
  have hAV : A≤V := simpleRoot_le_other_remainder Q split hhex i j hij
  have hEV : E₀≤V := (exchanged_roots_le_remainder Q split hhex i j hij).1
  have hBD : B≤D := commutator_mono hAV hAV
  have hKD : K≤D := commutator_mono hEV hEV
  have hcover : (D : Set (X ⧸ Q.D)) ⊆ (B : Set (X ⧸ Q.D))*C*(K : Set (X ⧸ Q.D)) := by
    intro x hx
    obtain ⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,he⟩ := hproj hx
    rw [←he] at hx
    have hbD : b∈D := by
      have hh := D.mul_mem (D.mul_mem (D.inv_mem (hBD ha)) hx) (D.inv_mem (hKD hc))
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh
    exact ⟨a*b,⟨a,ha,b,hesc ⟨hbD,hb⟩,rfl⟩,c,hc,he⟩
  have hBcard : Nat.card B ≤ 2^n := by
    let : Fact (IsPGroup 2 A) := ⟨split.isTwo.to_le (simpleRoot_le Q split i)⟩
    change Nat.card (⁅A,A⁆ : Subgroup (X ⧸ Q.D)) ≤ _
    rw [←map_subtype_commutator,card_map_of_injective A.subtype_injective]
    have hc := (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i 1 hi).2.1
    rw [rootAt_one,hmn] at hc
    exact (card_le_of_le (show _root_.commutator A ≤ frattini A from commutator_le_frattini_of_isPGroup (p:=2))).trans_eq hc
  have hKcard : Nat.card K ≤ 2^n := by
    let : Fact (IsPGroup 2 E₀) := ⟨split.isTwo.to_le (hEV.trans inf_le_left)⟩
    change Nat.card (⁅E₀,E₀⁆ : Subgroup (X ⧸ Q.D)) ≤ _
    rw [←map_subtype_commutator,card_map_of_injective E₀.subtype_injective]
    have hc := (original_unitary_root_cartan_constituents Q e h split I hm hE hconjE i
      (Q.simple j) hi).2.1
    rw [hmn] at hc
    exact (card_le_of_le (show _root_.commutator E₀ ≤ frattini E₀ from commutator_le_frattini_of_isPGroup (p:=2))).trans_eq hc
  have hCcard := original_unitary_pair_centralProduct_card_bound Q e h split J hn hcard hconj
    I hm hE hconjE hhex i j hij hi hj
  have h1 := Set.natCard_mul_le (s:=(B : Set (X ⧸ Q.D))) (t:=C)
  have h2 := Set.natCard_mul_le (s:=(B : Set (X ⧸ Q.D))*C) (t:=(K : Set (X ⧸ Q.D)))
  calc
    Nat.card D ≤ Nat.card ((B : Set (X ⧸ Q.D))*C*(K : Set (X ⧸ Q.D))) :=
      Nat.card_le_card_of_injective (Set.inclusion hcover) (Set.inclusion_injective hcover)
    _ ≤ Nat.card B * Nat.card C * Nat.card K := h2.trans (Nat.mul_le_mul_right _ h1)
    _ ≤ 2^n*2^(5*n)*2^n := Nat.mul_le_mul (Nat.mul_le_mul hBcard hCcard) hKcard
    _ = 2^(7*n) := by rw [←pow_add,←pow_add]; congr 1; omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
  (hconj : ∀ x, J.conj x=x^(2^n))
  {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
  {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
  (hconjE : ∀ x, I.conj x=x^(2^m))

include e h split hn hcard hconj hm hE hconjE in
/-- The actual derived subgroup escapes the central middle-root product.
If escape failed, its outside derived coordinates would force order at most
q^7. The literal section D/[D,V] would then have degree at most 6n while
containing a nonzero Cartan-invariant root-center image of order at most q,
contradicting the sharp natural-module torus obstruction. -/
theorem original_unitary_pair_initial_escape
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ¬ ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ⊓
      middleRoots Q split i j : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) ⊆
        middleCentralProduct Q split i j := by
  intro hesc
  have hKi := (unitary_seed_inputs Q split e h I hm hE hconjE i hi).1
  have hKj := (unitary_seed_inputs Q split e h J hn hcard hconj j hj).1
  have hd := original_unitary_pair_derived_card_le_of_no_escape Q split e h
    J hn hcard hconj I hm hE hconjE hhex i j hij hi hj
    (radical_derived_coordinates Q split hhex i j hij hKi hKj) hesc
  exact original_unitary_pair_excluded_of_derived_card_le Q split e h
    J hn hcard hconj I hm hE hconjE hhex i j hij hi hj hd

include e h split hn hcard hconj hm hE hconjE in
/-- Both original regular unitary factors are impossible in a hexagon.
The constructed initial escape feeds the proved lower-central propagation;
all parameters, scalar conventions and original markings are retained. -/
theorem original_unitary_pair_excluded
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False :=
  original_unitary_pair_excluded_of_escape Q e h split J hn hcard hconj I hm hE hconjE
    hhex i j hij hi hj
    (original_unitary_pair_initial_escape Q e h split J hn hcard hconj I hm hE hconjE
      hhex i j hij hi hj)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The regular-unitary pair is excluded on the literal original source
quotient, using its full original marked amalgam. -/
theorem quotient_unitary_pair_excluded
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    {m : ℕ} (hm : 2 ≤ m) (hE : Nat.card E = (2^m)^2)
    (hconjE : ∀ x, I.conj x=x^(2^m))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False :=
  original_unitary_pair_excluded Q (originalMarkedIso Q) h split
    J hn hcard hconj I hm hE hconjE hhex i j hij hi hj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
