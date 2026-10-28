module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.SmallUnitaryDegree
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.SectionFaithfulness
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitarySection

/-!
# The unitary quadrangle Frattini layer from its actual cover

The center of a crossed SU3 root has order q and is its derived subgroup,
including the quaternion root at q = 2. It lies in the derived subgroup of
the same complementary radical, hence in its Frattini subgroup. Local
characteristic two makes the root actor faithful on the Frattini quotient.
The actual SU3 cover then forces binary degree at least 6n. At q = 2 the
possible scalar kernel is excluded by the projective degree-eight bound;
the order-216 special actor forces degree six without perfectness.

A radical of order q^7 therefore has Frattini subgroup of order at most q.
The two bounds identify both its Frattini and derived subgroups with the
crossed-root center. Irreducibility of the Frattini action then puts the radical center in
this same layer: a central Frattini supplement would make it abelian.
No specialness of the original core is assumed.
The source adapter constructs the cover from the original factor quotient
and obtains this radical order from the actual two panel parameters.

Source: Fong--Seitz I (4D), (6A)(c), pp.21--23,37--38;
DGS (11.8)(a,c,d,f), pp.175--176. The marked split quotient, rotation four,
local regularity and actual unitary cover remain the stated inputs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem unitary_cross_root_special
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (j : Fin 2) (w : Weyl Q)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    _root_.commutator (rootAt Q split j w) = center (rootAt Q split j w) := by
  let a : simpleRoot Q split j ≃* rootAt Q split j w :=
    ((MulAut.conj (representative w : X ⧸ Q.D)).symm.subgroupMap _).trans
      (MulEquiv.subgroupCongr (by
        simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl))
  have he := congrArg (Subgroup.map a.toMonoidHom)
    (unitary_simpleRoot_special Q split J hn hE hfixed hJ j hVj ν).2
  rwa [map_commutator_eq,MonoidHom.range_eq_top.mpr a.surjective,
    ←_root_.commutator_def,center_map_equiv] at he

/-- The actual unitary root and the faithful Frattini action determine both
layers without a special-radical hypothesis. -/
theorem unitary_frattini_eq_cross_center_of_cover
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple j}) :
      Set (Q.tits.standardParabolic {Q.simple j})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple j}))
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
    (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
    (hcard : Nat.card (simpleRemainder Q split j) = (2^n)^7) :
    (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype ∧
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype := by
  let V := simpleRemainder Q split j
  let C := rootAt Q split j (Q.simple i)
  let Z := (center C).map C.subtype
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hE hconj
  have hspecial : _root_.commutator C = center C :=
    unitary_cross_root_special Q split J hn hE hfixed hJ j (Q.simple i) hVj ν
  have hCV : C ≤ V := cross_root_le_own_remainder Q split hm j i hij.symm
  have hZD : Z ≤ ⁅V,V⁆ := by
    rw [show Z = (center C).map C.subtype from rfl,←hspecial,map_subtype_commutator]
    exact commutator_mono hCV hCV
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hDΦ : ⁅V,V⁆ ≤ (frattini V).map V.subtype := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hZΦ := hZD.trans hDΦ
  have hZcard : Nat.card Z = 2^n := by
    rw [show Z = (center C).map C.subtype from rfl,card_map_of_injective C.subtype_injective]
    exact unitary_cross_center_card Q split J hn hE hfixed hJ j (Q.simple i) hVj ν
  let W := V ⧸ frattini V
  let : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply remainderFrattiniAction_injective Q split j s hVj hc
    ext v
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive W) => f (Additive.ofMul v)) hab)
  let σ := ρ.comp π
  have hσker : σ.ker ≤ J.specialToProjective.ker := by
    intro a ha
    have he : π a = 1 := hρ (ha.trans ρ.map_one.symm)
    rw [MonoidHom.mem_ker,←hπν,he,map_one,map_one]
  have hdcard : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    change Nat.card (Additive W) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W))
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini V)
  have hWupper : Nat.card W ≤ (2^n)^7 :=
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (frattini V))).trans_eq hcard
  have hdim : 6*n ≤ Module.finrank (ZMod 2) (Additive W) := by
    by_cases hn2 : 2 ≤ n
    · have hnt : ∃ a, σ a ≠ 1 := by
        obtain ⟨r,hr,hr1⟩ := (simpleRoot Q split j).bot_or_exists_ne_one.resolve_left
          (simpleRoot_ne_bot Q split j)
        let r' : rankOne Q split j := ⟨r,(show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left) hr⟩
        obtain ⟨a,ha⟩ := hπ r'
        refine ⟨a,fun he => hr1 ?_⟩
        have he' : ρ r' = 1 := by simpa only [σ,MonoidHom.comp_apply,ha] using he
        exact congrArg Subtype.val (hρ (he'.trans ρ.map_one.symm))
      exact Representation.SU3.BinaryDegree.finrank_ge J hn2 hE hconj σ hnt
    · have hn1 : n = 1 := by omega
      subst n
      have hd : Module.finrank (ZMod 2) (Additive W) < 8 := by
        have hh : 2 ^ Module.finrank (ZMod 2) (Additive W) ≤ 2^7 := by
          simpa only [hdcard,pow_one] using hWupper
        have := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hh
        omega
      have hσ := small_unitary_faithful_of_scalar_kernel J (by simpa using hE)
        (by simpa using hconj) hJ σ hσker hd
      simpa only [mul_one] using small_special_unitary_faithful_degree J
        (by simpa using hE) (by simpa using hconj) hJ σ hσ
  have hWlower : (2^n)^6 ≤ Nat.card W := by
    rw [hdcard,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hΦupper : Nat.card (frattini V) ≤ 2^n := by
    have hp : 0 < (2^n)^6 := pow_pos (pow_pos (by decide) n) 6
    have he : (2^n)^7 = Nat.card W * Nat.card (frattini V) := hcard.symm.trans hprod
    have hh : (2^n)^6 * Nat.card (frattini V) ≤ (2^n)^6 * 2^n := by
      calc
        _ ≤ Nat.card W * Nat.card (frattini V) := Nat.mul_le_mul_right _ hWlower
        _ = (2^n)^7 := he.symm
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hh hp
  have hΦ : (frattini V).map V.subtype = Z := (eq_of_le_of_card_ge hZΦ (by
    rw [card_map_of_injective V.subtype_injective,hZcard]
    exact hΦupper)).symm
  exact ⟨hΦ,le_antisymm (hDΦ.trans hΦ.le) hZD⟩


/-- Irreducibility of the radical Frattini action puts its center in the
Frattini subgroup unless the radical is abelian. -/
theorem remainder_center_le_frattini_of_irreducible
    (j : Fin 2) (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hirr : (elementaryRepresentation (p := 2)
      (remainderFrattiniAction Q split j hVj)).IsIrreducible)
    (hne : _root_.commutator (simpleRemainder Q split j) ≠ ⊥) :
    center (simpleRemainder Q split j) ≤ frattini (simpleRemainder Q split j) := by
  let V := simpleRemainder Q split j
  let W := V ⧸ frattini V
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
  let := hirr
  let q := QuotientGroup.mk' (frattini V)
  let Z := (center V).map q
  let ψ : Subgroup W ≃o Submodule (ZMod 2) (Additive W) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  let A : Subrepresentation ρ := ⟨ψ Z,by
    intro r v hv
    change v.toMul ∈ Z at hv
    change remainderFrattiniAction Q split j hVj r v.toMul ∈ Z
    obtain ⟨z,hz,hzv⟩ := hv
    rw [←hzv,remainderFrattiniAction_mk]
    exact mem_map_of_mem q
      (MulEquivClass.apply_mem_center (remainderRankOneAction Q split j hVj r) hz)⟩
  rcases eq_bot_or_eq_top A with hb | ht
  · intro z hz
    have hmem : Additive.ofMul (q z) ∈ A := mem_map_of_mem q hz
    rw [hb] at hmem
    have he : q z = 1 := Additive.ofMul.injective hmem
    exact (QuotientGroup.eq_one_iff z).mp he
  · have hZ : Z = ⊤ := by
      apply top_unique
      intro w _
      have hw : Additive.ofMul w ∈ A := ht ▸ (show Additive.ofMul w ∈ (⊤ : Subrepresentation ρ) from trivial)
      exact hw
    have he := congrArg (Subgroup.comap q) hZ
    have hsup : center V ⊔ frattini V = ⊤ := by
      simpa only [Z,q,comap_map_eq,QuotientGroup.ker_mk',comap_top] using he
    have hcent : center V = ⊤ := frattini_nongenerating hsup
    exact (hne ((commutator_eq_bot_iff_center_eq_top V).mpr hcent)).elim

/-- The center of the intervening root is central in the whole radical. -/
theorem cross_center_le_remainder_center
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j) :
    (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype ≤
      (center (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype := by
  let V := simpleRemainder Q split j
  let C := rootAt Q split j (Q.simple i)
  have hCV : C ≤ V := cross_root_le_own_remainder Q split hm j i hij.symm
  rintro x ⟨c,hc,rfl⟩
  have hcen : V ≤ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) := by
    dsimp only [V]
    rw [remainder_eq_three_roots Q split hm j i hij.symm]
    apply sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      apply mem_centralizer_singleton_iff.mpr
      exact (mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp
          (adjacent_roots_commute Q split hm i j hij hVi hVj) ha) c c.property).symm
    · intro a ha
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_center_iff.mp hc ⟨a,ha⟩)
    · intro a ha
      apply mem_centralizer_singleton_iff.mpr
      exact (mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp
          (middle_roots_commute Q split hm i j hij hVi hVj) ha) c c.property).symm
  refine ⟨⟨c,hCV c.property⟩,mem_center_iff.mpr (fun v => ?_),rfl⟩
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (hcen v.property))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
