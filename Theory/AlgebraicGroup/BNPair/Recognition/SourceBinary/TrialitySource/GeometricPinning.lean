module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanBraid
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.Generation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.OrthogonalPinning

/-!
# Triality pinnings and braid from the actual source geometry

Use the whole rank-one comparisons separately over the cubic field and its
actual fixed subfield. Align their Weyl matrices with specified reflections
inside the same canonical rank-one subgroups. The exchanged-root commutation
in 6E(b) gives both orthogonal centralizers. An element of the intersection
of the two rank-one Cartans is inverted by both reflections; transporting
its centralization back to a simple root makes it trivial. The sixth power
of the product of the reflections lies in the odd full Cartan and is inverted
by both reflections, so it lies in this trivial intersection.

Thus the constructed maps satisfy the braid and orthogonal actions needed
by RankOnePair, with the literal Weyl placements and simple-root ranges.
Both coroots lie in the full source Cartan. No perfectness or lower bound
excluding the fields of order two or four is used. The local PSL₂ comparisons
and radical-to-panel-kernel inclusions are earlier structural inputs;
compatibility of the two scalar labelings with the mixed module equations
remains a separate source obligation.

Source: Fong--Seitz I (5C), (6E)(b), printed pp.25--26,43; II §7 and
(9.25), printed pp.192,218. The odd-Cartan braid argument extends the
field-independent geometry used in GTwoSource.CartanBraid to unequal fields.
GeometricApplication supplies the literal original/geometric consumers.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open RootCoordinates HexagonStructure GTwoSource
namespace GeometricPinning
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem simple_square (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem commutator_right_bot {A B : Subgroup (X ⧸ Q.D)}
    (h : ⁅A,B⁆ = ⊥) (g : X ⧸ Q.D) :
    ⁅rightConjugate A g,rightConjugate B g⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  apply (MulAut.conj g).injective
  exact (map_mul (MulAut.conj g) y x).trans
    ((mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp h) hx) _ hy).trans
      (map_mul (MulAut.conj g) x y).symm)

/-- The exchanged-root clause of 6E(b) makes the whole opposite rank-one
factor centralize the orthogonal root. No field coordinates are used. -/
theorem rankOne_centralizes_tail (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (ni : RootReflection Q split i) (nj : RootReflection Q split j)
    (hc : ⁅rootAt Q split i (Q.simple j),rootAt Q split j (Q.simple i)⁆ = ⊥) :
    rankOne Q split j ≤ centralizer
      (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) := by
  apply rankOne_centralizes_orthogonal_of_simple Q split hm i j hij nj
  have he := commutator_right_bot Q hc (ni.val : X ⧸ Q.D)
  rw [rootAt_right Q split i _ _ ni.val ni.class_eq,
    rootAt_right Q split j _ _ ni.val ni.class_eq, simple_square, rootAt_one,
    commutator_comm] at he
  exact commutator_eq_bot_iff_le_centralizer.mp he

private theorem centralizes_right_of_inverted {A : Subgroup (X ⧸ Q.D)}
    {z g : X ⧸ Q.D} (hc : z ∈ centralizer (A : Set (X ⧸ Q.D)))
    (hi : MulAut.conj g z = z⁻¹) :
    z ∈ centralizer (rightConjugate A g : Set (X ⧸ Q.D)) := by
  apply mem_centralizer_iff.mpr
  intro x hx
  have hh : Commute (MulAut.conj g x) z := mem_centralizer_iff.mp hc _ hx
  apply (MulAut.conj g).injective
  simpa only [map_mul, hi] using hh.inv_right.eq

section Endpoint
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,F)) (ni : RootReflection Q split i)

include hV μ ni in
private theorem cartan_faithful {z : X ⧸ Q.D}
    (hzH : z ∈ Q.tits.B ⊓ Q.tits.N) (hzR : z ∈ rankOne Q split i)
    (hc : z ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D))) : z = 1 := by
  obtain ⟨a,rfl⟩ := exists_alignedTorus_of_mem Q split i hV μ ni hzH hzR
  have hx : alignedSimpleParameter Q split i hV μ ni (.ofAdd 1) ∈ simpleRoot Q split i := by
    rw [← alignedSimpleParameter_range Q split i hV μ ni]
    exact ⟨_,rfl⟩
  have he := alignedTorus_root Q split i hV μ ni a 1
  rw [← mem_centralizer_iff.mp hc _ hx, mul_assoc, mul_inv_cancel, mul_one] at he
  have haa : (a : F)^2 = 1 := by
    have hh := Multiplicative.ofAdd.injective
      (alignedSimpleParameter_injective Q split i hV μ ni he)
    simpa only [mul_one] using hh.symm
  have ha : a = 1 := Units.ext (CharTwo.sq_injective (haa.trans (one_pow 2).symm))
  change alignedTorusHom Q split i hV μ ni a = 1
  rw [ha,map_one]

include hV μ in
private theorem cartan_inverted {z : X ⧸ Q.D}
    (hzH : z ∈ Q.tits.B ⊓ Q.tits.N) (hzR : z ∈ rankOne Q split i) :
    MulAut.conj (ni.val : X ⧸ Q.D) z = z⁻¹ := by
  obtain ⟨a,rfl⟩ := exists_alignedTorus_of_mem Q split i hV μ ni hzH hzR
  change (ni.val : X ⧸ Q.D)*_*(ni.val : X ⧸ Q.D)⁻¹ = _
  rw [reflection_alignedTorus]
  exact (alignedTorusHom Q split i hV μ ni).map_inv a
end Endpoint

variable {F E : Type*} [Field F] [Finite F] [CharP F 2]
  [Field E] [Finite E] [CharP E 2]
  (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (μi : localGroup Q split i ≃* PSL(2,F))
  (μj : localGroup Q split j ≃* PSL(2,E))
  (ni : RootReflection Q split i) (nj : RootReflection Q split j)

include hij hVi hVj μi μj ni nj in
/-- The two actual rank-one Cartans are disjoint, also when their fields differ. -/
theorem cartan_disjoint (hm : rotationOrder Q = 6)
    (hc : ⁅rootAt Q split i (Q.simple j),rootAt Q split j (Q.simple i)⁆ = ⊥) :
    Disjoint ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i)
      ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split j) := by
  apply disjoint_def.mpr
  intro z hzi hzj
  have hi := cartan_inverted Q split i hVi μi ni hzi.1 hzi.2
  have hj := cartan_inverted Q split j hVj μj nj hzj.1 hzj.2
  have hD := rankOne_centralizes_tail Q split hm i j hij ni nj hc hzj.2
  have hC := centralizes_right_of_inverted Q hD hi
  rw [rootAt_right Q split i _ _ ni.val ni.class_eq,
    mul_assoc, simple_square, mul_one] at hC
  have hA := centralizes_right_of_inverted Q hC hj
  rw [rootAt_right Q split i _ _ nj.val nj.class_eq, simple_square, rootAt_one] at hA
  exact cartan_faithful Q split i hVi μi ni hzi.1 hzi.2 hA

private theorem involutions_invert_product_powers {Y : Type*} [Group Y] {r s : Y}
    (hr : r^2 = 1) (hs : s^2 = 1) (k : ℕ) :
    MulAut.conj r ((r*s)^k) = ((r*s)^k)⁻¹ ∧
      MulAut.conj s ((r*s)^k) = ((r*s)^k)⁻¹ := by
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hr)
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  have hR : MulAut.conj r (r*s) = (r*s)⁻¹ := by
    change r*(r*s)*r⁻¹ = _
    rw [← mul_assoc r r s, ← pow_two, hr, one_mul, mul_inv_rev, hs']
  have hS : MulAut.conj s (r*s) = (r*s)⁻¹ := by
    change s*(r*s)*s⁻¹ = _
    rw [← mul_assoc s r s, mul_assoc (s*r), mul_inv_cancel, mul_one, mul_inv_rev, hr', hs']
  constructor
  · rw [map_pow,hR,inv_pow]
  · rw [map_pow,hS,inv_pow]

include hij hVi hVj μi μj in
/-- The actual source lifts satisfy the length-six braid over unequal fields.
The proof uses the odd full Cartan and its two disjoint rank-one factors. -/
theorem reflections_braid (hm : rotationOrder Q = 6)
    (hc : ⁅rootAt Q split i (Q.simple j),rootAt Q split j (Q.simple i)⁆ = ⊥) :
    ((ni.val : X ⧸ Q.D) * nj.val)^6 = 1 := by
  let z : Q.tits.N := (ni.val*nj.val)^6
  have hz : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) z = 1 := by
    simp only [z,map_pow,map_mul,ni.class_eq,nj.class_eq]
    have he : orderOf (Q.simple i*Q.simple j) = 6 := by
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hm
      · exact (SemiconjBy.orderOf_eq (Q.simple 0) (show
          SemiconjBy (Q.simple 0) (Q.simple 1*Q.simple 0) (Q.simple 0*Q.simple 1) from
            (mul_assoc _ _ _).symm)).trans hm
      · exact (hij rfl).elim
    rw [← he]
    exact pow_orderOf_eq_one _
  have hmem : (z : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N := (QuotientGroup.eq_one_iff z).mp hz
  have hi : (ni.val : X ⧸ Q.D)^2 = 1 := by
    simpa only [pow_two] using sourceReflection_sq Q split i hVi μi ni
  have hj : (nj.val : X ⧸ Q.D)^2 = 1 := by
    simpa only [pow_two] using sourceReflection_sq Q split j hVj μj nj
  obtain ⟨hiz,hjz⟩ := involutions_invert_product_powers hi hj 6
  exact disjoint_def.mp (cartan_disjoint Q split i j hij hVi hVj μi μj ni nj hm hc)
    ⟨hmem,cartan_inverted_mem_rankOne Q split i ni hmem hiz⟩
    ⟨hmem,cartan_inverted_mem_rankOne Q split j nj hmem hjz⟩


private theorem conj_root_mem (k l : Fin 2) (v : Weyl Q)
    (nl : RootReflection Q split l) (hsq : (nl.val : X ⧸ Q.D) * nl.val = 1)
    {x : X ⧸ Q.D} (hx : x ∈ rootAt Q split k v) :
    MulAut.conj (nl.val : X ⧸ Q.D) x ∈ rootAt Q split k (v*Q.simple l) := by
  rw [← rootAt_right Q split k v _ nl.val nl.class_eq]
  change (nl.val : X ⧸ Q.D)*((nl.val : X ⧸ Q.D)*x*(nl.val : X ⧸ Q.D)⁻¹)*
    (nl.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split k v
  have hi : (nl.val : X ⧸ Q.D)⁻¹ = nl.val := inv_eq_of_mul_eq_one_right hsq
  rw [hi]
  have he : (nl.val : X ⧸ Q.D)*((nl.val : X ⧸ Q.D)*x*(nl.val : X ⧸ Q.D))*
      (nl.val : X ⧸ Q.D) = x := by
    calc
      _ = ((nl.val : X ⧸ Q.D)*nl.val)*x*((nl.val : X ⧸ Q.D)*nl.val) := by group
      _ = x := by rw [hsq, one_mul, mul_one]
  rwa [he]

include hVj μj in
private theorem tail_mem (a : F) :
    MulAut.conj (ni.val : X ⧸ Q.D) (MulAut.conj (nj.val : X ⧸ Q.D)
      (alignedPinningHom Q split i hVi μi ni (uni a))) ∈
      rootAt Q split i (Q.simple j*Q.simple i) := by
  apply conj_root_mem Q split i i (Q.simple j) ni (sourceReflection_sq Q split i hVi μi ni)
  have ha : alignedPinningHom Q split i hVi μi ni (uni a) ∈ rootAt Q split i 1 := by
    rw [rootAt_one, ← alignedSimpleParameter_range Q split i hVi μi ni]
    exact ⟨.ofAdd a,rfl⟩
  simpa only [one_mul] using conj_root_mem Q split i j 1 nj
    (sourceReflection_sq Q split j hVj μj nj) ha

end GeometricPinning

namespace GeometricPinning
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : F ≃+* F) (indices : Fin 2 ≃ Fin 2)
local notation "K" => Triality.Standard.RootPresentationRecognition.ScalarMarking.SourceFixed (σ := σ)
variable
  (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
  (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
  (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
  (μj : localGroup Q split (indices 1) ≃*
    PSL(2, Triality.Standard.RootPresentationRecognition.ScalarMarking.SourceFixed (σ := σ)))
  (ni : RootReflection Q split (indices 0)) (nj : RootReflection Q split (indices 1))
  (hm : rotationOrder Q = 6)
  (hc : ⁅rootAt Q split (indices 0) (Q.simple (indices 1)),
    rootAt Q split (indices 1) (Q.simple (indices 0))⁆ = ⊥)

/-- Construct both whole pinnings, their braid and orthogonal actions from
local PSL₂ identifications and the exchanged-root assertion of 6E(b).
Scalar compatibility of the mixed module equations is still a separate step. -/
def pair : RankOnePair σ (X ⧸ Q.D) where
  shortMap := alignedPinningHom (F := F) Q split (indices 0) hVi μi ni
  longMap := alignedPinningHom (F := K) Q split (indices 1) hVj μj nj
  braid := by
    change (alignedPinningHom Q split (indices 0) hVi μi ni (weyl F) *
      alignedPinningHom Q split (indices 1) hVj μj nj (weyl K))^6 = 1
    rw [alignedPinningHom_weyl, alignedPinningHom_weyl]
    exact reflections_braid Q split (indices 0) (indices 1)
      (indices.injective.ne (by decide)) hVi hVj μi μj ni nj hm hc
  orthogonalShort a := by
    simp only [alignedPinningHom_weyl]
    have hcent := rankOne_centralizes_tail Q split hm (indices 0) (indices 1)
      (indices.injective.ne (by decide)) ni nj hc nj.mem_rankOne
    have ht := tail_mem Q split (indices 0) (indices 1) hVi hVj μi μj ni nj a
    change (nj.val : X ⧸ Q.D)*_*(nj.val : X ⧸ Q.D)⁻¹ = _
    rw [← mem_centralizer_iff.mp hcent _ ht, mul_assoc, mul_inv_cancel, mul_one]
  orthogonalLong a := by
    simp only [alignedPinningHom_weyl]
    have hc' : ⁅rootAt Q split (indices 1) (Q.simple (indices 0)),
        rootAt Q split (indices 0) (Q.simple (indices 1))⁆ = ⊥ := by
      rwa [commutator_comm]
    have hcent := rankOne_centralizes_tail Q split hm (indices 1) (indices 0)
      (indices.injective.ne (by decide)) nj ni hc' ni.mem_rankOne
    have ht := tail_mem Q split (indices 1) (indices 0) hVj hVi μj μi nj ni a
    change (ni.val : X ⧸ Q.D)*_*(ni.val : X ⧸ Q.D)⁻¹ = _
    rw [← mem_centralizer_iff.mp hcent _ ht, mul_assoc, mul_inv_cancel, mul_one]

local notation "p" => pair Q split σ indices hVi hVj μi μj ni nj hm hc

/-- Both constructed Weyl elements lie in the same N and have the literal
oriented simple markings. -/
def placement : WeylPlacement Q p where
  indices := indices
  lift := ![ni.val,nj.val]
  short := (alignedPinningHom_weyl Q split (indices 0) hVi μi ni).symm
  long := (alignedPinningHom_weyl Q split (indices 1) hVj μj nj).symm
  simple k := by
    fin_cases k
    · exact ni.class_eq
    · exact nj.class_eq

theorem short_range : ((p).shortOrbit 0).range = simpleRoot Q split (indices 0) :=
  alignedSimpleParameter_range Q split (indices 0) hVi μi ni

theorem long_range : ((p).longOrbit 0).range = simpleRoot Q split (indices 1) :=
  alignedSimpleParameter_range Q split (indices 1) hVj μj nj

theorem short_injective : Function.Injective (p).shortMap :=
  alignedPinningHom_injective Q split (indices 0) hVi μi ni

theorem long_injective : Function.Injective (p).longMap :=
  alignedPinningHom_injective Q split (indices 1) hVj μj nj

/-- The constructed cubic-field coroot is in the full source Cartan. -/
theorem short_cartan (t : Fˣ) : (p).shortMap (tor t) ∈ Q.tits.B ⊓ Q.tits.N :=
  alignedTorus_mem_cartan Q split (indices 0) hVi μi ni t

/-- The fixed-field coroot uses the same Cartan and the actual fixed subfield. -/
theorem long_cartan (t : Kˣ) : (p).longMap (tor t) ∈ Q.tits.B ⊓ Q.tits.N :=
  alignedTorus_mem_cartan Q split (indices 1) hVj μj nj t

end GeometricPinning
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
