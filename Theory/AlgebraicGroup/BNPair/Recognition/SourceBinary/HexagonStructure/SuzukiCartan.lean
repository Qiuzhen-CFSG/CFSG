module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.CentralizerSections
public import Theory.PGroupCore
public import Theory.SpecificGroups.Suzuki.OddCartan

/-!
# The source odd Cartan subgroup and its centralizer sections

Construct T = Z(O_3(H)) inside the literal marked quotient. Since the split
Cartan is abelian, T is its three-core; it is characteristic in H and normal
in N. A cubic in an actual linear rank-one Cartan proves T nontrivial and
fixed-point-free on every Weyl conjugate of that linear root.

On the other endpoint, an actual Cartan action image of order prime to three
centralizes T on every root. The existing whole-panel Suzuki marking proves
this image condition, but the weaker root-generated Suzuki marking alone is
not identified with that whole panel. The conditional mixed exclusion keeps
this distinction explicit. It applies the literal two-root centralizer action
and both Frattini bounds from CentralizerSections, not an arbitrary module.

Source: Fong--Seitz I (6C), printed pp.39--40. SuzukiCartanAction supplies the source automorphism argument directly on the
root-generated model, removing the extra action-image premise for the mixed
linear branch. Equal Suzuki, unitary and solvable branches remain separate.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Z(O_3(H)), as a subgroup of the actual source H. -/
@[expose] def threeCartanIn : Subgroup ↥(Q.tits.B ⊓ Q.tits.N) :=
  (center (pCore 3 ↥(Q.tits.B ⊓ Q.tits.N))).map
    (pCore 3 ↥(Q.tits.B ⊓ Q.tits.N)).subtype

/-- The same source subgroup, embedded in Y using the actual inclusion. -/
@[expose] def threeCartan : Subgroup (X ⧸ Q.D) :=
  (threeCartanIn Q).map (Q.tits.B ⊓ Q.tits.N).subtype

include split in
theorem threeCartanIn_eq_core : threeCartanIn Q = pCore 3 ↥(Q.tits.B ⊓ Q.tits.N) := by
  let := split.abelian
  rw [threeCartanIn, center_eq_top, ← MonoidHom.range_eq_map, range_subtype]

include split in
theorem threeCartan_eq_core_image : threeCartan Q =
    (pCore 3 ↥(Q.tits.B ⊓ Q.tits.N)).map (Q.tits.B ⊓ Q.tits.N).subtype := by
  rw [threeCartan, threeCartanIn_eq_core Q split]

include split in
theorem threeCartan_characteristic : (threeCartanIn Q).Characteristic := by
  rw [threeCartanIn_eq_core Q split]
  infer_instance

theorem threeCartan_le_cartan : threeCartan Q ≤ Q.tits.B ⊓ Q.tits.N := map_subtype_le _

include split in
theorem threeCartan_normalized : Q.tits.N ≤ normalizer (threeCartan Q : Set (X ⧸ Q.D)) := by
  let : (threeCartanIn Q).Characteristic := threeCartan_characteristic Q split
  intro n hn
  exact normalizer_le_normalizer_characteristic_image _ _ (torus_normalizes (⟨n,hn⟩ : Q.tits.N))

include split in
theorem threeCartan_normal : ((threeCartan Q).subgroupOf Q.tits.N).Normal :=
  normal_subgroupOf_of_le_normalizer (threeCartan_normalized Q split)

/-- A cubic in the genuine linear rank-one Cartan supplies nontriviality
of Z(O_3(H)), and its action has no nonidentity fixed point on U_i. -/
theorem linear_threeCartan_nontrivial_fixedFree
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
    (hthree : 3 ∣ Nat.card F - 1) :
    threeCartan Q ⊓ rankOne Q split i ≠ ⊥ ∧
      ∀ w, rootAt Q split i w ⊓ centralizer (threeCartan Q : Set (X ⧸ Q.D)) = ⊥ := by
  let := split.abelian
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i)) 3
    (by rwa [rankOne_cartan_card Q split i hKi μi s])
  let z : ↥(Q.tits.B ⊓ Q.tits.N) := ⟨t,t.property.1⟩
  have hz : orderOf z = 3 := by
    calc
      orderOf z = orderOf (z : X ⧸ Q.D) := (Subgroup.orderOf_coe z).symm
      _ = orderOf t := Subgroup.orderOf_coe t
      _ = 3 := ht
  have hzcore : z ∈ pCore 3 ↥(Q.tits.B ⊓ Q.tits.N) := by
    have hp : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,hz,pow_one])
    exact (show zpowers z ≤ pCore 3 ↥(Q.tits.B ⊓ Q.tits.N) from
      le_sSup ⟨inferInstance,hp⟩) (mem_zpowers z)
  have htT : (t : X ⧸ Q.D) ∈ threeCartan Q := by
    rw [threeCartan_eq_core_image Q split]
    exact mem_map_of_mem (Q.tits.B ⊓ Q.tits.N).subtype hzcore
  have htne : (t : X ⧸ Q.D) ≠ 1 := by
    intro he
    have hh : orderOf (t : X ⧸ Q.D) = 3 := by simpa only [Subgroup.orderOf_coe] using ht
    rw [he,orderOf_one] at hh
    omega
  have hf := rankOne_cartan_root_fixedFree Q split i hKi μi s
    t.property.1 t.property.2 htne
  have hfT : simpleRoot Q split i ⊓ centralizer (threeCartan Q : Set (X ⧸ Q.D)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    apply hf.le
    exact ⟨hu.1,mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hu.2 _ htT).symm⟩
  refine ⟨fun he => htne (mem_bot.mp (he ▸ ⟨htT,t.property.2⟩)),?_⟩
  intro w
  let n := representative w
  have hn := (threeCartan_normalized Q split n.property)
  have hnc := normalizer_le_normalizer_centralizer (threeCartan Q) hn
  have hh := congrArg (fun A => rightConjugate A (n : X ⧸ Q.D)) hfT
  rw [rightConjugate_inf, rightConjugate_eq_self _ hnc] at hh
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) = ⊥ := by
    ext x
    change (n : X ⧸ Q.D)*x*(n : X ⧸ Q.D)⁻¹ = 1 ↔ x = 1
    exact (MulAut.conj (n : X ⧸ Q.D)).map_eq_one_iff
  rw [hb] at hh
  exact hh

/-- An actual Cartan action image of order prime to three kills the source
three-core. This concerns the literal root conjugation action. -/
theorem threeCartan_centralizes_roots_of_image_card (j : Fin 2)
    (hthree : ¬ 3 ∣ Nat.card (cartanPanelMap Q j).range) (w : Weyl Q) :
    rootAt Q split j w ≤ centralizer (threeCartan Q : Set (X ⧸ Q.D)) := by
  apply le_centralizer_iff.mp
  rw [threeCartan_eq_core_image Q split]
  rintro t ⟨z,hz,rfl⟩
  let a := rootAction Q split j w
  let r := a.rangeRestrict z
  obtain ⟨k,hk⟩ := pCore_isPGroup (⟨z,hz⟩ : pCore 3 ↥(Q.tits.B ⊓ Q.tits.N))
  have hzk : z^(3^k) = 1 := congrArg Subtype.val hk
  have ho : orderOf r ∣ 3^k := orderOf_dvd_of_pow_eq_one (by
    change (a.rangeRestrict z)^(3^k) = 1
    rw [← map_pow,hzk,map_one])
  have hc : Nat.Coprime 3 (Nat.card a.range) := by
    rw [Nat.card_congr (rootActionImageEquiv Q split j w).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hthree
  have hr : r = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hc.pow_left k) ho (orderOf_dvd_natCard r))
  have ha : a z = 1 := congrArg Subtype.val hr
  rw [mem_centralizer_iff]
  intro x hx
  have hh := congrArg (fun f : MulAut (rootAt Q split j w) => (f ⟨x,hx⟩ : X ⧸ Q.D)) ha
  change (z : X ⧸ Q.D)*x*(z : X ⧸ Q.D)⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem three_not_dvd_suzuki_torus (m : ℕ) : ¬ 3 ∣ 2^(2*m+1)-1 := by
  have hm : 2^(2*m+1) % 3 = 2 := by
    rw [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
    norm_num
  have hp : 0 < 2^(2*m+1) := by positivity
  omega

/-- The existing whole-panel marking supplies the actual image order.
This stronger marking is retained explicitly; it is not deduced from R_j. -/
theorem suzuki_threeCartan_centralizes_roots (j : Fin 2) (m : ℕ)
    (μ : (Endpoint Q j ⧸ panelKernel Q j) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q j).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split j) (w : Weyl Q) :
    rootAt Q split j w ≤ centralizer (threeCartan Q : Set (X ⧸ Q.D)) := by
  apply threeCartan_centralizes_roots_of_image_card Q split j
  rw [suzuki_cartanImage_card Q split j m μ hB s]
  exact three_not_dvd_suzuki_torus m

/-- Root Frattini bounds transfer through an actual group isomorphism;
the chart need not pin any mixed multiplication or torus character. -/
theorem suzuki_root_frattini_bound (j : Fin 2) {m : ℕ} (hm : 0 < m)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    Nat.card (simpleRoot Q split j ⧸ frattini (simpleRoot Q split j)) ≤ 2^(2*m+1) := by
  rw [Nat.card_congr (QuotientGroup.congr _ _ ν (frattini_map_equiv ν)).toEquiv]
  exact SuzukiCartan.root_frattini_quotient_card_le m hm

/-- The mixed linear/Suzuki (6C) contradiction with the actual source T.
The only additional action input is the order of the actual Cartan image. -/
theorem no_mixed_suzuki_of_cartan_image
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    (hthree : 3 ∣ Nat.card F - 1)
    {m : ℕ} (hm : 0 < m) (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (himage : ¬ 3 ∣ Nat.card (cartanPanelMap Q j).range) : False :=
  no_suzuki_centralizer_section Q split hhex i j hij sj hKj hm μj
    (suzuki_root_frattini_bound Q split j hm νj) (threeCartan Q) (threeCartan_le_cartan Q)
    (linear_threeCartan_nontrivial_fixedFree Q split i hKi μi si hthree).2
    (threeCartan_centralizes_roots_of_image_card Q split j himage)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
