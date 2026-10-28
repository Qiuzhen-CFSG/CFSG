module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartan
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.SuzukiGeometry

/-!
# The Suzuki Cartan action in the mixed hexagon contradiction

The canonical Suzuki root is a Sylow in the actual R_j. Its normalizer is
R_j intersect B, and the specified reflection identifies the two-point
intersection with the literal H intersect R_j. Thus this Cartan is cyclic
of order q-1, without identifying the whole panel group with Suzuki.

Conjugation by H acts on the same R_j and preserves that Sylow. The torus
acts faithfully since the concrete Suzuki group is centerless. If a
three-element of H had nontrivial action, multiplying it by a torus generator
would give an odd cyclic root-stabilizing automorphism group of order greater
than q-1. The proved Suzuki automorphism bound excludes this. N-normality of
T = Z(O_3(H)) transports centralization to every type-j root.

The opposite linear Cartan's cubic acts fixed-point-freely on all type-i
roots. CentralizerSections then constructs C(T) intersect U_sj, its actual
reflection action and the contradictory Frattini bounds. The earlier source
(1J) square profile supplies cubic divisibility, with genuine local models explicit; no unknown-group
perfectness or simplicity is assumed. Original-factor applications are in
CFSG HexagonStructure/SuzukiCartan.

Source: Fong--Seitz I (6C), printed pp.39--40. The automorphism argument uses
the equivalent odd cyclic root-stabilizer bound from Suzuki/OddCartan, rather
than assuming the desired Cartan centralization or a full-panel marking.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative Pointwise MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The Borel part of the actual root actor is exactly its root normalizer. -/
theorem rankOne_borel_iff_root_normalizer (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (r : rankOne Q split j) :
    (r : X ⧸ Q.D) ∈ Q.tits.B ↔
      r ∈ normalizer (((simpleRoot Q split j).subgroupOf (rankOne Q split j)) : Set (rankOne Q split j)) := by
  rw [← subgroupOf_normalizer_eq (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)]
  change (r : X ⧸ Q.D) ∈ Q.tits.B ↔ r.val ∈ normalizer (simpleRoot Q split j : Set (X ⧸ Q.D))
  constructor
  · intro hr
    obtain ⟨a,ha,t,ht,he⟩ := UnitarySource.rootActor_borel_factorization Q split j r.property hr
    rw [he]
    exact mul_mem ((simpleRoot Q split j).le_normalizer ha)
      (torus_normalizes_simpleRoot Q split j ht.2)
  · intro hr
    have hh := normalizer_inf_normalizer_le_normalizer_sup
      (simpleRoot Q split j) (simpleRemainder Q split j)
      ⟨hr,remainder_parabolic_normalizes Q split j hKj (rankOne_le_parabolic Q split j r.property)⟩
    have hs : simpleRoot Q split j ⊔ simpleRemainder Q split j = split.U := by
      apply le_antisymm (sup_le (simpleRoot_le Q split j) inf_le_left)
      intro x hx
      have hx' : x ∈ (simpleRoot Q split j : Set (X ⧸ Q.D)) *
          (simpleRemainder Q split j : Set (X ⧸ Q.D)) := by
        rw [simpleRoot_mul_remainder]; exact hx
      obtain ⟨a,ha,v,hv,rfl⟩ := hx'
      exact mul_mem (mem_sup_left ha) (mem_sup_right hv)
    rwa [hs,split.normalizer_eq] at hh

/-- A genuine Suzuki marking and the actual root order make the canonical
root a full Sylow of R_j. -/
theorem simpleRoot_sylow_of_suzuki (j : Fin 2) {m : ℕ}
    (μ : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    ∃ S : Sylow 2 (rankOne Q split j),
      (S : Subgroup (rankOne Q split j)) = (simpleRoot Q split j).subgroupOf (rankOne Q split j) := by
  let A := (simpleRoot Q split j).subgroupOf (rankOne Q split j)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split j)).comap_subtype
  obtain ⟨S,hS⟩ := hA.exists_le_sylow
  let S' := S.mapSurjective (f := μ.toMonoidHom) μ.surjective
  have hcA : Nat.card A = Nat.card (SuzukiRootSubgroup m) :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)).toEquiv).trans
      (Nat.card_congr ν.toEquiv)
  have hcS : Nat.card S = Nat.card (SuzukiRootSubgroup m) := by
    calc
      Nat.card S = Nat.card S' := Nat.card_congr ((S : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective).toEquiv
      _ = Nat.card (ReeSource.matrixRootSylow m) := Nat.card_congr (S'.equiv (ReeSource.matrixRootSylow m)).toEquiv
      _ = Nat.card (SuzukiRootSubgroup m) := by rw [ReeSource.matrixRootSylow_carrier]
  exact ⟨S,(eq_of_le_of_card_ge hS (by rw [hcA,hcS])).symm⟩

/-- The actual Cartan inside R_j, not the full panel quotient, is cyclic of
order q-1. The two-point model subgroup is identified inside the original Y. -/
theorem suzuki_rankOne_cartan_cyclic_card (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (s : RootReflection Q split j) :
    IsCyclic ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j)) ∧
      Nat.card ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j)) = 2^(2*m+1)-1 := by
  obtain ⟨S,hS⟩ := simpleRoot_sylow_of_suzuki Q split j μ ν
  let r := involutoryRootReflection Q split j s
  let t : rankOne Q split j := ⟨r.val,r.mem_rankOne⟩
  have ht : IsInvolution t := ⟨fun he => involutoryRootReflection_ne_one Q split j s
    (congrArg Subtype.val he),Subtype.ext (involutoryRootReflection_sq Q split j s)⟩
  have htB : t ∉ normalizer (S : Set (rankOne Q split j)) := by
    intro htB
    rw [show (S : Set (rankOne Q split j)) =
      ((simpleRoot Q split j).subgroupOf (rankOne Q split j) : Set _) from congrArg SetLike.coe hS] at htB
    exact Q.tits.representative_not_mem_B (Q.simple_mem j) r.val r.class_eq
      ((rankOne_borel_iff_root_normalizer Q split j hKj t).mpr htB)
  have he : BenderSuzuki.ZD.RankOneModelGeometry.twoPoint (normalizer (S : Set (rankOne Q split j))) t =
      (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) := by
    ext x
    change x ∈ normalizer (S : Set (rankOne Q split j)) ∧
      x ∈ BenderSuzuki.PFchapter1section1.rightConjugate (normalizer (S : Set (rankOne Q split j))) t ↔ _
    rw [BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry.mem_rightConjugate]
    simp only [show (S : Set (rankOne Q split j)) =
      ((simpleRoot Q split j).subgroupOf (rankOne Q split j) : Set _) from congrArg SetLike.coe hS,
      ← rankOne_borel_iff_root_normalizer Q split j hKj]
    constructor
    · intro hx
      apply UnitarySource.oppositeLevi_inf_two_borels_le_torus Q split j
      refine ⟨UnitarySource.rootActor_le_oppositeLevi Q split j x.property,hx.1,?_⟩
      rw [borelConjugate_eq _ r.val r.class_eq]
      exact hx.2
    · intro hx
      exact ⟨hx.1,((torus_conjugate r.val).symm ▸ hx).1⟩
  have hh := BenderSuzuki.ZD.RankOneModelGeometry.suzuki_twoPoint_geometry hm μ S t ht htB
  rw [he] at hh
  exact ⟨hh.1,hh.2.1⟩

/-- A commuting torus of full order q-1 leaves no nontrivial three-part in
an odd abelian group of automorphisms preserving the Suzuki root. -/
theorem suzuki_three_element_action_trivial
    {H : Type*} [Group H] [Finite H] [IsMulCommutative H]
    {m : ℕ} (hm : 0 < m) (ρ : H →* MulAut (SuzukiMatrixGroup m))
    (ho : Odd (Nat.card H)) (C : Subgroup H) [IsCyclic C]
    (hf : Function.Injective (ρ.comp C.subtype)) (hc : Nat.card C = 2^(2*m+1)-1)
    (hN : ∀ h, (SuzukiRootSubgroup m).map (ρ h).toMonoidHom = SuzukiRootSubgroup m)
    (t : H) {k : ℕ} (ht : t^(3^k) = 1) : ρ t = 1 := by
  obtain ⟨c,hcgen⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  have hcρ : orderOf (ρ c.val) = 2^(2*m+1)-1 :=
    (orderOf_injective (ρ.comp C.subtype) hf c).trans (hcgen.trans hc)
  have htρ : orderOf (ρ t) ∣ 3^k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow,ht,map_one])
  have hcop : Nat.Coprime (orderOf (ρ c.val)) (orderOf (ρ t)) := by
    rw [hcρ]
    apply Nat.Coprime.of_dvd_right htρ
    exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
      (three_not_dvd_suzuki_torus m)).symm.pow_right k
  let A := zpowers (ρ (c.val*t))
  have hAo : Odd (Nat.card A) := by
    rw [Nat.card_zpowers]
    exact ho.of_dvd_nat ((orderOf_map_dvd ρ (c.val*t)).trans (orderOf_dvd_natCard _))
  have hAn (a : A) : (SuzukiRootSubgroup m).map (A.subtype a).toMonoidHom = SuzukiRootSubgroup m := by
    obtain ⟨n,hn⟩ := a.property
    change (ρ (c.val*t))^n = a.val at hn
    change (SuzukiRootSubgroup m).map a.val.toMonoidHom = _
    rw [← hn, ← map_zpow]
    exact hN ((c.val*t)^n)
  have hb := SuzukiCartan.odd_cyclic_root_stabilizer_card_le m hm A.subtype A.subtype_injective hAo hAn
  have he := (show Commute c.val t from mul_comm _ _).map ρ
  change Nat.card (zpowers (ρ (c.val*t))) ≤ _ at hb
  rw [Nat.card_zpowers,map_mul,he.orderOf_mul_eq_mul_orderOf_of_coprime hcop,hcρ] at hb
  have hq : 0 < 2^(2*m+1)-1 := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ 2*m+1)
    norm_num at hh
    omega
  have hle : orderOf (ρ t) ≤ 1 := Nat.le_of_mul_le_mul_left (by simpa only [mul_one] using hb) hq
  have hpos : 0 < orderOf (ρ t) := orderOf_pos (ρ t)
  exact orderOf_eq_one_iff.mp (by omega)

/-- Every element of Z(O_3(H)) centralizes the actual Suzuki root actor.
The full torus is constructed inside H intersect R_j; its image and the
three-actor commute. The odd cyclic automorphism bound removes the actor. -/
theorem threeCartan_centralizes_suzuki_rankOne (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (s : RootReflection Q split j) :
    threeCartan Q ≤ centralizer (rankOne Q split j : Set (X ⧸ Q.D)) := by
  let H := Q.tits.B ⊓ Q.tits.N
  let R := rankOne Q split j
  let := split.abelian
  obtain ⟨S,hS⟩ := simpleRoot_sylow_of_suzuki Q split j μ ν
  obtain ⟨f,hf,_⟩ := suzukiSylow_aligned_equiv hm μ S
  let ρR : H →* MulAut R := RootAction.action H R (rankOne_torus_normalizes Q split j)
  let ρ : H →* MulAut (SuzukiMatrixGroup m) :=
    (MulAut.congr f.symm).toMonoidHom.comp ρR
  have hN (h : H) : (SuzukiRootSubgroup m).map (ρ h).toMonoidHom = SuzukiRootSubgroup m := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨a,ha,rfl⟩
      have hfa : f a ∈ (simpleRoot Q split j).subgroupOf R := by
        rw [← hS,← hf]
        exact mem_map_of_mem f.toMonoidHom ha
      have hh : ρR h (f a) ∈ (simpleRoot Q split j).subgroupOf R := by
        change (h : X ⧸ Q.D)*(f a : X ⧸ Q.D)*(h : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j
        exact (mem_normalizer_iff.mp (torus_normalizes_simpleRoot Q split j h.property) _).mp hfa
      have hmem : f (ρ h a) ∈ (SuzukiRootSubgroup m).map f.toMonoidHom := by
        rw [hf,hS]
        change f (f.symm (ρR h (f a))) ∈ (simpleRoot Q split j).subgroupOf R
        rwa [f.apply_symm_apply]
      exact (mem_map_iff_mem f.injective).mp hmem
    · rw [card_map_of_injective (ρ h).injective]
  let C := R.subgroupOf H
  let e : H.subgroupOf R ≃* C :=
    { toFun x := ⟨⟨x,x.property⟩,x.val.property⟩
      invFun x := ⟨⟨x,x.property⟩,x.val.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
  have hcart := suzuki_rankOne_cartan_cyclic_card Q split j hKj hm μ ν s
  let : IsCyclic C := e.isCyclic.mp hcart.1
  have hc : Nat.card C = 2^(2*m+1)-1 := (Nat.card_congr e.symm.toEquiv).trans hcart.2
  have hz : center R = ⊥ := by
    let : IsSimpleGroup (SuzukiMatrixGroup m) := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    let : IsSimpleGroup R := μ.isSimpleGroup
    rcases (inferInstance : (center R).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · have hcomm : IsMulCommutative R := ⟨⟨fun x y =>
        (mem_center_iff.mp (hz ▸ mem_top x) y).symm⟩⟩
      exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
        (Group.isSolvable_of_comm (fun x y => μ.symm.injective (by
          simpa only [map_mul] using mul_comm (μ.symm x) (μ.symm y))))).elim
  have hρC : Function.Injective (ρ.comp C.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro c hc1
    let r : R := ⟨c.val,c.property⟩
    have he : ρR c.val = MulAut.conj r := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rfl
    change (MulAut.congr f.symm) (ρR c.val) = 1 at hc1
    have hconj : MulAut.conj r = 1 := by
      rw [← he]
      apply (MulAut.congr f.symm).injective
      simpa only [map_one] using hc1
    have hr : r = 1 := (MulAut.conj_injective_of_center_eq_bot hz)
      (hconj.trans (map_one MulAut.conj).symm)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : R => (u : X ⧸ Q.D)) hr
  rw [threeCartan_eq_core_image Q split]
  rintro _ ⟨t,ht,rfl⟩
  obtain ⟨k,hk⟩ := pCore_isPGroup (⟨t,ht⟩ : pCore 3 H)
  have htρ := suzuki_three_element_action_trivial hm ρ
    (Nat.coprime_two_left.mp split.odd) C hρC hc hN t
    (congrArg Subtype.val hk)
  have htR : ρR t = 1 := by
    apply (MulAut.congr f.symm).injective
    change (MulAut.congr f.symm) (ρR t) = 1 at htρ
    simpa only [map_one] using htρ
  rw [mem_centralizer_iff]
  intro x hx
  have hh := congrArg (fun a : MulAut R => (a ⟨x,hx⟩ : X ⧸ Q.D)) htR
  change (t : X ⧸ Q.D)*x*(t : X ⧸ Q.D)⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- N-normality of the same T transports centralization to every literal
Suzuki root, with no whole-panel isomorphism assumption. -/
theorem threeCartan_centralizes_suzuki_roots (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (s : RootReflection Q split j) (w : Weyl Q) :
    rootAt Q split j w ≤ centralizer (threeCartan Q : Set (X ⧸ Q.D)) := by
  have hC := le_centralizer_iff.mp (threeCartan_centralizes_suzuki_rankOne Q split j hKj hm μ ν s)
  have hU : simpleRoot Q split j ≤ centralizer (threeCartan Q : Set (X ⧸ Q.D)) :=
    le_sup_left.trans hC
  let n := representative w
  have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hU
  change rootAt Q split j w ≤ rightConjugate (centralizer (threeCartan Q : Set (X ⧸ Q.D))) (n : X ⧸ Q.D) at hh
  rwa [rightConjugate_eq_self _ (normalizer_le_normalizer_centralizer _
    (threeCartan_normalized Q split n.property))] at hh

/-- The literal mixed linear/Suzuki centralizer contradiction of (6C).
The earlier source cubic-divisibility input is retained; all centralizer,
root action and Frattini premises are proved here from the actual models. -/
theorem no_mixed_suzuki_of_linear_cubic
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    (hthree : 3 ∣ Nat.card F - 1)
    {m : ℕ} (hm : 0 < m) (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) : False :=
  no_suzuki_centralizer_section Q split hhex i j hij sj hKj hm μj
    (suzuki_root_frattini_bound Q split j hm νj) (threeCartan Q) (threeCartan_le_cartan Q)
    (linear_threeCartan_nontrivial_fixedFree Q split i hKi μi si hthree).2
    (threeCartan_centralizes_suzuki_roots Q split j hKj hm μj νj sj)

open GTwoSource

/-- The actual square-product assertion of (1J) supplies the cubic in the
linear Cartan. No unexplained field-parity condition is introduced. -/
theorem linear_cubic_of_suzuki_square_profile
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i j : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,F))
    {m : ℕ} (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j))) :
    3 ∣ Nat.card F - 1 := by
  have hi := simpleRoot_card Q split i hKi μi
  obtain ⟨a,ha⟩ := (split.isTwo.to_le (simpleRoot_le Q split i)).exists_card_eq
  rw [hi] at ha
  have hc : Nat.Coprime 3 (Nat.card F) := by
    rw [ha]
    exact (by decide : Nat.Coprime 3 2).pow_right a
  have hne : Nat.card F % 3 ≠ 0 := by
    intro hz
    exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mp hc)
      ((Nat.dvd_iff_mod_eq_zero).mpr hz)
  have hj : Nat.card (simpleRoot Q split j) = (2^(2*m+1))^2 := by
    rw [Nat.card_congr νj.toEquiv,ReeSource.matrixRoot_card]
  have hq : 2^(2*m+1)%3 = 2 := by
    rw [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
    norm_num
  have hj3 : Nat.card (simpleRoot Q split j)%3 = 1 := by
    rw [hj,Nat.pow_mod,hq]
  obtain ⟨n,hn⟩ := hsquare
  rw [hi] at hn
  have hl : (Nat.card F*Nat.card (simpleRoot Q split j))%3 = Nat.card F%3 := by
    rw [Nat.mul_mod,hj3,mul_one,Nat.mod_mod]
  have hs := hl.symm.trans ((congrArg (fun k : ℕ => k%3) hn).trans (Nat.mul_mod n n 3))
  have hn3 : n%3 = 0 ∨ n%3 = 1 ∨ n%3 = 2 := by omega
  have hmod : Nat.card F%3 = 1 := by
    rcases hn3 with hn3 | hn3 | hn3 <;> norm_num [hn3] at hs <;> omega
  omega

/-- The mixed linear/Suzuki branch is excluded under the literal earlier
Feit--Higman square profile, with all Cartan and effective-action inputs proved. -/
theorem no_mixed_suzuki_of_square_profile
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {m : ℕ} (hm : 0 < m) (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j))) : False :=
  no_mixed_suzuki_of_linear_cubic Q split hhex i j hij hKi hKj μi si sj
    (linear_cubic_of_suzuki_square_profile Q split i j hKi μi νj hsquare) hm μj νj

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
