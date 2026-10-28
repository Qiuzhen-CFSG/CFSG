module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanAction
public import Theory.SpecificGroups.SU3.BinarySylowFixerCentralizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.ModelTransport

/-!
# The unitary side of the mixed Suzuki hexagon exclusion

The canonical root is a full Sylow in the actual unitary root actor. Its
normalizer is the actor's Borel, and the two-point torus is literally its
intersection with the source Cartan H. The concrete unitary two-point
calculation supplies its order, retaining the projective scalar divisor.

The earlier square profile forces even unitary field degree. A cubic in
that actual torus belongs to T = Z(O₃(H)). In even degree a unitary
involution centralizer has order prime to three, so the cubic fixes no
nonidentity element of the canonical root group. Normality of T in N
transports this to every conjugate root. The proved Suzuki Cartan action
centralizes the other root family. CentralizerSections therefore gives the
literal two-root fixed subgroup, its nontrivial reflection action, and the
incompatible Frattini bounds 2^(4b) ≤ index ≤ 2^(2b).

Source: Fong--Seitz I (6C), printed pp.39--40. The involution-centralizer
proof replaces the source's unitary torus-coordinate fixed-point check.
Theorem no_mixed_unitary_suzuki_of_square_profile accepts every positive
unitary degree; the source square profile rules out degree one. The acting
Suzuki degree remains positive (b > 1). The Sz(2), equal-Suzuki and pure
unitary exclusions remain separate source branches.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates HermitianForm ReeSource
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
private instance : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

private theorem unitary_sylow_card {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card T = (2^n)^3 := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  obtain ⟨a⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hcard hf
  let T' := T.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : T ≃* T' := (T : Subgroup _).equivMapOfInjective a.toMonoidHom a.injective
  rw [Nat.card_congr b.toEquiv,
    Nat.card_congr (T'.equiv (EvenTwoRank.rootSylow
      (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl hn hcard hf)).toEquiv]
  change Nat.card (OddPrimeSylow.NormalizedOuter.Coverage.rootGroup
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl) = _
  exact OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card _ rfl _ hcard hf

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem simpleRoot_sylow_of_unitary {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (j : Fin 2) (μ : rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hroot : Nat.card (simpleRoot Q split j) = (2^n)^3) :
    ∃ S : Sylow 2 (rankOne Q split j),
      (S : Subgroup (rankOne Q split j)) = (simpleRoot Q split j).subgroupOf (rankOne Q split j) := by
  let A := (simpleRoot Q split j).subgroupOf (rankOne Q split j)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split j)).comap_subtype
  obtain ⟨S,hS⟩ := hA.exists_le_sylow
  let S' := S.mapSurjective (f := μ.toMonoidHom) μ.surjective
  have hcA : Nat.card A = (2^n)^3 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)).toEquiv).trans hroot
  let a : S ≃* S' := (S : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective
  have hcS : Nat.card S = (2^n)^3 := by
    calc
      Nat.card S = Nat.card S' := Nat.card_congr a.toEquiv
      _ = (2^n)^3 := unitary_sylow_card J hn hcard hconj S'
  exact ⟨S,(eq_of_le_of_card_ge hS (by rw [hcA,hcS])).symm⟩

theorem unitary_rankOne_cartan_cyclic_card {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hroot : Nat.card (simpleRoot Q split j) = (2^n)^3)
    (s : RootReflection Q split j) :
    IsCyclic ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j)) ∧
      Nat.card ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j)) =
        ((2^n)^2-1) / Nat.gcd 3 (2^n+1) := by
  obtain ⟨S,hS⟩ := simpleRoot_sylow_of_unitary J Q split (by omega) hcard hconj j μ hroot
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
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨a⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hcard hf
  have hh := BenderSuzuki.ZD.RankOneModelGeometry.unitary_projective_tori_of_equiv
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) hn rfl hcard hf
    (μ.trans a) S t ht htB
  rw [he] at hh
  exact ⟨hh.1,hh.2.1⟩

/-- At even binary degree a cubic element fixes no nonidentity element of
any two-subgroup of the actual projective unitary model. -/
theorem unitary_cubic_two_centralizer {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (heven : Even n) (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : IsPGroup 2 A) (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 3) :
    A ⊓ centralizer ({t} : Set _) = ⊥ := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let C := A ⊓ centralizer ({t} : Set _)
  have hC : IsPGroup 2 C := hA.to_le inf_le_left
  by_contra hne
  obtain ⟨u,hu,hu1⟩ := C.bot_or_exists_ne_one.resolve_left hne
  have hd : 2 ∣ Nat.card C :=
    (hC.dvd_orderOf (g := ⟨u,hu⟩) (fun he => hu1 (congrArg Subtype.val he))).trans
      (orderOf_dvd_natCard (⟨u,hu⟩ : C))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hd
  have hxt : t ∈ centralizer ({(x : ProjectiveSpecialUnitaryMatrixGroup J)} : Set _) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp x.property.2).symm
  have ho : orderOf (x : ProjectiveSpecialUnitaryMatrixGroup J) = 2 :=
    (Subgroup.orderOf_coe x).trans hx
  apply BinaryFixedCubic.involution_centralizer_three_free J hn hcard hconj heven x ho
  have ht' : orderOf (⟨t,hxt⟩ : centralizer ({(x : ProjectiveSpecialUnitaryMatrixGroup J)} : Set _)) = 3 :=
    (Subgroup.orderOf_coe _).symm.trans ht
  have hd := orderOf_dvd_natCard (⟨t,hxt⟩ : centralizer ({(x : ProjectiveSpecialUnitaryMatrixGroup J)} : Set _))
  rwa [ht'] at hd

/-- The source Z(O₃(H)) meets the actual unitary actor nontrivially and
has trivial fixed subgroup on every Weyl conjugate of its root. -/
theorem unitary_threeCartan_nontrivial_fixedFree {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (heven : Even n) (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hroot : Nat.card (simpleRoot Q split i) = (2^n)^3)
    (s : RootReflection Q split i) :
    threeCartan Q ⊓ rankOne Q split i ≠ ⊥ ∧
      ∀ w, rootAt Q split i w ⊓ centralizer (threeCartan Q : Set (X ⧸ Q.D)) = ⊥ := by
  let := split.abelian
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hmod : 2^n % 3 = 1 := by
    rw [Nat.BinaryTorusParity.two_pow_mod_three,if_pos (Nat.even_iff.mp heven)]
  have hcop : Nat.gcd 3 (2^n+1) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega))
  have hthree : 3 ∣ Nat.card ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split i)) := by
    rw [(unitary_rankOne_cartan_cyclic_card J Q split hn hcard hconj i hKi μ hroot s).2,
      hcop,Nat.div_one]
    have hs : ((2^n)^2) % 3 = 1 := by rw [Nat.pow_mod,hmod]
    have hp : 0 < (2^n)^2 := by positivity
    omega
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card'
    (G := ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split i))) 3 hthree
  let z : ↥(Q.tits.B ⊓ Q.tits.N) := ⟨t.val,t.property⟩
  have hz : orderOf z = 3 := by
    calc
      orderOf z = orderOf (z : X ⧸ Q.D) := (Subgroup.orderOf_coe z).symm
      _ = orderOf t.val := Subgroup.orderOf_coe t.val
      _ = orderOf t := Subgroup.orderOf_coe t
      _ = 3 := ht
  have hzcore : z ∈ pCore 3 ↥(Q.tits.B ⊓ Q.tits.N) := by
    have hp : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,hz,pow_one])
    exact (show zpowers z ≤ pCore 3 ↥(Q.tits.B ⊓ Q.tits.N) from
      le_sSup ⟨inferInstance,hp⟩) (mem_zpowers z)
  have htT : (t.val : X ⧸ Q.D) ∈ threeCartan Q := by
    rw [threeCartan_eq_core_image Q split]
    exact mem_map_of_mem (Q.tits.B ⊓ Q.tits.N).subtype hzcore
  have htne : (t.val : X ⧸ Q.D) ≠ 1 := by
    intro he
    have hh : orderOf (t.val : X ⧸ Q.D) = 3 := by
      simpa only [Subgroup.orderOf_coe] using ht
    rw [he,orderOf_one] at hh
    omega
  let A := (simpleRoot Q split i).subgroupOf (rankOne Q split i)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split i)).comap_subtype
  have hf := unitary_cubic_two_centralizer J hn hcard hconj heven
    (A.map μ.toMonoidHom) (hA.map _) (μ t.val)
    ((μ.orderOf_eq t.val).trans ((Subgroup.orderOf_coe t).trans ht))
  have hfT : simpleRoot Q split i ⊓ centralizer (threeCartan Q : Set (X ⧸ Q.D)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    let r : rankOne Q split i := ⟨u,(show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) hu.1⟩
    have hr : μ r ∈ A.map μ.toMonoidHom ⊓ centralizer ({μ t.val} : Set _) := by
      refine ⟨mem_map_of_mem _ (show r ∈ A from hu.1),?_⟩
      apply mem_centralizer_singleton_iff.mpr
      have he : t.val*r = r*t.val := Subtype.ext (mem_centralizer_iff.mp hu.2 _ htT)
      simpa only [map_mul] using congrArg μ he.symm
    have hr1 : r = 1 := μ.injective ((mem_bot.mp (hf ▸ hr)).trans μ.map_one.symm)
    exact mem_bot.mpr (congrArg Subtype.val hr1)
  refine ⟨fun he => htne (mem_bot.mp (he ▸ ⟨htT,t.val.property⟩)),?_⟩
  intro w
  let a := representative w
  have hnc := normalizer_le_normalizer_centralizer (threeCartan Q)
    (threeCartan_normalized Q split a.property)
  have hh := congrArg (fun A => rightConjugate A (a : X ⧸ Q.D)) hfT
  rw [rightConjugate_inf,rightConjugate_eq_self _ hnc] at hh
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (a : X ⧸ Q.D) = ⊥ := by
    ext x
    change (a : X ⧸ Q.D)*x*(a : X ⧸ Q.D)⁻¹ = 1 ↔ x = 1
    exact (MulAut.conj (a : X ⧸ Q.D)).map_eq_one_iff
  rw [hb] at hh
  exact hh

/-- The literal earlier (1J) square profile forces even unitary degree
when the other root is Suzuki. -/
theorem unitary_even_of_suzuki_square_profile
    (i j : Fin 2) {n m : ℕ}
    (hi : Nat.card (simpleRoot Q split i) = (2^n)^3)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j))) :
    Even n := by
  have hj : Nat.card (simpleRoot Q split j) % 3 = 1 := by
    rw [Nat.card_congr νj.toEquiv,matrixRoot_card,Nat.pow_mod]
    have hq : 2^(2*m+1)%3 = 2 := by
      rw [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
      norm_num
    rw [hq]
  obtain ⟨k,hk⟩ := hsquare
  have hs := congrArg (fun a : ℕ => a%3) hk
  rw [Nat.mul_mod,hi,Nat.pow_mod,hj,mul_one,Nat.mod_mod,Nat.mul_mod] at hs
  have hp := Nat.BinaryTorusParity.two_pow_mod_three n
  by_contra hn
  have hn' : n%2 ≠ 0 := by simpa only [Nat.even_iff] using hn
  rw [if_neg hn'] at hp
  rw [hp] at hs
  have hk3 : k%3 = 0 ∨ k%3 = 1 ∨ k%3 = 2 := by omega
  rcases hk3 with hk3 | hk3 | hk3 <;> norm_num [hk3] at hs

/-- The mixed unitary/Suzuki branch of (6C), on the literal T-centralizer
section. Both action bounds and all fixed-point premises are proved. -/
theorem no_mixed_unitary_suzuki_of_even {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (heven : Even n) (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : rankOne Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hroot : Nat.card (simpleRoot Q split i) = (2^n)^3)
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {m : ℕ} (hm : 0 < m) (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) : False :=
  no_suzuki_centralizer_section Q split hhex i j hij sj hKj hm μj
    (suzuki_root_frattini_bound Q split j hm νj) (threeCartan Q) (threeCartan_le_cartan Q)
    (unitary_threeCartan_nontrivial_fixedFree J Q split hn hcard hconj heven i hKi μi hroot si).2
    (threeCartan_centralizes_suzuki_roots Q split j hKj hm μj νj sj)

/-- Source (1J) supplies the even degree; no field-parity or Cartan-action
premise is added to the mixed (6C) exclusion. -/
theorem no_mixed_unitary_suzuki_of_square_profile {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : rankOne Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hroot : Nat.card (simpleRoot Q split i) = (2^n)^3)
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {m : ℕ} (hm : 0 < m) (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j))) : False := by
  have heven := unitary_even_of_suzuki_square_profile Q split i j hroot νj hsquare
  have hn2 : 2 ≤ n := by have := Nat.even_iff.mp heven; omega
  exact no_mixed_unitary_suzuki_of_even J Q split hn2 hcard hconj heven hhex i j hij
    hKi hKj μi hroot si sj hm μj νj

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
