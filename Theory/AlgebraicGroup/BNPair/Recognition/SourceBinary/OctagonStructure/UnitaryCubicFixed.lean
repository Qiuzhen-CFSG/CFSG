module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitarySeparation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.LinearUnitaryCenter
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallSpecialUnitary
public import Theory.SpecificGroups.SU3.FixedFieldTwo

/-!
# The cubic fixed roots in the quadratic linear--unitary octagon

Use the entire three-core of the full Cartan, embedded in the same marked
quotient. Characteristicity makes it invariant under every Weyl lift.
A cubic element of the even-degree linear Cartan gives trivial fixed groups
on all linear roots. On an odd-degree unitary root center, the three-core
has a nonzero fixed point, and full-Cartan irreducibility makes it fix the
whole center.

For nonbinary unitary degree, irreducibility of the root Frattini quotient
makes an extra fixed point force centralization of every unitary root.
At degree one, orbit counting on the four-element Frattini quotient gives
the same implication. The separated-radical two-layer bounds exclude this
for both the special and projective actors, retaining the scalar cover.
Thus the unitary fixed group is exactly the intrinsic root center. The
last theorem identifies this center with the literal Frattini subgroup,
including degree one.

This proves the rootwise fixed-group input of Fong--Seitz I (6F), printed
pp.46--47. The subsequent centralizer product, commutator argument and
terminal exclusion remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

private theorem pgroup_fixes_irreducible_subgroup
    {Y : Type*} [Group Y] [Finite Y] (H A T : Subgroup Y)
    (hA : H ≤ normalizer (A : Set Y)) (hT : T ≤ H)
    (hTN : H ≤ normalizer (T : Set Y)) (hp : IsPGroup 3 T)
    (hcard : ¬ 3 ∣ Nat.card A - 1)
    (hirr : ∀ V : Subgroup Y, V ≤ A → V ≠ ⊥ →
      H ≤ normalizer (V : Set Y) → V=A) : A ≤ centralizer (T : Set Y) := by
  classical
  let ρ := RootAction.action T A (hT.trans hA)
  let : MulDistribMulAction T A := MulDistribMulAction.compHom A ρ
  let Z : SubMulAction T A := {
    carrier := {a | a ≠ 1}
    smul_mem' := by
      intro t a ha he
      exact ha ((MulAction.injective t) (he.trans (smul_one t).symm)) }
  have hc : Nat.card Z = Nat.card A - 1 := by
    let := Fintype.ofFinite A
    change Nat.card {a : A // a ≠ 1} = _
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp only [Fintype.card_unique,Nat.card_eq_fintype_card]
  obtain ⟨z,hz⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card Z (by rwa [hc])
  have hzC : ((z : A) : Y) ∈ centralizer (T : Set Y) := by
    intro t ht
    have he := congrArg (fun x : Z => ((x : A) : Y))
      (MulAction.mem_fixedPoints.mp hz (⟨t,ht⟩ : T))
    change t*(z : A)*t⁻¹ = (z : A) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hn : A ⊓ centralizer (T : Set Y) ≠ ⊥ := by
    intro he
    have hh : ((z : A) : Y) ∈ A ⊓ centralizer (T : Set Y) := ⟨(z : A).property,hzC⟩
    rw [he,mem_bot] at hh
    exact z.property (Subtype.ext hh)
  have he := hirr (A ⊓ centralizer (T : Set Y)) inf_le_left hn
    ((le_inf hA (hTN.trans (normalizer_le_normalizer_centralizer T))).trans
      inf_normalizer_le_normalizer_inf)
  rw [←he]
  exact inf_le_right

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The actual three-core of the full source Cartan, in the quotient. -/
def cartanThreeCore : Subgroup (X ⧸ Q.D) :=
  (pCore 3 ↥(Q.tits.B ⊓ Q.tits.N)).map (Q.tits.B ⊓ Q.tits.N).subtype

/-- The cubic core is a subgroup of the same full Cartan. -/
theorem cartanThreeCore_le : cartanThreeCore Q ≤ Q.tits.B ⊓ Q.tits.N :=
  map_subtype_le _

theorem cartanThreeCore_normalized :
    Q.tits.N ≤ normalizer (cartanThreeCore Q : Set (X ⧸ Q.D)) := by
  exact (fun _ hn => (normalizer_le_normalizer_characteristic_image
    (Q.tits.B ⊓ Q.tits.N) (pCore 3 ↥(Q.tits.B ⊓ Q.tits.N))) (torus_normalizes ⟨_,hn⟩))

theorem unitary_odd_center_fixed_by_threeCore
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : Odd b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (w : Weyl Q) :
    (center (rootAt Q split j w)).map (rootAt Q split j w).subtype ≤
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b hb.pos hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨e⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^b) hcard hf
  let A := rootAt Q split j w
  let Z := (center A).map A.subtype
  let f : A ≃* hermitianUnipotentCoord J₀ :=
    (RootAction.conjugateEquiv (simpleRoot Q split j) (representative w)).trans
      (QuadrangleStructure.simpleRootUnitaryEquiv J₀ Q split hb.pos hcard hf rfl j hKj (μj.trans e))
  let c : center (hermitianUnipotentCoord J₀) ≃*
      Multiplicative (HermitianForm.BorelTorus.EvenCenterAction.fixedField J₀) :=
    (MulEquiv.subgroupCongr (QuadrangleStructure.binary_coord_center J₀ hb.pos hcard hf)).trans
      (MonoidHom.ofInjective
        (HermitianForm.BorelTorus.EvenCenterAction.centralCoord_injective J₀)).symm
  have hc : Nat.card Z = 2^b :=
    (Nat.card_congr ((center A).equivMapOfInjective A.subtype A.subtype_injective).symm.toEquiv).trans
      ((Nat.card_congr (Subgroup.centerCongr f).toEquiv).trans
        ((Nat.card_congr c.toEquiv).trans ((Nat.card_congr Multiplicative.toAdd).trans hf)))
  apply pgroup_fixes_irreducible_subgroup (Q.tits.B ⊓ Q.tits.N) Z (cartanThreeCore Q)
  · exact (rootAt_torus_normalizes Q split j w).trans
      (normalizer_le_normalizer_characteristic_image A (center A))
  · exact map_subtype_le _
  · exact inf_le_right.trans (cartanThreeCore_normalized Q)
  · exact pCore_isPGroup.map _
  · rw [hc]
    exact Nat.prime_three.coprime_iff_not_dvd.mp (Nat.BinaryTorusParity.coprime_three_sub_one hb)
  · intro V hV hne hN
    exact QuadrangleStructure.rootAt_center_eq_of_torus_invariant Q split
      (QuadrangleStructure.unitary_sylow_center_irreducible J₀ hb.pos hcard hf rfl)
      j (μj.trans e) hKj w V hV hne hN

/-- The full cubic core contains a nonidentity element of the linear rank-one Cartan. -/
theorem exists_linear_cubic_in_threeCore
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {a : ℕ} (ha : Even a) (hE : Nat.card E=2^a)
    (i : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,E)) :
    ∃ t : X ⧸ Q.D, t ∈ cartanThreeCore Q ∧
      t ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i ∧ orderOf t=3 := by
  let := split.abelian
  let s := UnitarySource.actorReflection Q split i
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card'
    (G:=↥((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i)) 3 (by
      rw [rankOne_cartan_card Q split i hKi μi s,hE]
      exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff a).mpr ha)
  let z : ↥(Q.tits.B ⊓ Q.tits.N) := ⟨t,t.property.1⟩
  have hz : orderOf z=3 := by
    rw [←Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe t).trans ht
  have hp : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n:=1) (by
    rw [Nat.card_zpowers,hz,pow_one])
  have hle : zpowers z ≤ pCore 3 ↥(Q.tits.B ⊓ Q.tits.N) := le_sSup ⟨inferInstance,hp⟩
  exact ⟨t,⟨z,hle (mem_zpowers z),rfl⟩,t.property,(Subgroup.orderOf_coe t).trans ht⟩

/-- The actual cubic core fixes no nonidentity point of any linear root. -/
theorem even_linear_threeCore_fixed_free
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {a : ℕ} (ha : Even a) (hE : Nat.card E=2^a)
    (i : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,E)) (w : Weyl Q) :
    rootAt Q split i w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = ⊥ := by
  obtain ⟨t,ht,htr,hto⟩ := exists_linear_cubic_in_threeCore Q split ha hE i hKi μi
  have hne : t ≠ 1 := by intro he; rw [he,orderOf_one] at hto; omega
  have hsimple : simpleRoot Q split i ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = ⊥ := by
    apply bot_unique
    exact (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ht))).trans
      (rankOne_cartan_root_fixedFree Q split i hKi μi
        (UnitarySource.actorReflection Q split i) htr.1 htr.2 hne).le
  have hh := congrArg (fun A => rightConjugate A (representative w : X ⧸ Q.D)) hsimple
  rw [rightConjugate_inf,rightConjugate_eq_self _
    (normalizer_le_normalizer_centralizer _ (cartanThreeCore_normalized Q (representative w).property))] at hh
  exact hh.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot])


private theorem threeCore_centralizes_all_roots_of_one
    (j : Fin 2) (w : Weyl Q)
    (h : rootAt Q split j w ≤ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)))
    (v : Weyl Q) : rootAt Q split j v ≤ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) := by
  let n := representative (w⁻¹*v)
  have hh := comap_mono (f:=(MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) h
  change rightConjugate (rootAt Q split j w) (n : X ⧸ Q.D) ≤
    rightConjugate (centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) (n : X ⧸ Q.D) at hh
  rw [rootAt_right Q split j w (w⁻¹*v) n (representative_spec _),
    mul_inv_cancel_left,rightConjugate_eq_self _
      (normalizer_le_normalizer_centralizer _ (cartanThreeCore_normalized Q n.property))] at hh
  exact hh

private theorem unitary_threeCore_fixed_dichotomy
    {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 2 ≤ b) (hcard : Nat.card F=(2^b)^2)
    (hf : Nat.card {x : F // J.conj x=x}=2^b)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (w : Weyl Q) :
    rootAt Q split j w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
        (center (rootAt Q split j w)).map (rootAt Q split j w).subtype ∨
      (∀ v, rootAt Q split j v ≤ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) := by
  classical
  let := split.abelian
  let A := rootAt Q split j w
  let K := pCore 3 ↥(Q.tits.B ⊓ Q.tits.N)
  let τ := rootAtCartanFrattiniRepresentation Q split j w
  let : τ.IsIrreducible :=
    (unitary_rootAt_cartan_frattini_irreducible Q split J hb hcard hf hJ j μj hKj w).1
  by_cases hfix : Representation.invariants (τ.comp K.subtype) = ⊥
  · left
    intro x hx
    let a : A := ⟨x,hx.1⟩
    let v : Additive (A ⧸ frattini A) := Additive.ofMul ((QuotientGroup.mk' (frattini A)) a)
    have hv : v ∈ Representation.invariants (τ.comp K.subtype) := by
      intro k
      change Additive.ofMul ((quotientAut (frattini A))
        (rootAction Q split j w k.val) ((QuotientGroup.mk' (frattini A)) a)) = v
      rw [quotientAut_apply_mk]
      have he : rootAction Q split j w k.val a = a := by
        apply Subtype.ext
        change (k.val : X ⧸ Q.D)*x*(k.val : X ⧸ Q.D)⁻¹=x
        have hc := mem_centralizer_iff.mp hx.2 (k.val : X ⧸ Q.D)
          (mem_map_of_mem (Q.tits.B ⊓ Q.tits.N).subtype k.property)
        rw [hc,mul_inv_cancel_right]
      rw [he]
    rw [hfix,Submodule.mem_bot] at hv
    have ha : a ∈ frattini A := (QuotientGroup.eq_one_iff _).mp
      (congrArg Additive.toMul hv)
    rw [(unitary_rootAt_frattini_center Q split J hb hcard hf hJ j μj hKj w).1] at ha
    exact mem_map_of_mem A.subtype ha
  · right
    apply threeCore_centralizes_all_roots_of_one Q split j w
    intro a ha
    apply mem_centralizer_iff.mpr
    rintro t ⟨k,hk,rfl⟩
    have hh := Representation.le_ker_of_normal_invariants_ne_bot τ K hfix hk
    rw [rootAtCartanFrattiniRepresentation_kernel] at hh
    have he := congrArg (fun f : MulAut A => (f ⟨a,ha⟩ : X ⧸ Q.D)) hh
    change (k : X ⧸ Q.D)*a*(k : X ⧸ Q.D)⁻¹=a at he
    exact mul_inv_eq_iff_eq_mul.mp he

/-- The precise unitary root fixed group in the nonbinary quadratic case:
the full cubic core fixes exactly the intrinsic root center. -/
theorem unitary_threeCore_fixed_eq_center
    {E F : Type*} [Field E] [Finite E] [CharP E 2] [Field F] [Finite F]
    (J : HermitianForm 3 F) {b : ℕ} (hb : 2 ≤ b) (hob : Odd b)
    (hE : Nat.card E=2^(2*b)) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (hsquare : ∃ a : simpleRoot Q split j, a^2 ≠ 1)
    (w : Weyl Q) :
    rootAt Q split j w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) =
      (center (rootAt Q split j w)).map (rootAt Q split j w).subtype := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b hob.pos hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨e⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^b) hcard hf
  apply le_antisymm
  · rcases unitary_threeCore_fixed_dichotomy Q split J₀ hb hcard hf rfl j hKj (μj.trans e) w with hle | hfix
    · exact hle
    obtain ⟨t,ht,htr,hto⟩ := exists_linear_cubic_in_threeCore Q split (even_two_mul b) hE i hKi μi
    have hne : t ≠ 1 := by intro he; rw [he,orderOf_one] at hto; omega
    have hfixed (v : Weyl Q) : t ∈ centralizer (rootAt Q split j v : Set (X ⧸ Q.D)) :=
      (le_centralizer_iff.mp (hfix v)) ht
    have hfree := linear_cartan_separated_roots Q split i j hij hKi μi htr.1 htr.2 hne hfixed
    exact (separated_unitary_radical_false Q split J hb hcard hconj hm i j hij hKj σ hσ
      hroot hsquare ⟨t,htr.1⟩ (fun v => ⟨hfixed v,hfree v⟩)).elim
  · exact le_inf (map_subtype_le _)
      (unitary_odd_center_fixed_by_threeCore Q split J hob hcard hconj j hKj μj w)


private theorem three_action_four_fixed
    {K V : Type*} [Group K] [Group V] [Finite V]
    [MulDistribMulAction K V] (hK : IsPGroup 3 K) (hc : Nat.card V=4)
    (x : V) (hx : x ≠ 1) (hfix : ∀ k : K, k • x=x) :
    ∀ k : K, ∀ v : V, k • v=v := by
  let F := FixedPoints.subgroup K V
  have hn : F ≠ ⊥ := by
    intro he
    have hm : x ∈ F := hfix
    rw [he,mem_bot] at hm
    exact hx hm
  have hlo := F.one_lt_card_iff_ne_bot.mpr hn
  have hup : Nat.card F ≤ 4 := hc ▸ card_le_card_group F
  have hmod := hK.card_modEq_card_fixedPoints V
  change Nat.card V % 3 = Nat.card F % 3 at hmod
  rw [hc] at hmod
  have he : F=⊤ := F.eq_top_of_card_eq (by omega)
  intro k v
  exact (show v ∈ F from he ▸ mem_top v) k

private theorem small_unitary_threeCore_fixed_dichotomy
    {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 3 F)
    (hcard : Nat.card F=4) (hf : Nat.card {x : F // J.conj x=x}=2)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (w : Weyl Q) :
    rootAt Q split j w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
        (center (rootAt Q split j w)).map (rootAt Q split j w).subtype ∨
      (∀ v, rootAt Q split j v ≤ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) := by
  classical
  let A := rootAt Q split j w
  let K := pCore 3 ↥(Q.tits.B ⊓ Q.tits.N)
  let V := A ⧸ frattini A
  let α := rootAtCartanFrattiniAction Q split j w
  let : MulDistribMulAction K V := MulDistribMulAction.compHom V (α.comp K.subtype)
  let f : A ≃* hermitianUnipotentCoord J :=
    (RootAction.conjugateEquiv (simpleRoot Q split j) (representative w)).trans
      (QuadrangleStructure.simpleRootUnitaryEquiv J Q split (n:=1) (by decide)
        (by simpa using hcard) (by simpa using hf) hJ j hKj μj)
  have hq : Nat.card V=4 := by
    let a := QuotientGroup.congr _ _ f (frattini_map_equiv f)
    rw [Nat.card_congr a.toEquiv,
      HermitianForm.BinaryRootFrattini.frattini_eq_first_kernel J hcard hf,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
        (HermitianForm.BinaryRootFrattini.firstCoordinate J)
        (HermitianForm.BinaryRootFrattini.firstCoordinate_surjective J hcard hf)).toEquiv,
      Nat.card_congr Multiplicative.toAdd,hcard]
  have hPhi : frattini A ≤ center A :=
    (HermitianForm.BinaryRootFrattini.equiv_structure J hcard hf f).2
  by_cases hle : rootAt Q split j w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
      (center (rootAt Q split j w)).map (rootAt Q split j w).subtype
  · exact Or.inl hle
  right
  obtain ⟨x,hx,hxz⟩ := Set.not_subset.mp hle
  let a : A := ⟨x,hx.1⟩
  let v : V := (QuotientGroup.mk' (frattini A)) a
  have hv : v ≠ 1 := by
    intro he
    exact hxz (mem_map_of_mem A.subtype (hPhi ((QuotientGroup.eq_one_iff _).mp he)))
  have hfix (k : K) : k • v=v := by
    change ((quotientAut (frattini A)) (rootAction Q split j w k.val))
      ((QuotientGroup.mk' (frattini A)) a) = v
    rw [quotientAut_apply_mk]
    have he : rootAction Q split j w k.val a = a := by
      apply Subtype.ext
      change (k.val : X ⧸ Q.D)*x*(k.val : X ⧸ Q.D)⁻¹=x
      have hc := mem_centralizer_iff.mp hx.2 (k.val : X ⧸ Q.D)
        (mem_map_of_mem (Q.tits.B ⊓ Q.tits.N).subtype k.property)
      rw [hc,mul_inv_cancel_right]
    rw [he]
  have hall := three_action_four_fixed (pCore_isPGroup (p:=3)) hq v hv hfix
  apply threeCore_centralizes_all_roots_of_one Q split j w
  intro a ha
  apply mem_centralizer_iff.mpr
  rintro t ⟨k,hk,rfl⟩
  have hh : k ∈ (rootAtCartanFrattiniRepresentation Q split j w).ker := by
    change rootAtCartanFrattiniRepresentation Q split j w k = 1
    ext z
    exact congrArg Additive.ofMul (hall ⟨k,hk⟩ z.toMul)
  rw [rootAtCartanFrattiniRepresentation_kernel] at hh
  have he := congrArg (fun f : MulAut A => (f ⟨a,ha⟩ : X ⧸ Q.D)) hh
  change (k : X ⧸ Q.D)*a*(k : X ⧸ Q.D)⁻¹=a at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The same exact fixed-center equality at degree one, retaining either
the full special-unitary scalar cover or its projective quotient. -/
theorem small_unitary_threeCore_fixed_eq_center
    {E F : Type*} [Field E] [Finite E] [CharP E 2] [Field F] [Finite F]
    (J : HermitianForm 3 F) (hE : Nat.card E=4) (hcard : Nat.card F=4)
    (hconj : ∀ x, J.conj x=x^2)
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hmodel : Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hroot : Nat.card (simpleRoot Q split j)=8) (w : Weyl Q) :
    rootAt Q split j w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) =
      (center (rootAt Q split j w)).map (rootAt Q split j w).subtype := by
  have hf : Nat.card {x : F // J.conj x=x}=2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 (by decide)
      (by simpa using hcard) (by simpa using hconj)
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=2)
    (by simpa only [Nat.card_eq_fintype_card,Nat.reducePow] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨C,hC⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis
    J 2 hcard hf
  let ep := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.projectiveEquiv J C hC
  apply le_antisymm
  · rcases small_unitary_threeCore_fixed_dichotomy Q split J₀ hcard hf rfl j hKj (μj.trans ep) w with hle | hfix
    · exact hle
    obtain ⟨t,ht,htr,hto⟩ := exists_linear_cubic_in_threeCore Q split (a:=2) (by decide) hE i hKi μi
    have hne : t ≠ 1 := by intro he; rw [he,orderOf_one] at hto; omega
    have hfixed (v : Weyl Q) : t ∈ centralizer (rootAt Q split j v : Set (X ⧸ Q.D)) :=
      (le_centralizer_iff.mp (hfix v)) ht
    have hfree := linear_cartan_separated_roots Q split i j hij hKi μi htr.1 htr.2 hne hfixed
    have hsep (v : Weyl Q) := And.intro (hfixed v) (hfree v)
    rcases hmodel with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
    · let es := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC
      exact (separated_small_special_radical_false Q split j J₀ hcard hconj rfl hKj
        (ν.trans es) hroot hm i hij ⟨t,htr.1⟩ hsep).elim
    · let := HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj
      let : Group.IsSolvable (rankOne Q split j) :=
        Group.isSolvable_of_surjective (f:=ν.symm.toMonoidHom) ν.symm.surjective
      have hR : Nat.card (rankOne Q split j)=72 :=
        (Nat.card_congr ν.toEquiv).trans (HermitianForm.FixedFieldTwo.card_projective J hcard hconj)
      exact (separated_nine_radical_false Q split j hR hroot hm i hij hKj ⟨t,htr.1⟩ hsep).elim
  · exact le_inf (map_subtype_le _) (unitary_odd_center_fixed_by_threeCore Q split J
      (b:=1) (by decide) (by simpa using hcard) (by simpa using hconj) j hKj μj w)

/-- The center in the fixed-root formula is literally the Frattini subgroup,
including the root of order eight at unitary degree one. -/
theorem unitary_rootAt_frattini_eq_center_all
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (w : Weyl Q) :
    frattini (rootAt Q split j w) = center (rootAt Q split j w) := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b hb hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨e⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^b) hcard hf
  let A := rootAt Q split j w
  let f : A ≃* hermitianUnipotentCoord J₀ :=
    (RootAction.conjugateEquiv (simpleRoot Q split j) (representative w)).trans
      (QuadrangleStructure.simpleRootUnitaryEquiv J₀ Q split hb hcard hf rfl j hKj (μj.trans e))
  apply le_antisymm (HermitianForm.BinaryRootFrattini.equiv_structure J₀ hcard hf f).2
  intro a ha
  have he := MulEquivClass.apply_mem_center f ha
  change f a ∈ center (hermitianUnipotentCoord J₀) at he
  rw [QuadrangleStructure.binary_coord_center J₀ hb hcard hf] at he
  have hφ : f a ∈ frattini (hermitianUnipotentCoord J₀) := by
    rw [HermitianForm.BinaryRootFrattini.frattini_eq_first_kernel J₀ hcard hf]
    obtain ⟨z,hz⟩ := he
    rw [←hz]
    rfl
  rw [←frattini_map_equiv f] at hφ
  exact (mem_map_iff_mem f.injective).mp hφ

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
