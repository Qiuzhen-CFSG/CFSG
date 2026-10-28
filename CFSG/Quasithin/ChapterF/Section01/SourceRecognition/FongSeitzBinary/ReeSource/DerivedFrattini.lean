module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositiveSixFourEquality
public import Theory.Frattini.BinarySquares

/-!
# The derived and Frattini subgroups of the source Suzuki radical

Conjugates of the proved near and mixed commutators put the two internal
linear roots and all three Suzuki Omega subgroups in the derived radical.
The seven ordered root factors therefore have square one in its
abelianization. This proves Φ(V)=[V,V] for V=U_s₂, including Sz(2), where
the Suzuki root itself is cyclic of order four.

The five-factor product in (6H)(f) is proved to lie in this subgroup; equality
with that product and the remaining center clauses are separate obligations.
OriginalDerivedFrattini retains the original two-core and literal Q.q maps;
Section10DerivedFrattini supplies the (10.3) equality at every N-conjugate.

Source: Fong--Seitz I (1973), (6H)(f), printed p.55; II (1974), (10.3),
printed p.221. Natural panel markings and odd linear degree remain explicit.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

private theorem ssq (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
private theorem sinv (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k := inv_eq_of_mul_eq_one_right (ssq Q k)
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
private theorem right_rep (k : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split k v) (representative w : X ⧸ Q.D) =
      rootAt Q split k (v*w) := rootAt_right Q split k v w _ (representative_spec _)
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
private theorem right_simple (k : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split k) (representative w : X ⧸ Q.D) = rootAt Q split k w := rfl

set_option linter.unusedSimpArgs false in
private theorem root_remainder (hm : rotationOrder Q = 8) (k : Fin 5) :
    rootAt Q split ((![0,0,1,1,1] : Fin 5 → Fin 2) k)
      ((![Q.simple 1*Q.simple 0,Q.simple 1*Q.simple 0*Q.simple 1,Q.simple 0,
        Q.simple 0*Q.simple 1,Q.simple 0*Q.simple 1*Q.simple 0] : Fin 5 → Weyl Q) k) ≤
        simpleRemainder Q split 1 := by
  have hL (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 1) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 2) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 3) (by omega)) (And.intro
    (wordLength_alternatingWord Q b (n := 4) (by omega))
    (wordLength_alternatingWord Q b (n := 5) (by omega)))))
  have h0 := hL false
  have h1 := hL true
  simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
    mul_one,←mul_assoc] at h0 h1
  fin_cases k <;> dsimp <;> apply rootAt_le_remainder Q split _ 1 _ <;>
    simp only [mul_inv_rev,sinv,mul_assoc,←mul_assoc (Q.simple 0) (Q.simple 0),
      ←mul_assoc (Q.simple 1) (Q.simple 1),ssq,one_mul,mul_one,←mul_assoc,
      Q.tits.wordLength_one,h0.1,h0.2.1,h0.2.2.1,h0.2.2.2.1,h0.2.2.2.2,
      h1.1,h1.2.1,h1.2.2.1,h1.2.2.2.1,h1.2.2.2.2]

include ν hC μ hB hn in
private theorem internal_linear_le_derived
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    rootAt Q split 0 (Q.simple 1*Q.simple 0) ≤
        ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ ∧
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) ≤
        ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
  let V := simpleRemainder Q split 1
  have hnear := source_near_eq_of_odd_degree Q split n hn m ν T hC μ hB hm hcore hc
  constructor
  · have he := congrArg (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D)) hnear
    rw [right_comm,right_simple,right_rep,right_rep] at he
    rw [←he]
    exact commutator_mono (root_remainder Q split hm 2) (root_remainder Q split hm 4)
  · have he := congrArg (fun A => rightConjugate A (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D)) hnear
    rw [right_comm,right_simple,right_rep,right_rep] at he
    have hE : rootAt Q split 1 ((Q.simple 0*Q.simple 1)*(Q.simple 0*Q.simple 1)) =
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
      rw [←mul_assoc,←right_rep]
      exact perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)
    rw [hE] at he
    have he' : ⁅rootAt Q split 1 (Q.simple 0*Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ =
        rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) := by simpa only [mul_assoc] using he
    rw [←he']
    exact commutator_mono (root_remainder Q split hm 3) (root_remainder Q split hm 4)

private theorem right_omega (A : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate (omegaOneAmbient A) (representative w : X ⧸ Q.D) =
      omegaOneAmbient (rightConjugate A (representative w : X ⧸ Q.D)) := by
  simp only [rightConjugate,comap_equiv_eq_map_symm']
  exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _


include ν hC μ hB hn in
private theorem internal_omega_le_derived
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) ≤
        ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ ∧
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) ≤
        ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ ∧
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0)) ≤
        ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
  have hbase := source_six_four_eq Q split n hn m ν T hC μ hB hm hcore hc
  have hEB : ⁅rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0),
      rootAt Q split 0 (Q.simple 1)⁆ =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
    let w := Q.simple 0*Q.simple 1*Q.simple 0
    have hh := congrArg (fun A => rightConjugate A (representative w : X ⧸ Q.D)) hbase
    rw [right_comm,right_simple,right_omega] at hh
    have ht := four_interval_reflection Q split hm 1 0 (by decide) (representative w) (representative_spec _)
    rw [ht.2.1,ht.2.2] at hh
    exact hh
  have hGD : ⁅rootAt Q split 1 (Q.simple 0),
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D)) hbase
    rw [right_comm,right_simple,right_omega,
      perpendicular_root_stable Q split hm 0 1 (by decide) _ (representative_spec _),right_rep] at hh
    exact hh
  have hEH : ⁅rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0),simpleRoot Q split 0⁆ =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0)) := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D)) hEB
    rw [right_comm,right_omega,perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)] at hh
    simpa only [right_rep,mul_assoc,ssq,mul_one,rootAt_one] using hh
  have hB := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).1
  have hH : simpleRoot Q split 0 ≤ simpleRemainder Q split 1 := by
    have h0 := wordLength_alternatingWord Q false (n := 1) (by omega)
    have h1 := wordLength_alternatingWord Q true (n := 1) (by omega)
    have h10 := wordLength_alternatingWord Q true (n := 2) (by omega)
    simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_true,mul_one] at h0 h1 h10
    rw [←rootAt_one Q split 0]
    apply rootAt_le_remainder Q split 0 1 1 <;>
      simp only [inv_one,mul_one,one_mul,Q.tits.wordLength_one,h0,h1,h10]

  refine ⟨?_,?_,?_⟩
  · rw [←hEB]
    exact commutator_mono (root_remainder Q split hm 4) hB
  · rw [←hGD]
    exact commutator_mono (root_remainder Q split hm 2) (root_remainder Q split hm 1)
  · rw [←hEH]
    exact commutator_mono (root_remainder Q split hm 4) hH

private theorem radical_seven (hm : rotationOrder Q = 8) :
    rootIntersection split (longest Q) (alternatingWord Q false 7)⁻¹ =
      simpleRemainder Q split 1 := by
  have hw : longest Q = Q.simple 1*alternatingWord Q false 7 := by
    have hh := (alternatingWord_longest Q true).symm
    rw [hm] at hh
    exact hh
  change split.U ⊓ unipotentConjugate split (longest Q*(alternatingWord Q false 7)⁻¹) = _
  rw [hw,mul_inv_cancel_right]
  rfl

private theorem radical_list (hm : rotationOrder Q = 8) :
    orderedRoots Q split false 7 =
      [simpleRoot Q split 0,rootAt Q split 1 (Q.simple 0),
        rootAt Q split 0 (Q.simple 1*Q.simple 0),
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0),
        rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1),rootAt Q split 0 (Q.simple 1)] := by
  have h0 := perpendicular_root_stable Q split hm 0 1 (by decide)
    (representative (Q.simple 0)) (representative_spec _)
  have h1 := perpendicular_root_stable Q split hm 1 0 (by decide)
    (representative (Q.simple 1)) (representative_spec _)
  rw [right_rep] at h0 h1
  have h5 := congrArg (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D)) h1
  have h6 := congrArg (fun A => rightConjugate A (representative (Q.simple 1*Q.simple 0) : X ⧸ Q.D)) h0
  simp only [right_rep,mul_assoc,ssq,mul_one] at h5 h6
  simp only [←mul_assoc] at h5 h6
  simp only [orderedRoots,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
    List.map_cons,List.map_nil,right_simple,right_rep]
  rw [h0,h5,h6]
  simp only [mul_assoc,ssq,mul_one]

include ν hC in
private theorem linear_square (w : Weyl Q) (x : X ⧸ Q.D)
    (hx : x ∈ rootAt Q split 0 w) : x^2 = 1 := by
  let e : rootAt Q split 0 w ≃* Multiplicative (BinaryGaloisField n) :=
    (RootAction.conjugateEquiv (simpleRoot Q split 0) (representative w)).trans
      (linearRootEquiv Q split 0 ν T hC)
  have hs : (⟨x,hx⟩ : rootAt Q split 0 w)^2 = 1 := by
    apply e.injective
    rw [map_pow,map_one]
    apply Multiplicative.toAdd.injective
    change 2 • (e ⟨x,hx⟩).toAdd = 0
    rw [two_nsmul,CharTwo.add_self_eq_zero]
  exact congrArg Subtype.val hs

include μ hB in
private theorem suzuki_square (w : Weyl Q) (x : X ⧸ Q.D)
    (hx : x ∈ rootAt Q split 1 w) : x^2 ∈ omegaOneAmbient (rootAt Q split 1 w) := by
  let e := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split 1).map e.toMonoidHom = rootAt Q split 1 w := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  rw [←he] at hx ⊢
  obtain ⟨y,hy,rfl⟩ := hx
  rw [←map_pow,←map_omegaOneAmbient_injective e.toMonoidHom e.injective]
  exact mem_map_of_mem e.toMonoidHom ((suzukiOmega_mem_iff_square Q split 1 m μ hB _).mpr ⟨y,hy,rfl⟩)

include ν hC μ hB hn in
/-- Every ordered factor has square in the actual derived radical, including Sz(2). -/
private theorem radical_factor_square
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (A : Subgroup (X ⧸ Q.D)) (hA : A ∈ orderedRoots Q split false 7)
    (x : X ⧸ Q.D) (hx : x ∈ A) : x^2 ∈ ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ := by
  have hΩ := internal_omega_le_derived Q split n hn m ν T hC μ hB hm hcore hc
  rw [radical_list Q split hm] at hA
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : x^2 = 1 := linear_square Q split n ν T hC 1 x (by rwa [rootAt_one])
    rw [he]; exact one_mem _
  · exact hΩ.2.2 (suzuki_square Q split m μ hB _ x hx)
  · rw [linear_square Q split n ν T hC _ x hx]; exact one_mem _
  · exact hΩ.2.1 (suzuki_square Q split m μ hB _ x hx)
  · rw [linear_square Q split n ν T hC _ x hx]; exact one_mem _
  · exact hΩ.1 (suzuki_square Q split m μ hB _ x hx)
  · rw [linear_square Q split n ν T hC _ x hx]; exact one_mem _

include ν hC μ hB hn in
/-- The intrinsic derived subgroup equals the Frattini subgroup of the Suzuki radical. -/
theorem source_radical_frattini_eq_commutator
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    frattini (simpleRemainder Q split 1) = _root_.commutator (simpleRemainder Q split 1) := by
  let V := simpleRemainder Q split 1
  let π : V →* Abelianization V := Abelianization.of
  let l := orderedRoots Q split false 7
  have hAV (A : Subgroup (X ⧸ Q.D)) (hA : A ∈ l) : A ≤ V := by
    change A ≤ simpleRemainder Q split 1
    rw [←radical_seven Q split hm]
    exact orderedRoots_le Q split false 7 (by omega) A hA
  have hs (A : Subgroup (X ⧸ Q.D)) (hA : A ∈ l) (x : A) :
      π (inclusion (hAV A hA) x)^2 = 1 := by
    rw [←map_pow]
    apply MonoidHom.mem_ker.mp
    change (inclusion (hAV A hA) x)^2 ∈ (Abelianization.of : V →* Abelianization V).ker
    rw [Abelianization.ker_of]
    have hh := radical_factor_square Q split n hn m ν T hC μ hB hm hcore hc A hA x x.property
    rw [←map_subtype_commutator] at hh
    obtain ⟨y,hy,he⟩ := hh
    have he' : y = (inclusion (hAV A hA) x)^2 := Subtype.ext he
    exact he' ▸ hy
  have hp : ∀ (k : List (Subgroup (X ⧸ Q.D))) (hk : ∀ A ∈ k, A ∈ l)
      (p : RootTuple k),
      π ⟨rootProduct k p,rootProduct_mem k V (fun A hA => hAV A (hk A hA)) p⟩ ^ 2 = 1 := by
    intro k
    induction k with
    | nil =>
      intro hk p
      change π 1 ^ 2 = 1
      rw [map_one,one_pow]
    | cons A k ih =>
      intro hk p
      have he : (⟨rootProduct (A::k) p,rootProduct_mem (A::k) V
          (fun B hB => hAV B (hk B hB)) p⟩ : V) =
          inclusion (hAV A (hk A (List.mem_cons_self ..))) p.1 *
            ⟨rootProduct k p.2,rootProduct_mem k V
              (fun B hB => hAV B (hk B (List.mem_cons_of_mem A hB))) p.2⟩ := rfl
      rw [he,map_mul,mul_pow,hs A (hk A (List.mem_cons_self ..)) p.1,
        ih (fun B hB => hk B (List.mem_cons_of_mem A hB)) p.2,one_mul]
  have hall (v : V) : π v^2 = 1 := by
    obtain ⟨p,he⟩ := (orderedCoordinates Q split false 7 (by omega)).surjective
      ⟨v,by rw [radical_seven Q split hm]; exact v.property⟩
    have hv : (⟨rootProduct l p,rootProduct_mem l V hAV p⟩ : V) = v := by
      apply Subtype.ext
      exact (orderedCoordinates_apply Q split false 7 (by omega) p).symm.trans (congrArg Subtype.val he)
    rw [←hv]
    exact hp l (fun _ h => h) p
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  apply le_antisymm _ (commutator_le_frattini_of_isPGroup (p := 2))
  have h := frattini_le_ker_of_square_image π hall
  rwa [Abelianization.ker_of] at h

include ν hC μ hB hn in
/-- The ambient form of the first equality in (6H)(f), on the same marked quotient. -/
theorem source_radical_derived_eq_frattini
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ =
      (frattini (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype := by
  rw [source_radical_frattini_eq_commutator Q split n hn m ν T hC μ hB hm hcore hc,map_subtype_commutator]

include ν hC μ hB hn in
/-- The five factors in (6H)(f) all lie in the derived radical, in the literal source order. -/
theorem source_radical_five_product_le_derived
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) *
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) : Set (X ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) *
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0)) : Set (X ⧸ Q.D)) ⊆
      ((⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
  have hlin := internal_linear_le_derived Q split n hn m ν T hC μ hB hm hcore hc
  have hΩ := internal_omega_le_derived Q split n hn m ν T hC μ hB hm hcore hc
  rintro x ⟨_,⟨_,⟨_,⟨c,hc,d,hd,rfl⟩,e,he,rfl⟩,f,hf,rfl⟩,g,hg,rfl⟩
  exact mul_mem (mul_mem (mul_mem (mul_mem (hΩ.1 hc) (hlin.2 hd)) (hΩ.2.1 he)) (hlin.1 hf)) (hΩ.2.2 hg)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
