module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineSubgroup
public import Theory.GroupTheory.IntersectionIndexBound
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryCubicFixed

/-!
# Middle-root intersections in the unitary nine-b subgroup

Write C for the middle unitary root in the literal subgroup X of order
2^(9b), and M for its Frattini subgroup. Since |C|=2^(3b) and |M|=2^b,
relative index counting bounds any W in X with C intersect W <= M by
2^(7b). This applies to elementary abelian subgroups and to Z(X).

Full-Cartan irreducibility on C/M and M gives precisely three invariant
subgroups of C. At b=1, a proper subgroup outside M would be cyclic of
order four. The Cartan three-core acts trivially on such a cyclic group,
contradicting its exact fixed subgroup M. Thus the same trichotomy and
large-subgroup containment hold in every positive degree. The square,
center and Frattini statements use actual unitary root coordinates.

Source: Fong--Seitz I (6F), printed p.47, the subgroup-intersection and
index assertions. The matching CFSG module discharges the model and cubic
fixed-root premises at the original factor marks. These results do not
prove the sharp projective representation bound, that a proper candidate
subgroup is elementary, or the subsequent lower-central persistence.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External BenderSuzuki.MatrixGroups.HermitianForm
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem unitaryNineSubgroup_card_le_of_middle_intersection
    (i j : Fin 2) {b : ℕ}
    (hX : Nat.card (unitaryNineSubgroup Q split i j)=2^(9*b))
    (hC : Nat.card (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i))=2^(3*b))
    (hM : Nat.card (rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i))=2^b)
    (V : Subgroup (X ⧸ Q.D)) (hV : V ≤ unitaryNineSubgroup Q split i j)
    (hI : rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ⊓ V ≤
      rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)) :
    Nat.card V ≤ 2^(7*b) := by
  let C := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let K := unitaryNineSubgroup Q split i j
  have hCK : C ≤ K := le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have hi : C.relIndex K=2^(6*b) := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) C K bot_le hCK
    rw [relIndex_bot_left,relIndex_bot_left] at hc
    rw [show Nat.card C=2^(3*b) from hC,show Nat.card K=2^(9*b) from hX] at hc
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^(3*b))
    rw [hc,←pow_add]
    congr 1
    omega
  calc
    Nat.card V ≤ Nat.card ↥(C ⊓ V)*C.relIndex K :=
      card_le_card_inf_mul_relIndex_of_le V C K hV
    _ ≤ 2^b*2^(6*b) := by
      rw [hi]
      exact Nat.mul_le_mul_right _ ((Nat.card_le_card_of_injective (inclusion hI) (inclusion_injective hI)).trans_eq hM)
    _ = 2^(7*b) := by rw [←pow_add]; congr 1; omega

/-- All involutions of a unitary root lie in its literal Frattini subgroup. -/
theorem unitary_rootAt_square_one_iff_frattini
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (w : Weyl Q) (x : rootAt Q split j w) :
    x^2=1 ↔ (x : X ⧸ Q.D) ∈ rootFrattiniAt Q split j w := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b hb hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨ep⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^b) hcard hf
  let e : rootAt Q split j w ≃* hermitianUnipotentCoord J₀ :=
    (ReeSource.RootAction.conjugateEquiv (simpleRoot Q split j) (representative w)).trans
      (QuadrangleStructure.simpleRootUnitaryEquiv J₀ Q split hb hcard hf rfl j hKj (μ.trans ep))
  exact ((HermitianForm.BinaryRootFrattini.equiv_structure J₀ hcard hf e).1 x).symm.trans
    (mem_map_iff_mem (rootAt Q split j w).subtype_injective).symm

theorem unitaryNineSubgroup_elementary_card_le
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hi : Nat.card (simpleRoot Q split i)=2^(2*b))
    (hj : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (V : Subgroup (X ⧸ Q.D)) (hV : V ≤ unitaryNineSubgroup Q split i j)
    (hE : IsElementaryAbelian 2 V) : Nat.card V ≤ 2^(7*b) := by
  have hC : Nat.card (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i))=2^(3*b) := by
    rw [rootAt,card_rightConjugate,hj,←pow_mul,Nat.mul_comm b 3]
  apply unitaryNineSubgroup_card_le_of_middle_intersection Q split i j
    (unitaryNineSubgroup_card Q split J hb hcard hconj hm i j hij hKj μ hi hj)
    hC (unitary_rootFrattini_card Q split J hb hcard hconj j hKj μ _) V hV
  intro x hx
  let := hE
  exact (unitary_rootAt_square_one_iff_frattini Q split J hb hcard hconj j hKj μ _
    ⟨x,hx.1⟩).mp (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x hx.2))

theorem unitaryNineSubgroup_center_card_le
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hi : Nat.card (simpleRoot Q split i)=2^(2*b))
    (hj : Nat.card (simpleRoot Q split j)=(2^b)^3) :
    Nat.card (center (unitaryNineSubgroup Q split i j)) ≤ 2^(7*b) := by
  let K := unitaryNineSubgroup Q split i j
  let C := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  have hCK : C ≤ K := le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have hC : Nat.card C=2^(3*b) := by
    dsimp only [C]
    rw [rootAt,card_rightConjugate,hj,←pow_mul,Nat.mul_comm b 3]
  have hbound := unitaryNineSubgroup_card_le_of_middle_intersection Q split i j
    (unitaryNineSubgroup_card Q split J hb hcard hconj hm i j hij hKj μ hi hj)
    hC (unitary_rootFrattini_card Q split J hb hcard hconj j hKj μ _)
    ((center K).map K.subtype) (map_subtype_le _) (by
      rintro x ⟨hxC,z,hz,rfl⟩
      rw [rootFrattiniAt,unitary_rootAt_frattini_eq_center_all Q split J hb hcard hconj j hKj μ]
      refine ⟨⟨z,hxC⟩,mem_center_iff.mpr (fun y => ?_),rfl⟩
      exact Subtype.ext (congrArg (fun z : K => (z : X ⧸ Q.D)) ((mem_center_iff.mp hz) ⟨y,hCK y.property⟩)))
  rwa [card_map_of_injective K.subtype_injective] at hbound



/-- Irreducibility on a root's Frattini quotient only needs Cartan
normalization of the subgroup; normality in the whole root is unnecessary. -/
theorem rootAt_cartan_subgroup_dichotomy (j : Fin 2) (w : Weyl Q)
    (hirr : (rootAtCartanFrattiniRepresentation Q split j w).IsIrreducible)
    (W : Subgroup (X ⧸ Q.D)) (hW : W ≤ rootAt Q split j w)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D))) :
    W ≤ rootFrattiniAt Q split j w ∨ W=rootAt Q split j w := by
  let A := rootAt Q split j w
  let π := QuotientGroup.mk' (frattini A)
  let D := (W.subgroupOf A).map π
  let ρ := rootAtCartanFrattiniRepresentation Q split j w
  let := hirr
  let S : Subrepresentation ρ := ⟨AddSubgroup.toZModSubmodule 2 D.toAddSubgroup,by
    intro t v hv
    change v.toMul ∈ D at hv
    obtain ⟨x,hx,hxv⟩ := hv
    change ((quotientAut (frattini A)) (ReeSource.rootAction Q split j w t)) v.toMul ∈ D
    rw [←hxv,quotientAut_apply_mk]
    apply mem_map_of_mem π
    exact le_normalizer_iff.mp hH t.val t.property x.val hx⟩
  rcases eq_bot_or_eq_top S with hs | hs
  · left
    intro x hx
    have hp : Additive.ofMul (π ⟨x,hW hx⟩) ∈ S := mem_map_of_mem π hx
    rw [hs] at hp
    exact mem_map_of_mem A.subtype ((QuotientGroup.eq_one_iff _).mp
      (congrArg Additive.toMul hp))
  · right
    have hd : D=⊤ := by
      apply top_unique
      intro x _
      have hx : Additive.ofMul x ∈ S := hs ▸
        (show Additive.ofMul x ∈ (⊤ : Subrepresentation ρ) from trivial)
      exact hx
    have he := congrArg (Subgroup.comap π) hd
    have hsup : W.subgroupOf A ⊔ frattini A=⊤ := by
      simpa only [D,π,comap_map_eq,QuotientGroup.ker_mk',comap_top] using he
    exact le_antisymm hW (subgroupOf_eq_top.mp (frattini_nongenerating hsup))

/-- The full Cartan subgroup dichotomy for a nonbinary unitary root,
without a relative normality assumption. -/
private theorem unitary_rootAt_cartan_subgroup_dichotomy
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 2 ≤ b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (w : Weyl Q) (W : Subgroup (X ⧸ Q.D)) (hW : W ≤ rootAt Q split j w)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D))) :
    W ≤ rootFrattiniAt Q split j w ∨ W=rootAt Q split j w := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b (by omega) hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨ep⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^b) hcard hf
  exact rootAt_cartan_subgroup_dichotomy Q split j w
    (unitary_rootAt_cartan_frattini_irreducible Q split J₀ hb hcard hf rfl j (μ.trans ep) hKj w).1
    W hW hH

private theorem small_root_cartan_subgroup_dichotomy
    (j : Fin 2) (w : Weyl Q)
    (hcard : Nat.card (rootAt Q split j w)=8)
    (hsq : ∀ x : rootAt Q split j w,
      x^2=1 ↔ (x : X ⧸ Q.D) ∈ rootFrattiniAt Q split j w)
    (hfix : rootAt Q split j w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
      rootFrattiniAt Q split j w)
    (W : Subgroup (X ⧸ Q.D)) (hW : W ≤ rootAt Q split j w)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D))) :
    W ≤ rootFrattiniAt Q split j w ∨ W=rootAt Q split j w := by
  let A := rootAt Q split j w
  by_cases he : W=A
  · exact Or.inr he
  left
  by_contra hn
  obtain ⟨x,hx,hxp⟩ := Set.not_subset.mp hn
  have hle : Nat.card W ≤ 4 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup (X ⧸ Q.D)) W A bot_le hW
    rw [relIndex_bot_left,relIndex_bot_left,show Nat.card A=8 from hcard] at hc
    have hp : 0 < W.relIndex A := Nat.card_pos
    have hne : W.relIndex A ≠ 1 := by
      intro h1
      exact he (le_antisymm hW (relIndex_eq_one.mp h1))
    have hi : 2 ≤ W.relIndex A := by omega
    nlinarith
  let a : W := ⟨x,hx⟩
  have ha2 : a^2 ≠ 1 := by
    intro heq
    exact hxp ((hsq ⟨x,hW hx⟩).mp
      (Subtype.ext (congrArg (fun z : W => (z : X ⧸ Q.D)) heq)))
  have hd : orderOf a ∣ 2^3 := by
    have hd := (orderOf_dvd_natCard a).trans (card_dvd_of_le hW)
    rwa [hcard] at hd
  have ho : orderOf a=4 := by
    obtain ⟨k,hk,hkcard⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hd
    have ha := pow_orderOf_eq_one a
    have hl := (_root_.orderOf_le_card (x:=a)).trans hle
    interval_cases k <;> norm_num at hkcard
    · exact (ha2 (by rw [hkcard,one_pow])).elim
    · exact (ha2 (hkcard ▸ ha)).elim
    · exact hkcard
    · omega
  have hfour : Nat.card W=4 := le_antisymm hle (ho ▸ _root_.orderOf_le_card (x:=a))
  let : IsCyclic W := isCyclic_of_orderOf_eq_card a (ho.trans hfour.symm)
  let T := cartanThreeCore Q
  let α := ReeSource.RootAction.action T W ((cartanThreeCore_le Q).trans hH)
  have hp3 : IsPGroup 3 T := pCore_isPGroup.map _
  have h3 : IsPGroup 3 α.range := hp3.of_surjective α.rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  have h2 : IsPGroup 2 (MulAut W) := IsPGroup.of_card (n:=1) (by
    rw [IsCyclic.card_mulAut,hfour]; decide)
  have hbot : α.range=⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne 3 2 (by decide) α.range α.range h3 (h2.to_subgroup _))
  have hcentral : x ∈ centralizer (T : Set (X ⧸ Q.D)) := by
    intro t ht
    have ht1 : α ⟨t,ht⟩=1 := mem_bot.mp (hbot ▸ (show α ⟨t,ht⟩ ∈ α.range from ⟨⟨t,ht⟩,rfl⟩))
    have hh := congrArg (fun f : MulAut W => (f a : X ⧸ Q.D)) ht1
    change t*x*t⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh)
  exact hxp (hfix ⟨hW hx,hcentral⟩)

/-- The cubic fixed-root identity supplies the missing field-two case
of the full-Cartan subgroup dichotomy. -/
theorem unitary_rootAt_cartan_subgroup_dichotomy_all
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (w : Weyl Q)
    (hfix : rootAt Q split j w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
      rootFrattiniAt Q split j w)
    (W : Subgroup (X ⧸ Q.D)) (hW : W ≤ rootAt Q split j w)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D))) :
    W ≤ rootFrattiniAt Q split j w ∨ W=rootAt Q split j w := by
  by_cases hb2 : 2 ≤ b
  · exact unitary_rootAt_cartan_subgroup_dichotomy Q split J hb2 hcard hconj j hKj μ w W hW hH
  have hb1 : b=1 := by omega
  apply small_root_cartan_subgroup_dichotomy Q split j w ?_
    (unitary_rootAt_square_one_iff_frattini Q split J hb hcard hconj j hKj μ w) hfix W hW hH
  rw [rootAt,card_rightConjugate,hroot,hb1]
  decide

/-- The source's middle-root containment in every positive unitary degree.
The cubic identity is the previously proved source hypothesis, not a new
relative normality requirement on the invariant subgroup. -/
theorem unitaryNineSubgroup_large_contains_middle_all
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hi : Nat.card (simpleRoot Q split i)=2^(2*b))
    (hj : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (hfix : rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
        rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i))
    (V : Subgroup (X ⧸ Q.D)) (hV : V ≤ unitaryNineSubgroup Q split i j)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (V : Set (X ⧸ Q.D)))
    (hlarge : 2^(7*b) < Nat.card V) :
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤ V := by
  let C := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  have hHC : Q.tits.B ⊓ Q.tits.N ≤ normalizer (C : Set (X ⧸ Q.D)) :=
    rootAt_torus_normalizes Q split j _
  rcases unitary_rootAt_cartan_subgroup_dichotomy_all Q split J hb hcard hconj j hKj μ hj _ hfix
    (C ⊓ V) inf_le_left ((le_inf hHC hH).trans inf_normalizer_le_normalizer_inf) with hs | hs
  · have hC : Nat.card C=2^(3*b) := by
      dsimp only [C]
      rw [rootAt,card_rightConjugate,hj,←pow_mul,Nat.mul_comm b 3]
    exact (not_lt_of_ge (unitaryNineSubgroup_card_le_of_middle_intersection Q split i j
      (unitaryNineSubgroup_card Q split J hb hcard hconj hm i j hij hKj μ hi hj)
      hC (unitary_rootFrattini_card Q split J hb hcard hconj j hKj μ _) V hV hs)
      hlarge).elim
  · exact hs ▸ (show C ⊓ V ≤ V from inf_le_right)


/-- The exact source alternatives for a Cartan-invariant subgroup of a
unitary root: trivial, Frattini, or the whole root, including degree one. -/
theorem unitary_rootAt_cartan_subgroup_trichotomy
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (w : Weyl Q)
    (hfix : rootAt Q split j w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤
      rootFrattiniAt Q split j w)
    (W : Subgroup (X ⧸ Q.D)) (hW : W ≤ rootAt Q split j w)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D))) :
    W=⊥ ∨ W=rootFrattiniAt Q split j w ∨ W=rootAt Q split j w := by
  rcases unitary_rootAt_cartan_subgroup_dichotomy_all Q split J hb hcard hconj j hKj μ hroot
    w hfix W hW hH with hs | hs
  · by_cases hn : W=⊥
    · exact Or.inl hn
    right; left
    have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b hb hcard hconj
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
      (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
    let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    obtain ⟨ep⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
      J (2^b) hcard hf
    rw [rootFrattiniAt,unitary_rootAt_frattini_eq_center_all Q split J hb hcard hconj j hKj μ] at hs ⊢
    exact QuadrangleStructure.rootAt_center_eq_of_torus_invariant Q split
      (QuadrangleStructure.unitary_sylow_center_irreducible J₀ hb hcard hf rfl)
      j (μ.trans ep) hKj w W hs hn hH
  · exact Or.inr (Or.inr hs)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
