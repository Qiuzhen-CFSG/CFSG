module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.Center
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Core
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MatrixOrbit
public import Theory.Representation.BinaryConjugationSection.Canonical
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Normalizers
public import Theory.GroupTheory.SubgroupProductCard
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Dimension
public import Theory.GroupAction.NoncentralTwoChiefLength.SectionMaps
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation

/-!
# The partner intersection order in source 15.3.56

The same canonical source module gives cubic length s+2 on P: the lower
four-dimensional tensor contributes two, and its upper first-factor natural
sum contributes s. The invariant subgroup P ∩ J has the same length as P
and as O₂(J), since the two corresponding quotients are fixed and of order
two respectively.

On the literal rank-one core, F and X give a natural tensor quotient by
E = F ∩ X. If its multiplicity is r, its length is r; the lower plane V₀
gives length one on E. Hence r+1=s+2. The same natural decomposition counts
|U|=2^(r+1)|E|, while the original two-factor decomposition gives
|U|=2^(2s+5), so |E|=2^(s+3).

The rank-one quotient, its centralizer kernel, and its index-two bridge are
earlier geometric inputs. The original subgroup maps and the same
SourceModuleData witness are retained throughout; no independent rank or
order witness is substituted.

Source: Aschbacher–Smith, 15.3.56(2–3), printed pp.1147–1148; the natural
quotient argument of G.2.3(6), printed p.334.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open scoped IsMulCommutative
open Representation.BinaryFixedPoints Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
variable {G : Type*} [Group G] [Finite G]

/-- A fixed quotient contributes zero to the intrinsic cubic length. -/
private theorem length_eq_of_commutator_le (A R N : Subgroup G)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R)
    (hNR : N ≤ R) (hAR : A ≤ normalizer (R : Set G))
    (hAN : A ≤ normalizer (N : Set G)) [(N.subgroupOf R).Normal]
    (hc : ⁅A,R⁆ ≤ N) : conjugationCubicLength A R = conjugationCubicLength A N := by
  let := quotientConjugationAction A R N hAR hAN
  have hs := sectionCubicLength_eq_quotient_of_twoGroup A R N hA hR hNR hAR hAN
  have hz : FixedPoints.cubicLength A (R ⧸ N.subgroupOf R) = 0 := by
    apply FixedPoints.cubicLength_eq_zero_of_trivial
    intro a q
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) q
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ((a : G) * (r : G) * (a : G)⁻¹) / (r : G) ∈ N
    rw [div_eq_mul_inv]
    exact hc (commutator_mem_commutator a.property r.property)
  rw [hz] at hs
  have hm := conjugationCubicLength_mono A hNR
  unfold sectionCubicLength at hs
  omega

/-- An invariant index-two subgroup has the same cubic length. -/
private theorem length_eq_of_index_two (A R N : Subgroup G)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R)
    (hNR : N ≤ R) (hAR : A ≤ normalizer (R : Set G))
    (hAN : A ≤ normalizer (N : Set G)) [(N.subgroupOf R).Normal]
    (hi : N.relIndex R = 2) : conjugationCubicLength A R = conjugationCubicLength A N := by
  let := quotientConjugationAction A R N hAR hAN
  have hs := sectionCubicLength_eq_quotient_of_twoGroup A R N hA hR hNR hAR hAN
  have hc : Nat.card (R ⧸ N.subgroupOf R) = 2 := hi
  have hz : FixedPoints.cubicLength A (R ⧸ N.subgroupOf R) = 0 := by
    unfold FixedPoints.cubicLength
    apply Nat.log_eq_zero_iff.mpr
    left
    have hh := (FixedPoints.subgroup A (R ⧸ N.subgroupOf R)).index_dvd_card
    have hn := Nat.le_of_dvd (by omega : 0 < Nat.card (R ⧸ N.subgroupOf R)) hh
    omega
  rw [hz] at hs
  have hm := conjugationCubicLength_mono A hNR
  unfold sectionCubicLength at hs
  omega

/-- The actual binary conjugation section computes the difference of lengths. -/
private theorem binary_section_length {I R N A : Subgroup G}
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) I M}
    (d : Representation.BinaryConjugationSection I R N ρ)
    (hAI : A ≤ I) (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) :
    sectionCubicLength A N R = Nat.log 4 (fixedIndex (ρ.comp (inclusion hAI))) := by
  let τ := ρ.comp (inclusion hAI)
  let := action τ
  let s : ConjugationSection (Y := Multiplicative M) A N R (MonoidHom.id A) := {
    le := d.kernel_le
    normalizes := hAI.trans d.normalized
    projection := d.coordinates
    onto := d.onto
    kernel := d.kernel_eq
    equivariant := by
      intro a r
      apply Multiplicative.toAdd.injective
      exact d.equivariant (inclusion hAI a) r }
  exact s.length_eq hA hR Function.surjective_id

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open scoped TensorProduct

private theorem natural_cubic_fixed (c : S₃) (hc : c ^ 3 = 1) (hne : c ≠ 1)
    (v : BinaryPermutation.core (Fin 3))
    (hv : BinaryPermutation.coreRepresentation (Fin 3) c v = v) : v = 0 := by
  apply Subtype.ext
  exact (show ∀ c : S₃, c ^ 3 = 1 → c ≠ 1 → ∀ v : Fin 3 → ZMod 2,
    (∑ i, v i) = 0 → (∀ i, v (c⁻¹ i) = v i) → v = 0 by decide +kernel)
      c hc hne v.val v.property (fun i => congrArg (fun w : BinaryPermutation.core (Fin 3) => w.val i) hv)

private theorem natural_cubic_norm (c : S₃) (hc : c ^ 3 = 1) (hne : c ≠ 1)
    (v : BinaryPermutation.core (Fin 3)) :
    v + BinaryPermutation.coreRepresentation (Fin 3) c v +
      BinaryPermutation.coreRepresentation (Fin 3) c
        (BinaryPermutation.coreRepresentation (Fin 3) c v) = 0 := by
  apply Subtype.ext
  exact (show ∀ c : S₃, c ^ 3 = 1 → c ≠ 1 → ∀ v : Fin 3 → ZMod 2,
    (∑ i, v i) = 0 → (fun i => v i + v (c⁻¹ i) + v (c⁻¹ (c⁻¹ i))) = 0 by decide +kernel)
      c hc hne v.val v.property

variable {A M : Type*} [Group A] [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

omit [Finite M] in
/-- On the actual two-factor decomposition, a nontrivial first cubic has
fixed space exactly the second summand. -/
private theorem product_invariants {ρ : Representation (ZMod 2) (S₃ × S₃) M}
    (d : ProductDecomposition ρ) (π : A →* S₃ × S₃)
    (hr : ∀ a, (π a).2 = 1) (a : A) (c : S₃)
    (ha : π a = (c,1)) (hc : c^3=1) (hne : c≠1) :
    Representation.invariants (ρ.comp π) = d.right.toSubmodule := by
  have hfixed (b : A) (v : d.right.toSubmodule) : ρ (π b) v = v := by
    obtain ⟨x,rfl⟩ := d.rightEquiv.surjective v
    have he := d.right_equivariant (π b) x
    rw [hr] at he
    have hh := congrArg Subtype.val he.symm
    simp only [map_one, Module.End.one_apply] at hh
    exact hh
  have hleft (v : d.left.toSubmodule) (hv : ρ (c,1) v = v) : v = 0 := by
    obtain ⟨x,rfl⟩ := d.leftEquiv.surjective v
    have he : (fun j => BinaryPermutation.coreRepresentation (Fin 3) c (x j)) = x := by
      apply d.leftEquiv.injective
      exact (d.left_equivariant (c,1) x).trans (Subtype.ext hv)
    have hx : x = 0 := by
      funext j
      exact natural_cubic_fixed c hc hne (x j) (congrFun he j)
    rw [hx,map_zero]
  ext v
  constructor
  · intro hv
    have hsup : v ∈ d.left.toSubmodule ⊔ d.right.toSubmodule :=
      d.complementary.sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨l,hl,r,hr',rfl⟩ := Submodule.mem_sup.mp hsup
    have hv' : ρ (c,1) (l+r) = l+r := by simpa only [MonoidHom.comp_apply,ha] using hv a
    have hrfix : ρ (c,1) r = r := ha ▸ hfixed a ⟨r,hr'⟩
    have hlfix : ρ (c,1) l = l := by rw [map_add,hrfix] at hv'; exact add_right_cancel hv'
    have hl0 : l = 0 := congrArg Subtype.val (hleft ⟨l,hl⟩ hlfix)
    simpa only [hl0,zero_add] using hr'
  · intro hv a
    exact hfixed a ⟨v,hv⟩

/-- The first natural multiplicity is the cubic fixed-point length of the
literal representation restricted through the given actor map. -/
private theorem product_cubic_length {ρ : Representation (ZMod 2) (S₃ × S₃) M}
    (d : ProductDecomposition ρ) (π : A →* S₃ × S₃)
    (hr : ∀ a, (π a).2 = 1) (a : A) (c : S₃)
    (ha : π a = (c,1)) (hc : c^3=1) (hne : c≠1) :
    Nat.log 4 (fixedIndex (ρ.comp π)) = d.leftMultiplicity := by
  have hcard := fixedIndex_mul_card (ρ.comp π)
  rw [product_invariants d π hr a c ha hc hne] at hcard
  have hd : Nat.card M = Nat.card d.left.toSubmodule * Nat.card d.right.toSubmodule := by
    rw [← Nat.card_congr (Submodule.prodEquivOfIsCompl _ _ d.complementary).toEquiv,
      Nat.card_prod]
  rw [hd] at hcard
  have hi : fixedIndex (ρ.comp π) = Nat.card d.left.toSubmodule :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := d.right.toSubmodule)) hcard
  rw [hi,Module.natCard_eq_pow_finrank (K := ZMod 2),d.finranks.1,Nat.card_zmod,
    pow_mul, show (2:ℕ)^2=4 from rfl, Nat.log_pow (by decide : 1<4)]

omit [Finite M] in
/-- A natural tensor has zero fixed space for every nontrivial cubic. -/
private theorem tensor_cubic_fixed
    {I : Type*} [AddCommGroup I] [Module (ZMod 2) I]
    (σ : Representation (ZMod 2) S₃ M)
    (j : I ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] M)
    (hj : ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃ I)
        (BinaryPermutation.coreRepresentation (Fin 3))) a z) = σ a (j z))
    (c : S₃) (hc : c^3=1) (hne : c≠1) (v : M) (hv : σ c v = v) : v = 0 := by
  let τ := Representation.tprod (Representation.trivial (ZMod 2) S₃ I)
    (BinaryPermutation.coreRepresentation (Fin 3))
  have hnorm (z : I ⊗[ZMod 2] BinaryPermutation.core (Fin 3)) :
      z + τ c z + τ c (τ c z) = 0 := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero,add_zero]
    | tmul i n =>
      change i ⊗ₜ _ + i ⊗ₜ _ + i ⊗ₜ _ = 0
      rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add, natural_cubic_norm c hc hne,
        TensorProduct.tmul_zero]
    | add x y hx hy =>
      simp only [map_add]
      calc
        _ = (x + τ c x + τ c (τ c x)) + (y + τ c y + τ c (τ c y)) := by abel
        _ = 0 := by rw [hx,hy,add_zero]
  obtain ⟨z,rfl⟩ := j.surjective v
  have hn := congrArg j (hnorm z)
  have hj' (a : S₃) (z) : j (τ a z) = σ a (j z) := hj a z
  simp only [map_zero,map_add,hj',hv] at hn
  simpa only [← two_smul (ZMod 2), show (2:ZMod 2)=0 from rfl, zero_smul,zero_add] using hn

/-- The natural tensor multiplicity computes the cubic length on the
actual rank-one core quotient. -/
private theorem tensor_cubic_length
    {I : Type*} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]
    (σ : Representation (ZMod 2) S₃ M)
    (j : I ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] M)
    (hj : ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃ I)
        (BinaryPermutation.coreRepresentation (Fin 3))) a z) = σ a (j z))
    (π : A →* S₃) (a : A) (ha : (π a)^3=1) (hne : π a≠1) :
    Nat.log 4 (fixedIndex (σ.comp π)) = Module.finrank (ZMod 2) I := by
  have hi : Representation.invariants (σ.comp π) = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    exact tensor_cubic_fixed σ j hj (π a) ha hne v (hv a)
  have hc := fixedIndex_mul_card (σ.comp π)
  rw [hi] at hc
  simp only [Nat.card_unique,mul_one] at hc
  rw [hc,Module.natCard_eq_pow_finrank (K := ZMod 2),← j.finrank_eq,
    Module.finrank_tensorProduct, BinaryPermutation.finrank_core]
  simp only [Fintype.card_fin,Nat.card_zmod]
  rw [Nat.mul_comm (Module.finrank (ZMod 2) I) 2,pow_mul,
    show (2:ℕ)^2=4 from rfl,Nat.log_pow (by decide : 1<4)]

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02
open CFSG.Quasithin.ChapterG.Section02.Setup
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open ClassicalOrthogonal.FourPlusMatrix
open Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

private theorem source_cubic_fixed_free (d : Hypothesis D g) (y : D.I g)
    (hy : d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) y) = MatrixOrbit.leftCubic) :
    D.VL ⊓ centralizer (zpowers (y:G) : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  let v : D.VL := ⟨x,hx.1⟩
  have he := d.quotientMatrixEquiv_equivariant y v
  have hc := mem_centralizer_iff.mp hx.2 (y:G) (mem_zpowers (y:G))
  change (y:G) * (v:G) = (v:G) * (y:G) at hc
  rw [hc,mul_inv_cancel_right,hy] at he
  have hfixed : matrixAction MatrixOrbit.leftCubic (d.coordinates v).toAdd =
      (d.coordinates v).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply d.coordinates.symm.injective
    apply Subtype.ext
    simpa only [ofAdd_toAdd,MulEquiv.symm_apply_apply] using he
  have hv0 : (d.coordinates v).toAdd = 0 := by
    by_contra hn
    exact MatrixOrbit.cubic_moves _ hn hfixed
  have hv1 : v = 1 := by
    apply d.coordinates.injective
    apply Multiplicative.toAdd.injective
    simpa only [map_one,toAdd_one] using hv0
  exact congrArg Subtype.val hv1

omit [Finite G] in
private theorem length_of_fixed_free (A R : Subgroup G)
    (hc : R ⊓ centralizer (A : Set G) = ⊥) :
    conjugationCubicLength A R = Nat.log 4 (Nat.card R) := by
  have he : (centralizer (A : Set G)).subgroupOf R = ⊥ := by
    ext r
    constructor
    · intro hr
      exact Subtype.ext (hc.le ⟨r.property,hr⟩)
    · intro hr
      exact (Subgroup.mem_bot.mp hr) ▸ one_mem _
  simp only [conjugationCubicLength,relIndex,he,index_bot]

/-- Every invariant subgroup of the lower tensor module has no nontrivial
fixed point for the chosen source cubic. -/
private theorem source_lower_length (d : Hypothesis D g) (y : D.I g)
    (hy : d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) y) = MatrixOrbit.leftCubic)
    (R : Subgroup G) (hR : R ≤ D.VL) :
    conjugationCubicLength (zpowers (y:G)) R = Nat.log 4 (Nat.card R) := by
  apply length_of_fixed_free
  exact le_bot_iff.mp ((inf_le_inf_right _ hR).trans (source_cubic_fixed_free d y hy).le)

/-- The canonical SourceModuleData determines the contribution above V_L,
with exactly its first multiplicity and the selected literal cubic. -/
private theorem source_upper_length (d : Hypothesis D g)
    [((OrthogonalPlusFour.S₂ D g).subgroupOf (D.S g)).Normal] [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient D g)]
    (f : SourceModuleData d) (y : D.I g) (hy3 : orderOf y = 3)
    (hy : d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) y) = MatrixOrbit.leftCubic) :
    sectionCubicLength (zpowers (y:G)) (OrthogonalPlusFour.S₂ D g) (D.S g) = f.decomposition.leftMultiplicity := by
  let A := zpowers (y:G)
  have hAI : A ≤ D.I g := zpowers_le.mpr y.property
  let π := (moduleProjection d.quotientSymmetricEquiv).comp (inclusion hAI)
  let a : A := ⟨y,mem_zpowers (y:G)⟩
  let c : S₃ := (pairPermEquiv MatrixOrbit.leftCubic).1
  have hcimage : π a = (c,1) := by
    change pairPermEquiv (d.quotientMatrixEquiv (QuotientGroup.mk' _ y)) = (c,1)
    rw [hy]
    apply Prod.ext
    · rfl
    · change (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three) 1 = 1
      exact map_one _
  have hr : ∀ b : A, (π b).2 = 1 := by
    let q := (MonoidHom.snd S₃ S₃).comp (moduleProjection d.quotientSymmetricEquiv)
    have hm : A ≤ q.ker.map (D.I g).subtype := by
      apply zpowers_le.mpr
      exact ⟨y,congrArg Prod.snd hcimage,rfl⟩
    intro b
    obtain ⟨u,hu,he⟩ := hm b.property
    have he' : inclusion hAI b = u := Subtype.ext he.symm
    change q (inclusion hAI b) = 1
    rw [he']
    exact hu
  have hc3 : c^3=1 := by
    have hh : MatrixOrbit.leftCubic^3=1 := by
      apply Prod.ext
      · exact MatrixOrbit.cubic_cube
      · change (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))^3=1
        exact one_pow 3
    have h := congrArg (fun z => (pairPermEquiv z).1) hh
    simp only [map_pow,map_one,Prod.pow_fst] at h
    exact h
  have hcne : c≠1 := by
    intro hc
    have hh : pairPermEquiv MatrixOrbit.leftCubic = 1 := by
      apply Prod.ext
      · exact hc
      · change (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three) 1 = 1
        exact map_one _
    have hz : MatrixOrbit.leftCubic = 1 := pairPermEquiv.injective (hh.trans pairPermEquiv.map_one.symm)
    exact (by decide +kernel : MatrixOrbit.leftCubic ≠ 1) hz
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact ((D.I g).orderOf_coe y).trans hy3)
  have hh := binary_section_length f.conjugation hAI hA
    (d.base.binary_T_isPGroup.to_le d.S_le_T)
  exact hh.trans (product_cubic_length f.decomposition π hr a c hcimage hc3 hcne)

/-- The lower tensor contributes two and the upper natural sum contributes
its same canonical first multiplicity. -/
theorem source_pair_length (d : Hypothesis D g)
    [((OrthogonalPlusFour.S₂ D g).subgroupOf (D.S g)).Normal] [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient D g)]
    (f : SourceModuleData d) (hOmega : omegaCenter D.T ≤ D.VL)
    (y : D.I g) (hy3 : orderOf y = 3)
    (hy : d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) y) = MatrixOrbit.leftCubic) :
    conjugationCubicLength (zpowers (y:G)) (D.S g) = f.decomposition.leftMultiplicity + 2 := by
  have hu := source_upper_length d f y hy3 hy
  have hl := source_lower_length d y hy D.VL le_rfl
  have hc : Nat.card D.VL = 16 := by
    rw [Nat.card_congr d.coordinates.toEquiv]
    change Nat.card (Fin 2 → Fin 2 → ZMod 2) = 16
    simp
  rw [hc,show Nat.log 4 16 = 2 from by decide] at hl
  have hcollapse := (source_collapse d hOmega).2.2.2.2.2
  conv_lhs at hu => rw [hcollapse]
  have hm := conjugationCubicLength_mono (zpowers (y:G))
    (d.central_first_layer.trans inf_le_left)
  unfold sectionCubicLength at hu
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open scoped Pointwise TensorProduct commutatorElement
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The marked product has elementary quotient by the marked intersection. -/
private theorem pair_quotient_elementary (K F X E : Subgroup G)
    (hK : K = F ⊔ X) (hE : E = F ⊓ X)
    (hKF : K ≤ normalizer (F : Set G)) (hKX : K ≤ normalizer (X : Set G))
    (hF : ∀ f ∈ F, f^2 ∈ E) (hX : ∀ x ∈ X, x^2 ∈ E)
    [(E.subgroupOf K).Normal] : IsElementaryAbelian 2 (K ⧸ E.subgroupOf K) := by
  let q := QuotientGroup.mk' (E.subgroupOf K)
  have hFK : F ≤ K := le_sup_left.trans hK.ge
  have hXK : X ≤ K := le_sup_right.trans hK.ge
  have hcomm : ⁅F,X⁆ ≤ E := by
    rw [hE]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp (hXK.trans hKF))
      (le_normalizer_iff_commutator_le_right.mp (hFK.trans hKX))
  have hsquare (a : K ⧸ E.subgroupOf K) : a^2 = 1 := by
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf K) a
    have hk : (k:G) ∈ (F : Set G) * (X : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left F X (hXK.trans hKF),← hK]
      exact k.property
    obtain ⟨f,hf,x,hx,he⟩ := hk
    let fk : K := ⟨f,hFK hf⟩
    let xk : K := ⟨x,hXK hx⟩
    have hk' : fk*xk=k := Subtype.ext he
    have hf2 : (q fk)^2=1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hF f hf)
    have hx2 : (q xk)^2=1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hX x hx)
    have hfx : Commute (q fk) (q xk) := by
      change q fk * q xk = q xk * q fk
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hcomm (commutator_mem_commutator hf hx))
    change (q k)^2=1
    rw [← hk',map_mul,hfx.mul_pow,hf2,hx2,mul_one]
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsquare x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }

/-- The same natural quotient used in G.2.3, on arbitrary literal marked
subgroups. Its proof does not identify the plane V₀ with the seed Z_S. -/
private theorem rank_one_natural_data (J U K F X E : Subgroup G) (y : G)
    (hUJ : U ≤ J) (hKJ : K ≤ J) (hEJ : J ≤ normalizer (E : Set G))
    (hKnorm : J ≤ normalizer (K : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (hF : F = U ⊓ K) (hX : X = F.conjBy y⁻¹)
    (hK : K = F ⊔ X) (hE : E = F ⊓ X) (hy : y ∈ J)
    (hindex : F.relIndex U = 2)
    (hsqF : ∀ f ∈ F, f^2 ∈ E) (hsqX : ∀ x ∈ X, x^2 ∈ E)
    (hUF : ⁅U,F⁆ ≤ E)
    (π : J →* S₃) (hπ : Function.Surjective π) (hk : π.ker = K.subgroupOf J) :
    ∃ (hN : (E.subgroupOf K).Normal), letI := hN
      ∃ (hA : IsElementaryAbelian 2 (K ⧸ E.subgroupOf K)), letI := hA
        ∃ (σ : Representation (ZMod 2) S₃ (Additive (K ⧸ E.subgroupOf K)))
          (_d : Representation.BinaryConjugationSection J K E (σ.comp π)),
          ∃ j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
              Additive (K ⧸ E.subgroupOf K),
            (∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
              (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
                σ a (j z)) ∧
            Nat.card U = 2 ^ (Module.finrank (ZMod 2) (multiplicitySpace σ) + 1) * Nat.card E := by
  have hFK : F ≤ K := le_sup_left.trans hK.ge
  have hXK : X ≤ K := le_sup_right.trans hK.ge
  have hEK : E ≤ K := hE.le.trans (inf_le_left.trans hFK)
  have hKF : K ≤ normalizer (F : Set G) := by
    rw [hF]
    exact (le_inf hKU K.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hKX : K ≤ normalizer (X : Set G) := by
    rw [hX]
    have he : K.map (MulAut.conj y⁻¹).toMonoidHom = K :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (K:Set G)).inv_mem (hKnorm hy))
    have hh := (map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hKF).trans
      (F.le_normalizer_map (MulAut.conj y⁻¹).toMonoidHom)
    rwa [he] at hh
  let hN : (E.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer (hKJ.trans hEJ)
  let hA := pair_quotient_elementary K F X E hK hE hKF hKX hsqF hsqX
  obtain ⟨σ,d,_⟩ := Representation.BinaryConjugationSection.exists_canonical
    J K E hKJ hEK hKnorm hEJ π hπ hk
  have hex : ∃ u ∈ U, u ∉ F := by
    by_contra! hn
    have h1 : F.relIndex U=1 := relIndex_eq_one.mpr hn
    omega
  obtain ⟨u,hu,huf⟩ := hex
  let ui : J := ⟨u,hUJ hu⟩
  have hcard : Nat.card ((U.subgroupOf J).map π) = 2 := by
    rw [← relIndex_ker,hk]
    have he := relIndex_map_map_of_injective (K.subgroupOf J) (U.subgroupOf J) J.subtype_injective
    rw [map_subgroupOf_eq_of_le hKJ,map_subgroupOf_eq_of_le hUJ] at he
    rw [← he,← inf_relIndex_left,← hF]
    exact hindex
  have ht : (π ui)^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨π ui,mem_map_of_mem π hu⟩ : (U.subgroupOf J).map π))
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  have hne : π ui ≠ 1 := by
    intro he
    have huK : ui ∈ K.subgroupOf J := hk ▸ (show ui ∈ π.ker from he)
    exact huf (hF.symm ▸ ⟨hu,huK⟩)
  have hUK : ⁅U,K⁆ ≤ F := by
    rw [hF]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hKU)
      (le_normalizer_iff_commutator_le_right.mp (hUJ.trans hKnorm))
  obtain ⟨⟨j,hj⟩,_⟩ := d.natural_tensor_and_marks_of_subgroup_pair σ π U F X
    ui ⟨y,hy⟩ hu hK hE hX hUF hUK ht hne
  refine ⟨hN,hA,σ,d,j,hj,?_⟩
  have hproduct : (K : Set G) = (F : Set G) * (X : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left F X (hXK.trans hKF),hK]
  have hc := card_set_mul_mul_card_inf F X
  have hXcard : Nat.card X = Nat.card F := by rw [hX]; exact card_map_of_injective (MulAut.conj y⁻¹).injective
  rw [← hproduct,← hE,hXcard] at hc
  change Nat.card K * Nat.card E = Nat.card F * Nat.card F at hc
  have hcardK := d.card_section
  have hd : Nat.card (Additive (K ⧸ E.subgroupOf K)) =
      2 ^ (2 * Module.finrank (ZMod 2) (multiplicitySpace σ)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),← j.finrank_eq,
      Module.finrank_tensorProduct,BinaryPermutation.finrank_core,Nat.card_zmod]
    simp only [Fintype.card_fin]
    congr 1
    omega
  rw [hd] at hcardK
  rw [hcardK] at hc
  have hcardF : Nat.card F = 2 ^ Module.finrank (ZMod 2) (multiplicitySpace σ) * Nat.card E := by
    apply Nat.pow_left_injective (by decide : 2≠0)
    change (Nat.card F)^2 = (2 ^ Module.finrank (ZMod 2) (multiplicitySpace σ) * Nat.card E)^2
    rw [mul_pow,pow_two (Nat.card F),← hc,← pow_mul]
    ring_nf
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) F U bot_le
    (hF.le.trans inf_le_left)
  rw [relIndex_bot_left,relIndex_bot_left,hindex,hcardF] at hi
  rw [← hi,pow_succ]
  ring

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open scoped TensorProduct
variable {G : Type*} [Group G] [Finite G]

/-- The natural multiplicity comparison yields the exact marked intersection
order, with neither its rank nor its cardinality assumed. -/
private theorem rank_one_card_of_lengths (J U K F X E : Subgroup G) (y : G) (s : ℕ)
    (hUJ : U ≤ J) (hKJ : K ≤ J) (hEJ : J ≤ normalizer (E : Set G))
    (hKnorm : J ≤ normalizer (K : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (hF : F = U ⊓ K) (hX : X = F.conjBy y⁻¹)
    (hK : K = F ⊔ X) (hE : E = F ⊓ X) (hy : y ∈ J)
    (hindex : F.relIndex U = 2)
    (hsqF : ∀ f ∈ F, f^2 ∈ E) (hsqX : ∀ x ∈ X, x^2 ∈ E)
    (hUF : ⁅U,F⁆ ≤ E)
    (π : J →* S₃) (hπ : Function.Surjective π) (hk : π.ker = K.subgroupOf J)
    (hK2 : IsPGroup 2 K) (hy3 : orderOf y = 3)
    (hKlength : conjugationCubicLength (zpowers y) K = s+2)
    (hElength : conjugationCubicLength (zpowers y) E = 1)
    (hUcard : Nat.card U = 2^(2*s+5)) : Nat.card E = 2^(s+3) := by
  obtain ⟨hN,hA,σ,d,j,hj,hu⟩ := rank_one_natural_data J U K F X E y hUJ hKJ hEJ
    hKnorm hKU hF hX hK hE hy hindex hsqF hsqX hUF π hπ hk
  let := hN
  let := hA
  let A := zpowers y
  have hAJ : A ≤ J := zpowers_le.mpr hy
  let a : A := ⟨y,mem_zpowers y⟩
  let πA := π.comp (inclusion hAJ)
  have ha3 : (πA a)^3=1 := by
    rw [← map_pow]
    apply (map_one πA).subst
    congr 1
    exact Subtype.ext (hy3 ▸ pow_orderOf_eq_one y)
  have hane : πA a≠1 := by
    intro he
    have hyK : (⟨y,hy⟩ : J) ∈ K.subgroupOf J := hk ▸ (show (⟨y,hy⟩ : J) ∈ π.ker from he)
    have ho : orderOf (⟨y,hyK⟩ : K) = 3 := (K.orderOf_coe ⟨y,hyK⟩).symm.trans hy3
    have hc := hK2.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨y,hyK⟩ : K)
    rw [ho] at hc
    norm_num at hc
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n:=1) (by rw [Nat.card_zpowers,hy3,pow_one])
  have hsection := binary_section_length d hAJ hA3 hK2
  change sectionCubicLength A E K = Nat.log 4 (fixedIndex (σ.comp πA)) at hsection
  have hnatural := tensor_cubic_length σ j hj πA a ha3 hane
  have hr : Module.finrank (ZMod 2) (multiplicitySpace σ) = s+1 := by
    unfold sectionCubicLength at hsection
    rw [hKlength,hElength] at hsection
    omega
  rw [hr,hUcard] at hu
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0<2) : 0<2^(s+1+1))
  rw [← hu,← pow_add]
  congr 1
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
open CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {Z ZS Zperp V Y T : Subgroup G} {g : G}

/-- The order of the original U, retaining the canonical source multiplicity. -/
theorem literal_closure_card
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y=V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) (hΩ : omegaCenter T=Z)
    [((OrthogonalPlusFour.S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal]
    [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)]
    (f : SourceModuleData d)
    (hsame : f.decomposition.leftMultiplicity=f.decomposition.rightMultiplicity) :
    Nat.card (closureU Z ZS) = 2^(2*f.decomposition.leftMultiplicity+5) := by
  let D := Chapter15.setup Z Zperp Y T
  have hΩD : omegaCenter D.T ≤ D.VL := by
    change omegaCenter T ≤ D.VL
    rw [hΩ]
    exact point_le_VL D
  have hl := (source_collapse d hΩD).2.2.2.2.2
  have hcV : Nat.card D.VL = 16 := by
    rw [Nat.card_congr d.coordinates.toEquiv]
    change Nat.card (Fin 2 → Fin 2 → ZMod 2)=16
    simp
  have hp := f.core_card
  have hlcard : Nat.card (OrthogonalPlusFour.S₂ D g)=16 :=
    (congrArg (fun H : Subgroup G => Nat.card H) hl).trans hcV
  have hp' : Nat.card (pairP Z ZS g)=2^(4*f.decomposition.leftMultiplicity+4) := by
    rw [hlcard,← hsame] at hp
    have hs : D.S g=pairP Z ZS g := Chapter15.S_eq g hZS hperp
    conv_lhs at hp => rw [hs]
    rw [hp,show (16:ℕ)=2^4 from rfl,← pow_add]
    congr 1
    omega
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,⟨e⟩,_⟩ := literal_source_collapse hZS hperp hspan d hΩ
  have hfour : Nat.card (pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g : Subgroup G)=4 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Fin 2 → ZMod 2)=4
    simp
  have hprod := (literal_products hZS hperp d).2
  have hw := card_pairW Z ZS g f.decomposition.leftMultiplicity hprod hfour hp'
  have hi := d.W_index_eq_four
  have hu : D.U=closureU Z ZS := Chapter15.closure_eq hZS hperp
  have hmark : D.W g=pairW Z ZS g := Chapter15.W_eq g hZS hperp
  rw [hu,hmark] at hi
  have ht := relIndex_mul_relIndex (⊥ : Subgroup G) (pairW Z ZS g) (closureU Z ZS)
    bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hw,hi] at ht
  rw [← ht,show (4:ℕ)=2^2 from rfl,← pow_add]

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02
open CFSG.Quasithin.ChapterG.Section02.Setup
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
variable {G : Type*} [Group G] [Finite G]
  {Z ZS Zperp V Y T : Subgroup G} {g : G}

/-- The literal E has order 2^(s+3), for the same multiplicity s as the
canonical G.2.6 source module. The marked rank-one quotient and index-two
bridge are the earlier geometric inputs, independent of this comparison. -/
theorem literal_intersectionE_card
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y=V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) (hΩ : omegaCenter T=Z)
    [((OrthogonalPlusFour.S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal]
    [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)]
    (f : SourceModuleData d)
    (hsame : f.decomposition.leftMultiplicity=f.decomposition.rightMultiplicity)
    (y : (Chapter15.setup Z Zperp Y T).I g) (hy3 : orderOf y=3)
    (hymodel : d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 _) y)=MatrixOrbit.leftCubic)
    (V₀ : Subgroup G) (hplane : V₀=Z ⊔ rightConjugate Z (y:G))
    (hV₀U : V₀ ≤ closureU Z ZS) (hyV₀ : (y:G)∈normalizer (V₀:Set G))
    (hdis : Disjoint Z (rightConjugate Z (y:G))) (hV₀card : Nat.card V₀=4)
    (hyJ : (y:G)∈pairI Z ZS (y:G))
    (e : (pairI Z ZS (y:G) ⧸ pCore 2 (pairI Z ZS (y:G))) ≃* S₃)
    (hcore : pairP Z ZS (y:G)=pairI Z ZS (y:G) ⊓ centralizer (V₀:Set G))
    (hbridge : (pairP Z ZS g ⊓ pairI Z ZS (y:G)).relIndex (pairP Z ZS (y:G))=2) :
    Nat.card (intersectionE Z ZS (y:G))=2^(f.decomposition.leftMultiplicity+3) := by
  let D := Chapter15.setup Z Zperp Y T
  let U := closureU Z ZS
  let P := pairP Z ZS g
  let J := pairI Z ZS (y:G)
  let K := pairP Z ZS (y:G)
  let F := intersectionF Z ZS (y:G)
  let X := partnerX Z ZS (y:G)
  let E := intersectionE Z ZS (y:G)
  let A := zpowers (y:G)
  let N := P ⊓ J
  have hu : D.U=U := Chapter15.closure_eq hZS hperp
  have hp : D.S g=P := Chapter15.S_eq g hZS hperp
  have hΩD : omegaCenter D.T ≤ D.VL := by
    change omegaCenter T ≤ D.VL
    rw [hΩ]
    exact point_le_VL D
  have hUH : U ≤ centralizerH Z := by
    rw [← hu]
    exact d.base.U_le_H
  have hZH : ZS ≤ centralizerH Z := (hZS.trans hperp).trans hUH
  have hU2 : IsPGroup 2 U := hu ▸ U_isPGroup d.base d.closure
  have hf : (frattini U).map U.subtype ≤ Z := by
    have hh := d.closure.frattini
    rw [hu] at hh
    exact hh
  have hl := rank_one_intersection_layer Z ZS V₀ (y:G) hZH hU2 hf hplane hV₀U hyV₀ hdis
  have hV₀E : V₀ ≤ E := hl.1
  have hEK : E ≤ K := hl.2.1
  have hJE : J ≤ normalizer (E:Set G) := hl.2.2.1
  have hEJ : ⁅E,J⁆ ≤ V₀ := hl.2.2.2.1
  have hZV₀ : Z ≤ V₀ := by rw [hplane]; exact le_sup_left
  have hZyU : rightConjugate Z (y:G) ≤ U :=
    (show rightConjugate Z (y:G)≤V₀ by rw [hplane]; exact le_sup_right).trans hV₀U
  have hex := PairGeometry.literal_extraspecial hZS hperp hspan d hΩ
  let := hex.1
  have hindex := intersectionF_index Z ZS (y:G) hex.2.1 d.point_card hZyU hdis
  have hF : F=U ⊓ K := intersectionF_eq_pairW Z ZS V₀ (y:G) hZH hplane hcore
  have hK : K=F ⊔ X := partner_core_product Z ZS V₀ Y T (y:G) hZH hplane hcore hyJ e hindex
  have hX : X=F.conjBy (y:G)⁻¹ := rfl
  have hE : E=F ⊓ X := rfl
  have hUJ : U ≤ J := le_sup_left
  have hKJ : K ≤ J := pCoreIn_le 2 J
  have hJnormK : J ≤ normalizer (K:Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  change K=J ⊓ centralizer (V₀:Set G) at hcore
  have hKU : K ≤ normalizer (U:Set G) := by
    rw [hcore]
    exact (inf_le_right.trans (centralizer_le hZV₀)).trans (H_normalizes_closureU Z ZS)
  have hUI : U ≤ D.I g := hu ▸ le_sup_left
  have hJI : J ≤ D.I g := by
    apply sup_le hUI
    rintro _ ⟨u,hu',rfl⟩
    exact (mem_normalizer_iff.mp ((D.I g).le_normalizer ((D.I g).inv_mem y.property)) u).mp (hUI hu')
  have hIP : D.I g ≤ normalizer (P:Set G) := hp ▸ core_normalized D g
  have hP2 : IsPGroup 2 P := hp ▸ d.base.binary_T_isPGroup.to_le d.S_le_T
  have hK2 : IsPGroup 2 K := isPGroup_pCoreIn 2 J
  have hV₀VL : V₀ ≤ D.VL := by
    rw [hplane]
    apply sup_le (point_le_VL D)
    rintro _ ⟨z,hz,rfl⟩
    exact (mem_normalizer_iff.mp (d.I_normalizes_VL ((D.I g).inv_mem y.property)) z).mp
      (point_le_VL D hz)
  have hPVL : P ≤ centralizer (D.VL:Set G) := by
    rw [← hp]
    exact le_centralizer_iff.mp (d.central_first_layer.trans inf_le_right)
  have hPV₀ : P ≤ centralizer (V₀:Set G) := hPVL.trans (centralizer_le hV₀VL)
  have hPJ : P ≤ normalizer (J:Set G) := hPV₀.trans
    (plane_centralizer_normalizes Z ZS V₀ (y:G) hZV₀ hyV₀).1
  have hAJ : A ≤ J := zpowers_le.mpr hyJ
  have hAI : A ≤ D.I g := zpowers_le.mpr y.property
  have hAP : A ≤ normalizer (P:Set G) := hAI.trans hIP
  have hAN : A ≤ normalizer (N:Set G) :=
    (le_inf hAP (hAJ.trans J.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hNK : N ≤ K := le_pCoreIn_of_normalizes (hP2.to_le inf_le_left) inf_le_right
    ((le_inf (hJI.trans hIP) J.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n:=1) (by
    rw [Nat.card_zpowers,pow_one]
    exact ((D.I g).orderOf_coe y).trans hy3)
  have hNP : (N.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf P.le_normalizer hPJ).trans inf_normalizer_le_normalizer_inf)
  have hNKnormal : (N.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf ((hKJ.trans hJI).trans hIP) (hKJ.trans J.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf)
  let := hNP
  let := hNKnormal
  have hcomm : ⁅A,P⁆ ≤ N := le_inf
    (le_normalizer_iff_commutator_le_right.mp hAP)
    ((commutator_mono hAJ le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hPJ))
  have hpLength := length_eq_of_commutator_le A P N hA3 hP2 inf_le_left hAP hAN hcomm
  have hkLength := length_eq_of_index_two A K N hA3 hK2 hNK (hAJ.trans hJnormK) hAN hbridge
  have hsource := source_pair_length d f hΩD y hy3 hymodel
  conv_lhs at hsource => rw [hp]
  have hKL : conjugationCubicLength A K=f.decomposition.leftMultiplicity+2 :=
    hkLength.trans (hpLength.symm.trans hsource)
  have hE2 : IsPGroup 2 E := hK2.to_le hEK
  have hEV₀ : E ≤ normalizer (V₀:Set G) := by
    let := hl.2.2.2.2
    have hEE : E ≤ centralizer (E:Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
    exact (hEE.trans (centralizer_le hV₀E)).trans (Subgroup.centralizer_le_normalizer _)
  have hAV₀ : A ≤ normalizer (V₀:Set G) := zpowers_le.mpr hyV₀
  let hV₀N : (V₀.subgroupOf E).Normal := normal_subgroupOf_of_le_normalizer hEV₀
  have hEl := length_eq_of_commutator_le A E V₀ hA3 hE2 hV₀E (hAJ.trans hJE) hAV₀
    (by rw [commutator_comm]; exact (commutator_mono le_rfl hAJ).trans hEJ)
  have hV₀l := source_lower_length d y hymodel V₀ hV₀VL
  rw [hV₀card,show Nat.log 4 4=1 from by decide] at hV₀l
  have hEL : conjugationCubicLength A E=1 := hEl.trans hV₀l
  have hsqU (u : G) (hu' : u∈U) : u^2∈Z := by
    let : Fact (IsPGroup 2 U) := ⟨hU2⟩
    exact hf (mem_map_of_mem U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨u,hu'⟩:U)))
  have hsqF (u : G) (hu' : u∈F) : u^2∈E := hV₀E (hZV₀ (hsqU u hu'.1))
  have hsqX (x : G) (hx : x∈X) : x^2∈E := by
    obtain ⟨u,hu',rfl⟩ := hx
    have hh := mem_map_of_mem (MulAut.conj (y:G)⁻¹).toMonoidHom (hsqU u hu'.1)
    apply hV₀E
    apply (show rightConjugate Z (y:G)≤V₀ by rw [hplane]; exact le_sup_right)
    change ((MulAut.conj (y:G)⁻¹).toMonoidHom u)^2 ∈ Z.map (MulAut.conj (y:G)⁻¹).toMonoidHom
    rw [← map_pow]
    exact hh
  have hUF : ⁅U,F⁆≤E := ((commutator_mono le_rfl (show F≤U from inf_le_left)).trans
    (derived_le_of_frattini_image_le hU2 hf)).trans (hZV₀.trans hV₀E)
  let π : J →* S₃ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : π.ker=K.subgroupOf J := by
    ext j
    change e (QuotientGroup.mk' (pCore 2 J) j)=1 ↔ (j:G)∈J.pCoreIn 2
    constructor
    · intro he
      have hj : j ∈ pCore 2 J := (QuotientGroup.eq_one_iff _).mp
        (e.injective (he.trans e.map_one.symm))
      exact mem_map_of_mem J.subtype hj
    · rintro ⟨u,hu',he⟩
      have hj : j ∈ pCore 2 J := (Subtype.ext he : u=j) ▸ hu'
      have hq : QuotientGroup.mk' (pCore 2 J) j=1 := (QuotientGroup.eq_one_iff _).mpr hj
      rw [hq,map_one]
  exact rank_one_card_of_lengths J U K F X E (y:G) f.decomposition.leftMultiplicity
    hUJ hKJ hJE hJnormK hKU hF hX hK hE hyJ hindex hsqF hsqX hUF π hπ hk hK2
    (((D.I g).orderOf_coe y).trans hy3) hKL hEL
    (literal_closure_card hZS hperp hspan d hΩ f hsame)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
