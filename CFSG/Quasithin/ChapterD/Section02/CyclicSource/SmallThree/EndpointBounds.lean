module
public import Theory.Representation.FaithfulSixteenPGroupNine
public import Theory.Representation.InvertedOddSupportRank
public import Theory.GroupAction.IndependentCoprimeSupports
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Theory.GroupTheory.OddInvolutionNormalizer
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportPermutation
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.Defs
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.CyclicFixedRank

/-!
# Bounding and normalizing the canonical cubic support factors

An involution of binary displacement rank at most two inverts an odd
commutator whose support has at most sixteen vectors. Faithfulness bounds
its elementary three-group by nine. A cyclic fixed subgroup has order at
most three, so the original normal elementary group has order at most 27.

A transposition of canonical support factors supplies a diagonal fixed
cubic subgroup. Any third factor is fixed and independent, contradicting
the cyclic centralizer. Thus in the three-factor case every small-support
involution normalizes all factors. The final theorem applies the order
bound to the literal linear support-factor multiplication map.

Source: Aschbacher--Smith, D.2.25, printed p.190.
-/

open scoped IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.ChapterD.CyclicSource.SmallThree

private theorem card_le_nine_of_small_binary_action
    {A W : Type*} [Group A] [Finite A] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction A W] [FaithfulSMul A W]
    (hA : IsPGroup 3 A) (hW : Nat.card W ≤ 16) : Nat.card A ≤ 9 := by
  classical
  let ρ := Representation.ofElementaryAbelianAction (A := A) (G := W) (p := 2)
  have hi : Function.Injective ρ.asGroupHom := by
    intro a b hab
    apply FaithfulSMul.eq_of_smul_eq_smul (α := W)
    intro w
    apply Additive.ofMul.injective
    exact LinearMap.congr_fun (congrArg Units.val hab) (Additive.ofMul w)
  let n := Module.finrank (ZMod 2) (Additive W)
  have hn : n ≤ 4 := by
    have hc : 2 ^ n ≤ 2 ^ 4 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
      rw [Nat.card_zmod] at hh
      rw [← hh, Nat.card_congr Additive.toMul]
      exact hW
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  let b := Module.finBasis (ZMod 2) (Additive W)
  let f : A →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hd := Subgroup.card_dvd_of_injective f
    ((Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hi)
  obtain ⟨r,hr⟩ := hA.exists_card_eq
  have hbad : ¬ 27 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
    have hnone : ∀ k : ℕ, k ≤ 4 →
        ¬ 27 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod 2)) := by
      intro k hk
      interval_cases k <;> rw [Matrix.card_GL_field] <;>
        norm_num [Fin.prod_univ_succ]
    exact hnone n hn
  have hrle : r ≤ 2 := by
    by_contra hh
    apply hbad
    exact (Nat.pow_dvd_pow 3 (show 3 ≤ r by omega)).trans (hr ▸ hd)
  rw [hr]
  exact Nat.pow_le_pow_right (by decide) hrle


/-- The elementary three-core has rank at most three once a rank-two
involution has cyclic centralizer in it. -/
public theorem normal_elementary_three_card_le
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V] [FaithfulSMul G V]
    (P : Subgroup G) [P.Normal] [IsElementaryAbelian 3 P]
    (t : G) (ht : IsInvolution t)
    (hsmall : Nat.card (commutatorAction (zpowers t) V) ≤ 4)
    (hcyclic : IsCyclic (P ⊓ centralizer ({t} : Set G) : Subgroup G)) :
    Nat.card P ≤ 27 := by
  let T := zpowers t
  let D := ⁅P,T⁆
  let C := P ⊓ centralizer ({t} : Set G)
  have hDP : D ≤ P := commutator_le_left P T
  let : IsElementaryAbelian 3 D := IsElementaryAbelian.of_injective
    (inclusion hDP) (inclusion_injective _)
  let : IsElementaryAbelian 3 C := IsElementaryAbelian.of_injective
    (inclusion (show C ≤ P from inf_le_left)) (inclusion_injective _)
  have hodd (H : Subgroup G) [IsElementaryAbelian 3 H] : Odd (Nat.card H) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 H).exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  have hDinv : ∀ x ∈ D, t*x*t⁻¹=x⁻¹ := by
    let : MulDistribMulAction G P := MulDistribMulAction.compHom P
      (MulAut.conjNormal : G →* MulAut P)
    have hm : (commutatorAction T P).map P.subtype = D :=
      commutatorAction_subgroup_conj_map_eq_commutator P T le_normalizer_of_normal
    intro x hx
    obtain ⟨r,hr,rfl⟩ := (mem_map.mp (hm.symm ▸ hx))
    exact congrArg Subtype.val
      (Theory.GroupTheory.involution_inverts_abelian_action_commutator t ht r hr)
  let W := commutatorAction D V
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    W.subtype W.subtype_injective
  let : IsInvariant D V W := commutatorAction_isInvariant
  have hcop : Nat.Coprime (Nat.card D) (Nat.card V) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact (hodd D).coprime_two_right.pow_right n
  let : FaithfulSMul D W := faithfulSMul_iff.mpr (by
    intro x hx
    apply Subtype.ext
    exact ActionSupport.eq_one_of_fixes_support D hcop x (fun v hv =>
      congrArg Subtype.val (hx ⟨v,hv⟩)))
  have hW : Nat.card W ≤ 16 := by
    obtain ⟨heq,_,hle⟩ := invertedOddSubgroup_support_card_data (W := V) D (hodd D) t ht hDinv
    have hb := (Subgroup.card_le_of_le hle).trans hsmall
    change Nat.card W = _ at heq
    rw [heq]
    exact (Nat.pow_le_pow_left hb 2).trans (by decide)
  have hDcard := card_le_nine_of_small_binary_action (A := D)
    (W := W) (IsElementaryAbelian.isPGroup 3 D) hW
  let : IsCyclic C := hcyclic
  have hCcard : Nat.card C ≤ 3 := by
    apply Nat.le_of_dvd (by decide)
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 3 C
  have hsplit : P = D ⊔ C := by
    have hh := eq_commutator_sup_centralizer_of_solvable_coprime P T
      le_normalizer_of_normal
      (Group.isSolvable_of_comm (fun x y : P => mul_comm x y))
      (show Nat.Coprime (Nat.card T) (Nat.card P) by
        rw [Nat.card_zpowers, orderOf_eq_prime ht.2 ht.1]
        exact (hodd P).coprime_two_left)
    simpa only [D, C, T, zpowers_eq_closure, centralizer_closure] using hh
  have hn : C ≤ normalizer (D : Set G) := by
    apply (show C ≤ centralizer (D : Set G) from ?_).trans (centralizer_le_normalizer _)
    intro c hc
    apply mem_centralizer_iff.mpr
    intro d hd
    exact congrArg Subtype.val (mul_comm (⟨d,hDP hd⟩ : P) ⟨c,hc.1⟩)
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes D C hn
  rw [← hsplit] at hp
  have hi : 1 ≤ Nat.card (D ⊓ C : Subgroup G) := Nat.card_pos
  nlinarith


/-- A transposition of the canonical factors creates a diagonal cubic fixed
subgroup. A third fixed factor then contradicts cyclicity of the centralizer. -/
public theorem factors_normalized_of_three_le
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V] [FaithfulSMul G V]
    (P : Subgroup G) [IsElementaryAbelian 3 P]
    (hYP : smallSupportGroup G V 1 ≤ P)
    (t : G) (ht : IsInvolution t)
    (hsmall : Nat.card (commutatorAction (zpowers t) V) = 4)
    (hcyclic : IsCyclic (P ⊓ centralizer ({t} : Set G) : Subgroup G))
    (hthree : 3 ≤ Nat.card (smallSupportFactors G V 1)) :
    ∀ X ∈ smallSupportFactors G V 1, t ∈ normalizer (X : Set G) := by
  classical
  rcases smallSupportFactors_normalized_or_single_transposition t ht hsmall with h | h
  · exact h
  obtain ⟨X,Y,hXY,hX,hY,hrest,_⟩ := h
  obtain ⟨Z,hZX,hZY⟩ := ENat.exists_ne_ne_of_three_le
    (α := smallSupportFactors G V 1)
    (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast hthree) X Y
  have hle (F : smallSupportFactors G V 1) : F.val ≤ P :=
    (le_sSup F.property).trans hYP
  let C := P ⊓ centralizer ({t} : Set G)
  let : IsElementaryAbelian 3 C := IsElementaryAbelian.of_injective
    (inclusion (show C ≤ P from inf_le_left)) (inclusion_injective _)
  let : IsCyclic C := hcyclic
  have hCcard : Nat.card C ≤ 3 := by
    apply Nat.le_of_dvd (by decide)
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 3 C
  have hZC : Z.val ≤ C := by
    intro z hz
    refine ⟨hle Z hz,mem_centralizer_singleton_iff.mpr ?_⟩
    exact (mem_centralizer_iff.mp (hrest Z hZX hZY).2.1 z hz)
  have hCZ : C = Z.val := (eq_of_le_of_card_ge hZC (by
    have hh : Nat.card Z.val = 3 := Z.property.2.1
    omega)).symm
  have hnormX : X.val.conjBy t = Y.val := congrArg Subtype.val hX
  have hind := (smallSupportFactors_internalDirectProduct (G := G) (V := V) (Or.inl rfl)).1
  have hXrest : Disjoint X.val (Y.val ⊔ Z.val) := by
    apply (hind X).mono_right
    refine sup_le ?_ ?_
    · exact le_iSup_of_le Y (le_iSup_of_le hXY.symm le_rfl)
    · exact le_iSup_of_le Z (le_iSup_of_le hZX le_rfl)
  have hXbot : X.val = ⊥ := by
    apply bot_unique
    intro x hx
    have hconj : t*x*t⁻¹ ∈ Y.val := by
      rw [← hnormX]
      exact mem_map.mpr ⟨x,hx,rfl⟩
    have hcomm : Commute x (t*x*t⁻¹) := by
      exact congrArg Subtype.val (mul_comm (⟨x,hle X hx⟩ : P) ⟨_,hle Y hconj⟩)
    have hc : x*(t*x*t⁻¹) ∈ C := by
      refine ⟨P.mul_mem (hle X hx) (hle Y hconj),?_⟩
      apply mem_centralizer_singleton_iff.mpr
      have htt : t*t=1 := by simpa only [pow_two] using ht.2
      have hconjtwice : t*(t*x*t⁻¹)*t⁻¹=x := by
        have := congrArg (fun q : G => q*x*q⁻¹) htt
        simpa only [mul_inv_rev, mul_assoc, one_mul, mul_one, inv_one] using this
      have hcj : t*(x*(t*x*t⁻¹))*t⁻¹=x*(t*x*t⁻¹) := by
        calc
          t*(x*(t*x*t⁻¹))*t⁻¹ = (t*x*t⁻¹)*(t*(t*x*t⁻¹)*t⁻¹) := by group
          _ = (t*x*t⁻¹)*x := by rw [hconjtwice]
          _ = x*(t*x*t⁻¹) := hcomm.eq.symm
      exact (mul_inv_eq_iff_eq_mul.mp hcj).symm
    have hz : x*(t*x*t⁻¹) ∈ Z.val := hCZ ▸ hc
    have hxrest : x ∈ Y.val ⊔ Z.val := by
      have hh := (Y.val ⊔ Z.val).mul_mem (mem_sup_right hz)
        ((Y.val ⊔ Z.val).inv_mem (mem_sup_left hconj))
      simpa only [mul_inv_cancel_right] using hh
    exact hXrest.le_bot ⟨hx,hxrest⟩
  have hh := X.property.2.1
  rw [hXbot,card_bot] at hh
  norm_num at hh


/-- The actual linear support factors in D.2.25 number at most three. -/
public theorem supportFactors_size_le_three
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (P : Subgroup G) [P.Normal] [IsElementaryAbelian 3 P]
    {s : ℕ} (d : FittingConfigurations.SupportFactors ρ P s)
    (t : G) (ht : IsInvolution t)
    (hsmall : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2)
    (hcyclic : IsCyclic (P ⊓ centralizer ({t} : Set G) : Subgroup G)) : s ≤ 3 := by
  classical
  let := Representation.BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := Representation.BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := Representation.BinaryGroupAction.faithful ρ hf
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hcard := normal_elementary_three_card_le (V := Multiplicative V) P t ht
    (show Nat.card (commutatorAction (zpowers t) (Multiplicative V)) ≤ 4 by
      rw [Representation.BinaryGroupAction.commutator_card,
        Representation.CyclicFixedRank.commutator_eq_range]
      exact Nat.pow_le_pow_right (by decide) hsmall) hcyclic
  have hp : Nat.card P = 3 ^ s := by
    rw [← Nat.card_congr (Equiv.ofBijective _ d.multiply_bijective), Nat.card_pi]
    simp only [d.card_factor, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hp] at hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp hcard

end CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
