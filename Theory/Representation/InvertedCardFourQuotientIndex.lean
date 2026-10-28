module

public import Theory.Representation.InvertedOddElement
public import Mathlib.GroupTheory.GroupAction.OfQuotient

/-!
# The card-four fixed-point quotient index

Suppose an involution `x` inverts an odd-order element `a` on a finite
elementary abelian `2`-group `V`.  This module proves the strengthened index
bound used in the card-four branch of Stellmacher's Lemma (1.3): if
`|[V,⟨a⟩]| = 4` and `|V| ≤ 4 |C_V(x)|`, then the induced involution on
`C_V(a)` has fixed-point index at most two.

The proof applies coprime action to split `V` as
`C_V(a) × [V,⟨a⟩]`.  Inversion makes both factors `x`-stable.  The
involution cannot act trivially on the four-element commutator factor:
otherwise its inversion relation would make the odd-order generator act
trivially there, contradicting the coprime decomposition.  Its fixed subgroup
on that factor therefore has order two.  Taking fixed points in the direct
product and cancelling this factor sharpens the original index bound from
four to two.  The quotient-group action on `C_V(a)` is the canonical one.

Source: `refs/latex/stellmacher-n-group.tex`, proof of Lemma (1.3), the
card-four central-element quotient step (journal pp. 15--16; LaTeX lines
323--334).
-/

open scoped IsMulCommutative

universe u v

private theorem elementaryAbelian_subgroup_local
    {V : Type v} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U where
  toIsMulCommutative :=
    ⟨⟨fun x y => Subtype.ext
      (show (x : V) * (y : V) = (y : V) * (x : V) from
        (IsMulCommutative.is_comm (M := V)).comm x y)⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro z
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (z : V)

private theorem cardTwo_fixed_commutator_card_data
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [Nontrivial V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x : G) (hx : IsInvolution x) (hcardG : Nat.card G = 2) :
    Nat.card V = Nat.card (FixedPoints.subgroup G V) *
        Nat.card (commutatorAction G V) ∧
      commutatorAction G V ≤ FixedPoints.subgroup G V := by
  classical
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  let d : V →* V :=
    { toFun := fun w => w⁻¹ * (x • w)
      map_one' := by simp
      map_mul' := by
        intro w z
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hker : d.ker = FixedPoints.subgroup G V := by
    ext w
    constructor
    · intro hw
      rw [FixedPoints.mem_subgroup]
      intro r
      have hwx : x • w = w := by
        exact (eq_of_inv_mul_eq_one (MonoidHom.mem_ker.mp hw)).symm
      by_cases hr : r = 1
      · simp [hr]
      · obtain ⟨z, _hzne, hzuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : G)).mp hcardG
        have hre : r = x := (hzuniq r hr).trans (hzuniq x hx.1).symm
        simpa [hre] using hwx
    · intro hw
      rw [MonoidHom.mem_ker]
      have hwx := (FixedPoints.mem_subgroup (M := G) (a := w)).1 hw x
      exact inv_mul_eq_one.mpr hwx.symm
  have hrange : d.range = commutatorAction G V := by
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨w, rfl⟩
      change w⁻¹ * (x • w) ∈ commutatorAction G V
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨x, w, rfl⟩
    · rw [commutatorAction_eq_closure]
      refine (Subgroup.closure_le (K := d.range)).2 ?_
      intro z hz
      rcases hz with ⟨r, w, rfl⟩
      by_cases hr : r = 1
      · subst r
        exact ⟨1, by simp [d]⟩
      · obtain ⟨z, _hzne, hzuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : G)).mp hcardG
        have hre : r = x := (hzuniq r hr).trans (hzuniq x hx.1).symm
        exact ⟨w, by simp [d, hre]⟩
  have hrange_le_ker : d.range ≤ d.ker := by
    intro z hz
    rcases hz with ⟨w, rfl⟩
    rw [MonoidHom.mem_ker]
    have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
    have hxx : x * x = 1 := by simpa [pow_two] using hx.2
    have hexp : Monoid.exponent V = 2 := IsElementaryAbelian.exponent_eq_prime
    have hinvself (y : V) : y⁻¹ = y :=
      inv_eq_self_of_exponent_two hexp y
    have hpow2 (y : V) : y * y = 1 := by
      have h := Monoid.pow_exponent_eq_one y
      rw [hexp] at h
      simpa [pow_two] using h
    change
      ((w⁻¹ * (x • w))⁻¹ *
        (x • (w⁻¹ * (x • w)))) = 1
    simp only [mul_inv_rev, smul_mul', smul_inv', ← mul_smul, hxx, one_smul]
    simp_rw [hinvself]
    calc
      (x • w) * w * ((x • w) * w) =
          (w * w) * ((x • w) * (x • w)) := by ac_rfl
      _ = 1 := by rw [hpow2, hpow2, one_mul]
  constructor
  · calc
      Nat.card V = Nat.card d.ker * d.ker.index := d.ker.card_mul_index.symm
      _ = Nat.card d.ker * Nat.card d.range := by rw [Subgroup.index_ker]
      _ = Nat.card (FixedPoints.subgroup G V) *
          Nat.card (commutatorAction G V) := by rw [hker, hrange]
  · simpa [hker, hrange] using hrange_le_ker

/-- In the card-four branch for an inverted odd element, passage to its
fixed-point module improves the involution fixed-point index from four to two. -/
public theorem invertedOddElement_cardFour_fixedPointQuotient_index_le_two
    {G : Type u} {V : Type v} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (a x : G) (_ha : a ≠ 1) (haodd : Nat.Coprime 2 (orderOf a))
    (hx : IsInvolution x) (hinv : x * a * x⁻¹ = a⁻¹)
    (hAnorm : (Subgroup.zpowers a).Normal)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers a) V) = 4)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V)) :
    letI : (Subgroup.zpowers a).Normal := hAnorm
    let q : G →* G ⧸ Subgroup.zpowers a :=
      QuotientGroup.mk' (Subgroup.zpowers a)
    let C : Subgroup V := FixedPoints.subgroup (Subgroup.zpowers a) V
    let xbar : G ⧸ Subgroup.zpowers a := q x
    Nat.card C ≤
      2 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers xbar) C) := by
  classical
  let A : Subgroup G := Subgroup.zpowers a
  let hAnorm' : A.Normal := by simpa [A] using hAnorm
  let : A.Normal := hAnorm'
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let C : Subgroup V := FixedPoints.subgroup A V
  let W : Subgroup V := commutatorAction A V
  let R : Subgroup G := Subgroup.zpowers x
  let xbar : G ⧸ A := q x
  let Rbar : Subgroup (G ⧸ A) := Subgroup.zpowers xbar
  let aa : A := ⟨a, Subgroup.mem_zpowers a⟩
  let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hcardR : Nat.card R = 2 := by
    simpa [R, Nat.card_zpowers] using hxorder
  obtain ⟨n, hcardV⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hcardA : Nat.card A = orderOf a := by simp [A, Nat.card_zpowers]
  have hcopAV : Nat.Coprime (Nat.card A) (Nat.card V) := by
    rw [hcardA, hcardV]
    exact haodd.symm.pow_right n
  have hcompl : IsCompl C W :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := A)
      (Group.isSolvable_of_comm fun y z =>
        (IsMulCommutative.is_comm (M := V)).comm y z)
      hcopAV (inferInstance : IsMulCommutative V)
  let hWnorm : W.Normal := Subgroup.normal_of_isMulCommutative W
  let : W.Normal := hWnorm
  have hCWcomp : C.IsComplement' W := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hcompl.disjoint
    rw [← Subgroup.mul_normal C W, hcompl.sup_eq_top]
    rfl
  have hconjA (r : A) : x * (r : G) * x⁻¹ ∈ A := by
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp r.property
    have hz' : x * (r : G) * x⁻¹ = (a⁻¹) ^ z := by
      calc
        x * (r : G) * x⁻¹ = x * a ^ z * x⁻¹ := by rw [hz]
        _ = (x * a * x⁻¹) ^ z := conj_zpow.symm
        _ = (a⁻¹) ^ z := by rw [hinv]
    rw [hz']
    exact A.zpow_mem (A.inv_mem (Subgroup.mem_zpowers a)) z
  have hxWforward (w : V) (hw : w ∈ W) : x • w ∈ W := by
    change w ∈ commutatorAction A V at hw
    change x • w ∈ commutatorAction A V
    rw [commutatorAction_eq_closure] at hw ⊢
    refine Subgroup.closure_induction
      (p := fun z _ => x • z ∈
        Subgroup.closure {z : V | ∃ r : A, ∃ v : V, z = v⁻¹ * (r • v)})
      ?_ ?_ ?_ ?_ hw
    · intro z hz
      rcases hz with ⟨r, v, rfl⟩
      refine Subgroup.subset_closure
        ⟨⟨x * (r : G) * x⁻¹, hconjA r⟩, x • v, ?_⟩
      change x • (v⁻¹ * ((r : G) • v)) =
        (x • v)⁻¹ * ((x * (r : G) * x⁻¹) • (x • v))
      simp [smul_mul', smul_smul, mul_assoc]
    · simp
    · intro y z _hy _hz hy hz
      simpa [smul_mul'] using Subgroup.mul_mem _ hy hz
    · intro y _hy hy
      simpa [smul_inv'] using Subgroup.inv_mem _ hy
  have hWforward (r : R) (w : V) (hw : w ∈ W) : (r : G) • w ∈ W := by
    by_cases hr : r = 1
    · simp [hr, hw]
    · obtain ⟨z, _hzne, hzuniq⟩ :=
        (Nat.card_eq_two_iff' (1 : R)).mp hcardR
      have hrxne : rx ≠ 1 := by
        intro h
        exact hx.1 (congrArg Subtype.val h)
      have hre : r = rx := (hzuniq r hr).trans (hzuniq rx hrxne).symm
      simpa [hre, rx] using hxWforward w hw
  let hWinv : IsInvariant R V W := ⟨by
    intro r w
    constructor
    · exact hWforward r w
    · intro hw
      have := hWforward r⁻¹ ((r : G) • w) hw
      simpa [inv_smul_smul] using this⟩
  let : IsInvariant R V W := hWinv
  let hWelem : IsElementaryAbelian 2 W := elementaryAbelian_subgroup_local W
  let : IsElementaryAbelian 2 W := hWelem
  let hAWinv : IsInvariant A V W := commutatorAction_isInvariant
  let : IsInvariant A V W := hAWinv
  have hcardW : Nat.card W = 4 := by simpa [W, A] using hcard
  have hWne : W ≠ ⊥ := by
    intro hW
    have : Nat.card W = 1 := Subgroup.card_eq_one.mpr hW
    omega
  let : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hWne
  have hcommRWne : commutatorAction R W ≠ ⊥ := by
    intro hcommbot
    have htrivR : ActsTrivially (A := R) (G := W) :=
      actsTrivially_of_commutatorAction_eq_bot (G := W) (A := R) hcommbot
    have hxfix (w : W) : rx • w = w := htrivR rx w
    let rho : A →* MulAut W := MulDistribMulAction.toMulAut A W
    let y : MulAut W := rho aa
    have hyinv : y = y⁻¹ := by
      apply DFunLike.ext _ _
      intro w
      have hax : a * x = x * a⁻¹ := by
        have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
        have hxx : x * x = 1 := by simpa [pow_two] using hx.2
        calc
          a * x = (x * x) * a * x := by rw [hxx, one_mul]
          _ = x * (x * a * x⁻¹) := by rw [hxinv]; group
          _ = x * a⁻¹ := by rw [hinv]
      have hrel : aa • (rx • w) = rx • (aa⁻¹ • w) := by
        apply Subtype.ext
        change a • (x • (w : V)) = x • (a⁻¹ • (w : V))
        simpa [← mul_smul] using congrArg (fun g : G => g • (w : V)) hax
      rw [hxfix w, hxfix (aa⁻¹ • w)] at hrel
      simpa [y, rho, MulDistribMulAction.toMulAut_apply] using hrel
    have hy2 : y ^ 2 = 1 := by
      rw [pow_two]
      exact (congrArg (fun z : MulAut W => z * y) hyinv).trans (inv_mul_cancel y)
    have hyOrderDvdTwo : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    have hyOrderDvdA : orderOf y ∣ orderOf a := by
      have h := orderOf_map_dvd rho aa
      rw [← Subgroup.orderOf_coe aa] at h
      exact h
    have hyOrder : orderOf y = 1 :=
      Nat.eq_one_of_dvd_coprimes haodd hyOrderDvdTwo hyOrderDvdA
    have hyone : y = 1 := orderOf_eq_one_iff.mp hyOrder
    have haaFix (w : W) : aa • w = w := by
      have := DFunLike.congr_fun hyone w
      simpa [y, rho, MulDistribMulAction.toMulAut_apply] using this
    have hfixedA (w : W) : (w : V) ∈ FixedPoints.subgroup A V := by
      rw [FixedPoints.mem_subgroup]
      intro r
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp r.property
      have haafix : aa ^ z • w = w := by
        exact MulAction.mem_fixedBy_zpow (MulAction.mem_fixedBy.mpr (haaFix w)) z
      have haar : aa ^ z = r := by
        apply Subtype.ext
        simpa [aa] using hz
      have haafix' := congrArg Subtype.val haafix
      change ((aa ^ z : A) : G) • (w : V) = (w : V) at haafix'
      rw [haar] at haafix'
      exact haafix'
    have hWbot : W = ⊥ := by
      apply eq_bot_iff.mpr
      intro w hw
      have hwinf : w ∈ C ⊓ W := ⟨hfixedA ⟨w, hw⟩, hw⟩
      rw [hcompl.inf_eq_bot] at hwinf
      simpa using hwinf
    exact hWne hWbot
  have hrxne : rx ≠ 1 := by
    intro h
    exact hx.1 (congrArg Subtype.val h)
  have hrxSq : rx ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hx.2
  have hrx : IsInvolution rx := ⟨hrxne, hrxSq⟩
  obtain ⟨hcardWdecomp, hcommWle⟩ :=
    cardTwo_fixed_commutator_card_data (V := W) rx hrx hcardR
  have hcardCommWle : Nat.card (commutatorAction R W) ≤
      Nat.card (FixedPoints.subgroup R W) := Subgroup.card_le_of_le hcommWle
  have hcardCommWne : Nat.card (commutatorAction R W) ≠ 1 := by
    intro h
    exact hcommRWne (Subgroup.card_eq_one.mp h)
  have hcardFixW : Nat.card (FixedPoints.subgroup R W) = 2 := by
    have heq : 4 = Nat.card (FixedPoints.subgroup R W) *
        Nat.card (commutatorAction R W) := hcardW.symm.trans hcardWdecomp
    have hcommDvdFour : Nat.card (commutatorAction R W) ∣ 4 :=
      ⟨Nat.card (FixedPoints.subgroup R W), by simpa [mul_comm] using heq⟩
    have hcommLeFour : Nat.card (commutatorAction R W) ≤ 4 :=
      Nat.le_of_dvd (by norm_num) hcommDvdFour
    have hcommEven : 2 ∣ Nat.card (commutatorAction R W) := by
      have hP : IsPGroup 2 (commutatorAction R W) :=
        (IsElementaryAbelian.isPGroup 2 W).to_subgroup _
      exact hP.card_eq_or_dvd.resolve_left hcardCommWne
    obtain ⟨k, hk⟩ := hcommEven
    have hcommPos : 0 < Nat.card (commutatorAction R W) := Nat.card_pos
    have hcases : Nat.card (commutatorAction R W) = 2 ∨
        Nat.card (commutatorAction R W) = 4 := by omega
    rcases hcases with htwo | hfour
    · rw [htwo] at heq
      omega
    · rw [hfour] at heq hcardCommWle
      omega
  let D : Subgroup C := FixedPoints.subgroup Rbar C
  let E : Subgroup W := FixedPoints.subgroup R W
  let P : Subgroup V := FixedPoints.subgroup R V
  let f : D × E → P := fun z => ⟨((z.1 : C) : V) * ((z.2 : W) : V), by
    rw [FixedPoints.mem_subgroup]
    intro r
    by_cases hr : r = 1
    · simp [hr]
    · obtain ⟨y, _hyne, hyuniq⟩ :=
        (Nat.card_eq_two_iff' (1 : R)).mp hcardR
      have hre : r = rx := (hyuniq r hr).trans (hyuniq rx hrxne).symm
      let rxbar : Rbar := ⟨xbar, Subgroup.mem_zpowers xbar⟩
      have hd := (FixedPoints.mem_subgroup (M := Rbar) (a := (z.1 : C))).mp
        z.1.property rxbar
      have he := (FixedPoints.mem_subgroup (M := R) (a := (z.2 : W))).mp
        z.2.property rx
      have hd' : x • ((z.1 : C) : V) = ((z.1 : C) : V) := by
        exact congrArg Subtype.val (by simpa [rxbar, xbar, q] using hd)
      have he' : x • ((z.2 : W) : V) = ((z.2 : W) : V) := by
        have heV := congrArg Subtype.val he
        change (rx : R) • ((z.2 : W) : V) = ((z.2 : W) : V) at heV
        simpa [rx] using heV
      change (r : G) • (((z.1 : C) : V) * ((z.2 : W) : V)) = _
      rw [hre]
      change x • (((z.1 : C) : V) * ((z.2 : W) : V)) = _
      rw [smul_mul', hd', he']⟩
  have hf_inj : Function.Injective f := by
    intro z z' hzz'
    have hpairs : ((z.1 : C), (z.2 : W)) = ((z'.1 : C), (z'.2 : W)) := by
      apply hCWcomp.1
      exact congrArg Subtype.val hzz'
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hpairs
    · apply Subtype.ext
      exact congrArg Prod.snd hpairs
  have hf_surj : Function.Surjective f := by
    intro z
    obtain ⟨⟨c0, w0⟩, hcw0⟩ := hCWcomp.2 (z : V)
    let c : C := ⟨(c0 : V), c0.property⟩
    let w : W := ⟨(w0 : V), w0.property⟩
    have hcw : (c : V) * (w : V) = (z : V) := hcw0
    have hzfixx : x • (z : V) = (z : V) := by
      have := (FixedPoints.mem_subgroup (M := R) (a := (z : V))).mp z.property rx
      simpa [rx] using this
    have hcxmem : x • (c : V) ∈ C := by
      exact ((xbar • c : C)).property
    have hxwmem : x • (w : V) ∈ W := hWforward rx w w.property
    have hpairs :
        ((⟨x • (c : V), hcxmem⟩ : C),
          (⟨x • (w : V), hxwmem⟩ : W)) = (c, w) := by
      apply hCWcomp.1
      calc
        x • (c : V) * x • (w : V) = x • ((c : V) * (w : V)) :=
          (smul_mul' x (c : V) (w : V)).symm
        _ = x • (z : V) := congrArg (fun y : V => x • y) hcw
        _ = (z : V) := hzfixx
        _ = (c : V) * (w : V) := hcw.symm
    have hcfixx : xbar • c = c := by
      apply Subtype.ext
      exact congrArg (fun t : C × W => (t.1 : V)) hpairs
    have hwfixx : rx • w = w := by
      apply Subtype.ext
      exact congrArg (fun t : C × W => (t.2 : V)) hpairs
    have hcD : c ∈ D := by
      change c ∈ FixedPoints.subgroup Rbar C
      rw [FixedPoints.mem_subgroup]
      intro rbar
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp rbar.property
      have hpow := MulAction.mem_fixedBy_zpow (MulAction.mem_fixedBy.mpr hcfixx) k
      rw [MulAction.mem_fixedBy] at hpow
      change (rbar : G ⧸ A) • c = c
      rw [← hk]
      exact hpow
    have hwE : w ∈ E := by
      change w ∈ FixedPoints.subgroup R W
      rw [FixedPoints.mem_subgroup]
      intro r
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp r.property
      have hpow := MulAction.mem_fixedBy_zpow (MulAction.mem_fixedBy.mpr hwfixx) k
      rw [MulAction.mem_fixedBy] at hpow
      have hr : rx ^ k = r := by
        apply Subtype.ext
        simpa [rx] using hk
      rw [← hr]
      exact hpow
    refine ⟨(⟨c, hcD⟩, ⟨w, hwE⟩), ?_⟩
    apply Subtype.ext
    exact hcw
  have hcardFixedProduct : Nat.card D * Nat.card E = Nat.card P :=
    (Nat.card_prod D E).symm.trans
      (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩))
  have hcardProduct : Nat.card C * Nat.card W = Nat.card V :=
    hCWcomp.card_mul_card
  change Nat.card C ≤ 2 * Nat.card D
  have hcardE : Nat.card E = 2 := by simpa [E] using hcardFixW
  have hcardP : Nat.card P = Nat.card D * 2 := by
    rw [← hcardFixedProduct, hcardE]
  have hcardV' : Nat.card V = Nat.card C * 4 := by
    rw [← hcardProduct, hcardW]
  have hindexP : Nat.card V ≤ 4 * Nat.card P := by
    simpa [P, R] using hindex
  rw [hcardV', hcardP] at hindexP
  omega
