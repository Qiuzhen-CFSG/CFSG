module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# A central odd element with a four-element commutator module

Let an odd-order subgroup \`F\` act faithfully on a finite elementary abelian
2-group \`V\`, and let \`a\` be a nonidentity element in the ambient image of
\`Z(F)\`.  If \`[V,a]\` has order four, this module proves that the subgroup
of \`F\` fixing \`C_V(a)\` pointwise is exactly \`⟨a⟩\`.

The proof uses the coprime decomposition \`V = C_V(a)[V,a]\`.  Centrality
makes \`[V,a]\` invariant under the fixed-point kernel, and the decomposition
makes its restricted action faithful.  Thus the kernel embeds in
\`GL₂(2)\`, whose order is six.  The kernel has odd order and contains the
nontrivial subgroup \`⟨a⟩\`, so it has order three and equals that subgroup.

This supplies the fixed-point-kernel assertion used in the proof of
Stellmacher (1.3), \`refs/latex/stellmacher-n-group.tex\`, journal page 16.
-/

open scoped Pointwise IsMulCommutative

universe u v

private theorem elementaryAbelianSubgroup_local
    {V : Type u} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U where
  toIsMulCommutative :=
    ⟨⟨fun x y => Subtype.ext
      (show (x : V) * (y : V) = (y : V) * (x : V) from
        (IsMulCommutative.is_comm (M := V)).comm x y)⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (x : V)

private theorem commutatorAction_isInvariant_of_commuting_subgroups_local
    {G : Type u} {V : Type v} [Group G] [Group V] [MulDistribMulAction G V]
    (P Q : Subgroup G) (hPQ : ⁅P, Q⁆ = ⊥) :
    IsInvariant P V (commutatorAction Q V) := by
  have hcomm : P ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPQ
  have hpq (a : P) (q : Q) : (a : G) * (q : G) = (q : G) * (a : G) := by
    exact (Subgroup.mem_centralizer_iff.mp (hcomm a.property)
      (q : G) q.property).symm
  have hsmul (a : P) (q : Q) (v : V) : a • (q • v) = q • (a • v) := by
    change (a : G) • ((q : G) • v) = (q : G) • ((a : G) • v)
    rw [← mul_smul, ← mul_smul, hpq]
  have hforward : ∀ a : P, ∀ v : V,
      v ∈ commutatorAction Q V → a • v ∈ commutatorAction Q V := by
    intro a v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction
      (p := fun x _ => a • x ∈ Subgroup.closure
        {d : V | ∃ q : Q, ∃ v : V, d = v⁻¹ * q • v})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨q, w, rfl⟩
      refine Subgroup.subset_closure ⟨q, a • w, ?_⟩
      simp only [smul_mul', smul_inv', hsmul]
    · simp
    · intro x y _ _ hx hy
      simpa [smul_mul'] using (Subgroup.closure
        {d : V | ∃ q : Q, ∃ v : V, d = v⁻¹ * q • v}).mul_mem hx hy
    · intro x _ hx
      simpa [smul_inv'] using (Subgroup.closure
        {d : V | ∃ q : Q, ∃ v : V, d = v⁻¹ * q • v}).inv_mem hx
  constructor
  intro a v
  constructor
  · exact hforward a v
  · intro hav
    have h := hforward a⁻¹ (a • v) hav
    simpa [inv_smul_smul] using h

public theorem centralOddPElement_cardFour_fixedPointKernel_eq_zpowers
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F : Subgroup G) (_hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    {a : G} (ha : a ≠ 1) (hacent : a ∈ centerIn F)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers a) V) = 4) :
    fixingSubgroup F
        (FixedPoints.subgroup (Subgroup.zpowers a) V : Set V) =
      (Subgroup.zpowers a).subgroupOf F := by
  classical
  let A : Subgroup G := Subgroup.zpowers a
  have haF : a ∈ F := by
    exact hacent.1
  have hAF : A ≤ F := by
    exact Subgroup.zpowers_le.mpr haF
  have hAcentralF : A ≤ Subgroup.centralizer (F : Set G) := by
    exact Subgroup.zpowers_le.mpr hacent.2
  let C : Subgroup V := FixedPoints.subgroup A V
  let W : Subgroup V := commutatorAction A V
  let K : Subgroup F := fixingSubgroup F (C : Set V)
  let Kamb : Subgroup G := K.map F.subtype
  have hKambF : Kamb ≤ F := Subgroup.map_subtype_le K
  have hcommKA : ⁅Kamb, A⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact hKambF.trans (Subgroup.le_centralizer_iff.mp hAcentralF)
  have hWinv : IsInvariant Kamb V W := by
    simpa [W] using
      commutatorAction_isInvariant_of_commuting_subgroups_local Kamb A hcommKA
  let _ : IsInvariant Kamb V W := hWinv
  let _ : IsElementaryAbelian 2 W := elementaryAbelianSubgroup_local W
  have hAFK : A.subgroupOf F ≤ K := by
    intro x hx
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hvfix :=
      (FixedPoints.mem_subgroup (M := A) (a := v)).mp hv
        (⟨(x : G), hx⟩ : A)
    simpa only [Subgroup.smul_def] using hvfix
  have hAKamb : A ≤ Kamb := by
    calc
      A = (A.subgroupOf F).map F.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hAF).symm
      _ ≤ K.map F.subtype := Subgroup.map_mono hAFK
      _ = Kamb := rfl
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hAdvdF : Nat.card A ∣ Nat.card F := Subgroup.card_dvd_of_le hAF
  have h2A : Nat.Coprime 2 (Nat.card A) :=
    Nat.Coprime.of_dvd_right hAdvdF hFodd
  have hcopAV : Nat.Coprime (Nat.card A) (Nat.card V) := by
    rw [hm]
    exact h2A.symm.pow_right m
  have hcompl : IsCompl C W := by
    exact
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := V) (A := A)
        (Group.isSolvable_of_comm (fun x y =>
          (IsMulCommutative.is_comm (M := V)).comm x y))
        hcopAV (inferInstance : IsMulCommutative V)
  let ρ := Representation.ofElementaryAbelianAction
    (A := Kamb) (G := W) (p := 2)
  have hρinj : Function.Injective ρ.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro k hk
      have hρk : ρ k = 1 := by
        exact congrArg Units.val (MonoidHom.mem_ker.mp hk)
      have hkfixW (w : W) : k • w = w := by
        apply Additive.ofMul.injective
        have happ := LinearMap.congr_fun hρk (Additive.ofMul w)
        simpa [ρ] using happ
      obtain ⟨f, hfK, hfk⟩ := k.property
      have hkfixC (v : V) (hv : v ∈ C) : (k : G) • v = v := by
        have hfixF :=
          (mem_fixingSubgroup_iff (M := F) (s := (C : Set V))).mp hfK v hv
        rw [← hfk]
        change f • v = v
        exact hfixF
      have hkfixV (v : V) : (k : G) • v = v := by
        have hvtop : v ∈ C ⊔ W := by
          rw [hcompl.sup_eq_top]
          exact Subgroup.mem_top v
        let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
        rcases Subgroup.mem_sup_of_normal_left.mp hvtop with
          ⟨c, hc, w, hw, hcw⟩
        have hkc : (k : G) • c = c := hkfixC c hc
        have hkw : (k : G) • w = w := by
          exact congrArg Subtype.val (hkfixW ⟨w, hw⟩)
        rw [← hcw, smul_mul', hkc, hkw]
      have hkG : (k : G) ∈ fixingSubgroup G (Set.univ : Set V) :=
        (mem_fixingSubgroup_iff (M := G) (s := (Set.univ : Set V))).mpr
          (fun v _ => hkfixV v)
      rw [hfaith] at hkG
      apply Subtype.ext
      simpa using hkG
    · exact bot_le
  let nW := Module.finrank (ZMod 2) (Additive W)
  have hnW : nW = 2 := by
    have hc : Nat.card (Additive W) = 4 := by
      calc
        Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
        _ = 4 := by simpa [W, A] using hcard
    rw [@Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive W)] at hc
    norm_num at hc
    change 2 ^ nW = 2 ^ 2 at hc
    exact Nat.pow_right_injective (by omega) hc
  let b : Module.Basis (Fin nW) (ZMod 2) (Additive W) :=
    Module.finBasis (ZMod 2) (Additive W)
  let φ : Kamb →* GL (Fin nW) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hφinj : Function.Injective φ :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hρinj
  have hdiv : Nat.card Kamb ∣ Nat.card (GL (Fin nW) (ZMod 2)) :=
    Subgroup.card_dvd_of_injective φ hφinj
  rw [hnW, Matrix.card_GL_field] at hdiv
  norm_num [Fin.prod_univ_succ] at hdiv
  have h2Kamb : Nat.Coprime 2 (Nat.card Kamb) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hKambF) hFodd
  have hKambNe : Kamb ≠ ⊥ := by
    intro hbot
    have hAbot : A = ⊥ := by
      apply le_antisymm
      · simpa [hbot] using hAKamb
      · exact bot_le
    exact (Subgroup.zpowers_ne_bot.mpr ha) (by simpa [A] using hAbot)
  have hKambGt : 1 < Nat.card Kamb :=
    (Subgroup.one_lt_card_iff_ne_bot Kamb).mpr hKambNe
  have hKambCard : Nat.card Kamb = 3 := by
    have hdiv3 : Nat.card Kamb ∣ 3 := by
      apply h2Kamb.symm.dvd_of_dvd_mul_left
      simpa using hdiv
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with hcardOne | hcardThree
    · omega
    · exact hcardThree
  let Aint : Subgroup Kamb := A.subgroupOf Kamb
  have hAintNe : Aint ≠ ⊥ := by
    intro hbot
    have haAint : (⟨a, hAKamb (Subgroup.mem_zpowers a)⟩ : Kamb) ∈ Aint :=
      Subgroup.mem_zpowers a
    rw [hbot] at haAint
    exact ha (by simpa using congrArg Subtype.val (show
      (⟨a, hAKamb (Subgroup.mem_zpowers a)⟩ : Kamb) = 1 by simpa using haAint))
  let _ : Fact (Nat.Prime (Nat.card Kamb)) := ⟨by
    simpa [hKambCard] using Nat.prime_three⟩
  have hAintTop : Aint = ⊤ :=
    (Subgroup.eq_bot_or_eq_top_of_prime_card Aint).resolve_left hAintNe
  have hAKambEq : A = Kamb := by
    apply le_antisymm hAKamb
    intro x hx
    let xK : Kamb := ⟨x, hx⟩
    have hxA : xK ∈ Aint := by
      rw [hAintTop]
      trivial
    exact hxA
  apply Subgroup.map_injective F.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hAF]
  simpa [Kamb] using hAKambEq.symm
