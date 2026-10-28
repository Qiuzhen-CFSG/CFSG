module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverDiagonal

/-!
# Diagonal actions on the full binary linear cover

An order-three coefficient automorphism fixes both a nontrivial scalar
cubic and an independent diagonal cubic in SL₃. Projective semilinear
descent is lifted through the faithful action on the central quotient.
Consequently a non-diagonal cubic actor fixes a rank-two subgroup in the
actual cover. The original disjoint outside cubic would enlarge it to
rank three, contradicting SQTK. This excludes every binary linear field
actor without a prime-to-three hypothesis on the covering center.

The center of order three also supplies the precise signed field
congruence. The source refinement retains the original star quotient,
residual product and disjoint complement. Only binary unitary actions
remain without a diagonal marking; the Singer centralizer and conjugacy
clauses remain separate source obligations for both signs. OddRankSource
applies this refinement to the literal Cartan extension.

Source: Aschbacher–Smith A.3.18, printed pp.51–53. The descent and matrix
witnesses reuse the attributed intrinsic results imported by CoverDiagonal.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverBinary
private theorem fixed_rank_lt_two {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (x : G) (hx : orderOf x = 3) (hxK : x ∉ K)
    (hr : primeRank 3 G ≤ 2) (C : Subgroup K)
    (hC : ∀ c : C, Commute (c.val : G) x) : primeRank 3 C < 2 := by
  by_contra hn
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := C) (p := 3)
  let := hE
  obtain ⟨B,hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := 2)
    (by rw [hcard]; exact pow_dvd_pow 3 (by omega))
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.of_injective B.subtype B.subtype_injective
  let f : E →* G := K.subtype.comp (C.subtype.comp E.subtype)
  have hf : Function.Injective f := K.subtype_injective.comp
    (C.subtype_injective.comp E.subtype_injective)
  let D := B.map f
  let : IsElementaryAbelian 3 D := IsElementaryAbelian.map f
  have hdK : D ≤ K := by rintro _ ⟨b,_,rfl⟩; exact b.val.val.property
  have hfix : D ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨b,_,rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hC b.val)
  have hc : Nat.card D = 3^2 := by rw [card_map_of_injective hf,hB]
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join D x hx
    (fun h => hxK (hdK h)) hfix hc
  omega

private theorem fixes_cubic_scalar {F : Type*} [Field F] (σ : F ≃+* F) (hs : σ ^ 3 = 1)
    (u : F) (hu : u ^ 3 = 1) (hne : u ≠ 1) : σ u = u := by
  have hp : IsPrimitiveRoot u 3 := IsPrimitiveRoot.iff_orderOf.mpr
    (orderOf_eq_prime hu hne)
  obtain ⟨k, hk, he⟩ := hp.eq_pow_of_pow_eq_one (show σ u ^ 3 = 1 by rw [← map_pow, hu, map_one])
  have hne' : σ u ≠ 1 := by simpa using hne
  have hs' : σ (σ (σ u)) = u := DFunLike.congr_fun hs u
  interval_cases k
  · exact (hne' (by simpa using he.symm)).elim
  · simpa using he.symm
  · have h2 : σ u = u ^ 2 := he.symm
    rw [h2, map_pow, h2, map_pow, map_pow, h2] at hs'
    have h8 : ((u ^ 2) ^ 2) ^ 2 = u ^ 2 := by
      calc ((u ^ 2) ^ 2) ^ 2 = u ^ 3 * u ^ 3 * u ^ 2 := by ring
           _ = u ^ 2 := by rw [hu]; simp
    rw [h8] at hs'
    have hu0 : u ≠ 0 := by intro he; simp [he] at hu
    have h1 : u = 1 := by
      apply mul_right_cancel₀ hu0
      simpa only [pow_two, one_mul] using hs'
    exact (hne h1).elim


/-- Cubic coefficient automorphisms fix a rank-two torus in the full cover. -/
theorem linear_field_fixed_rank {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n)
    (σ : F ≃+* F) (hs : σ ^ 3 = 1) :
    2 ≤ primeRank 3 (MulAut.fixedSubgroup (Atlas.fieldEquivSL 3 σ)) := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by
    rw [Nat.card_units, hF]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr hn)
  have hu3 : (u : F) ^ 3 = 1 := congrArg Units.val (orderOf_eq_prime_iff.mp hu).1
  have hu1 : (u : F) ≠ 1 := fun h => (orderOf_eq_prime_iff.mp hu).2 (Units.ext h)
  have hfix : σ (u : F) = u := fixes_cubic_scalar σ hs u hu3 hu1
  let D := Theory.SpecificGroups.SignedThreeCubicRank.diagonal (u : F) hu3
  let Z := Theory.SpecificGroups.SignedThreeCubicRank.scalar (u : F) hu3
  have hd : D ∈ (MulAut.fixedSubgroup (Atlas.fieldEquivSL 3 σ)) := by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    ext i j
    change σ (D.val i j) = D.val i j
    fin_cases i <;> fin_cases j <;>
      simp [D, Theory.SpecificGroups.SignedThreeCubicRank.diagonal, hfix]
  have hz : Z ∈ (MulAut.fixedSubgroup (Atlas.fieldEquivSL 3 σ)) := by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    ext i j
    change σ (Z.val i j) = Z.val i j
    fin_cases i <;> fin_cases j <;>
      simp [Z, Theory.SpecificGroups.SignedThreeCubicRank.scalar, hfix]
  exact Theory.SpecificGroups.SignedThreeCubicRank.special_rank (u : F) hu3 hu1
    (SpecialLinearGroup.toGL.comp (MulAut.fixedSubgroup (Atlas.fieldEquivSL 3 σ)).subtype)
    (SpecialLinearGroup.toGL_injective.comp Subtype.val_injective) ⟨D,hd⟩ ⟨Z,hz⟩ rfl rfl

/-- A cubic outside actor on a binary SL₃ cover is an actual diagonal actor. -/
theorem linear_binary {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} [K.Normal] (hr : primeRank 3 G ≤ 2)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (hm : IsSL K 3 (2 ^ n))
    (a : G) (ha : orderOf a = 3) (haK : a ∉ K) :
    IsLinearDiagonal K (2 ^ n) (MulAut.conjNormal a) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let α : MulAut K := MulAut.conjNormal a
  let β := MulAut.congr e α
  let γ := centerAction F β
  have hα : α ^ 3 = 1 := by
    change (MulAut.conjNormal a : MulAut K)^3=1
    rw [←map_pow,←ha,pow_orderOf_eq_one,map_one]
  have hβ : β ^ 3 = 1 := by rw [←map_pow,hα,map_one]
  have hγ : γ ^ 3 = 1 := by rw [←map_pow,hβ,map_one]
  have hd : γ ∈ innerDiagonal F := by
    by_contra hnot
    have hstandard : γ ∈ standard F := by
      rw [standard_eq_top_of_two_power_card F hn hF]
      trivial
    obtain ⟨m,σ,hfactor,hσ⟩ :=
      Matrix.PSL3.StandardCubicFixedNine.cubic_factorization γ hstandard hγ hnot
    obtain ⟨P,hP⟩ := Matrix.PSL3.StandardCubicFixedNine.Descent.exists_linear_conjugate_field
      m σ hσ (hfactor ▸ hγ)
    have hc (u v : MulAut SL(3,F)) : MulAut.congr u v = u * v * u⁻¹ := by
      ext x
      rfl
    have hc' (u v : MulAut PSL(3,F)) : MulAut.congr u v = u * v * u⁻¹ := by
      ext x
      rfl
    have hfield : centerAction F (Atlas.fieldEquivSL 3 σ) = fieldAction F σ := by
      ext x
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) x
      change centerAction F (Atlas.fieldEquivSL 3 σ) (QuotientGroup.mk y) =
        fieldAction F σ (QuotientGroup.mk y)
      rw [centerAction_mk,fieldAction_mk]
      rfl
    have hlift : MulAut.congr (linearConjSL F P) β = Atlas.fieldEquivSL 3 σ := by
      apply Matrix.PSL3.CartanActions.ActorCoverage.centerAction_injective F
      rw [hc,map_mul,map_mul,map_inv,hfield]
      change linearConj F P * γ * (linearConj F P)⁻¹ = _
      rw [hfactor,←hc']
      exact hP
    have hbound : primeRank 3 α.fixedSubgroup < 2 := by
      apply fixed_rank_lt_two K a ha haK hr
      intro c
      have he := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp c.property)
      exact ((mul_inv_eq_iff_eq_mul).mp he).symm
    have heq := primeRank_congr 3 (MulAut.fixedSubgroupCongr e α)
    have heq' := primeRank_congr 3 (MulAut.fixedSubgroupCongr (linearConjSL F P) β)
    rw [hlift] at heq'
    have hge := linear_field_fixed_rank hF heven σ (hσ ▸ pow_orderOf_eq_one σ)
    change primeRank 3 α.fixedSubgroup = primeRank 3 β.fixedSubgroup at heq
    omega
  obtain ⟨g,hg⟩ := hd
  have he : linearConjSL F g = β :=
    Matrix.PSL3.CartanActions.ActorCoverage.centerAction_injective F hg
  refine ⟨F,inferInstance,inferInstance,hF,e,g,?_⟩
  intro l
  have hh := linearConjSL_toGL F g (e l)
  rw [he] at hh
  simpa only [β,α,MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hh


/-- A central three-cover forces the exact signed congruence in A.3.18. -/
theorem cover_congruence {L : Type*} [Group L]
    (hz : Nat.card (center L) = 3) (u : Bool) (q : ℕ)
    (hq : CoverParameter u q) (hm : IsSLSign L u 3 q) : SignedCongruence u q := by
  rcases hq with ⟨n,hn,hq,hmod⟩ | ⟨hp,ho⟩
  · exact hmod
  cases u with
  | false =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center,hF] at hz
    have hd : 3 ∣ q - 1 := hz ▸ Nat.gcd_dvd_right 3 (q-1)
    have hh := Nat.mod_eq_zero_of_dvd hd
    have hq := hp.two_le
    change q % 3 = 1
    omega
  | true =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    let : Fact q.Prime := ⟨hp⟩
    have hfixed : Nat.card {x : F // J.conj x=x} = q := by
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius J.conj q 1
        (by decide) (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hconj)
    have hlarge : 2 < q := by have := hp.two_le; have := Nat.odd_iff.mp ho; omega
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      BenderSuzuki.External.huppert_II_10_13 J q hlarge hF hfixed
    let := J.projective_isPerfect_of_fixed_card hlarge hF hfixed
    have hZ : center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
      rcases (inferInstance : (center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
          with h | h
      · exact h
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
    have hz' : Nat.card (center J.specialSubgroup) = 3 := by
      rwa [Nat.card_congr (centerCongr e).toEquiv] at hz
    obtain ⟨z,hzorder⟩ := exists_prime_orderOf_dvd_card' (G := center J.specialSubgroup) 3
      (by rw [hz'])
    have hk : z.val ∈ J.specialToProjective.ker :=
      (J.specialToProjective_ker_eq_center hZ).symm ▸ z.property
    have hGL : z.val.val ∈ center (GL (Fin 3) F) := by
      apply ProjGenLinGroup.mk_eq_one.mp
      simpa only [J.specialToProjective_apply_val,Subgroup.coe_one] using
        congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    rw [GeneralLinearGroup.center_eq_range_scalar] at hGL
    obtain ⟨v,hv⟩ := hGL
    have hm := (BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.scalar_mem_special_iff J v).mp
      (hv ▸ z.val.property)
    have hv1 : v ≠ 1 := by
      intro he
      have hz1 : z=1 := by
        apply Subtype.ext
        apply Subtype.ext
        rw [←hv,he,map_one]
        rfl
      rw [hz1,orderOf_one] at hzorder
      omega
    have hpow : v ^ (q+1)=1 := by
      apply Units.ext
      simpa only [hconj,←pow_succ,Units.val_pow_eq_pow_val,Units.val_one] using hm.1
    have hd : 3 ∣ q+1 := (orderOf_eq_prime hm.2 hv1) ▸ orderOf_dvd_of_pow_eq_one hpow
    have hh := Nat.mod_eq_zero_of_dvd hd
    change q % 3 = 2
    omega

variable {G : Type*} [Group G] [Finite G]

/-- The source cover with its signed parameter and actual outer matrix
marking, except for the remaining binary unitary field-action branch. -/
structure MarkedStarCover (K : Subgroup G) (a : G) : Prop extends
    CoverStructure.StarCover K a where
  marking : ∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
    SignedCongruence unitary q ∧ IsSLSign (starComponent 3 K) unitary 3 q ∧
    ∃ α : MulAut (starComponent 3 K),
      (∀ l : starComponent 3 K, (α l).val = starMap 3 G a * l.val * (starMap 3 G a)⁻¹) ∧
      α ∉ MulAut.innerSubgroup (starComponent 3 K) ∧
      ((unitary = true ∧ ∃ n : ℕ, 1 ≤ n ∧ q = 2 ^ n) ∨
        IsDiagonalSign (starComponent 3 K) unitary q α)

/-- The original actor is diagonal on every linear cover and every odd
prime-field unitary cover. The literal central cover and split clauses persist. -/
theorem marked_star_cover {K : Subgroup G} [K.Normal]
    (hb : primeRank 3 G ≤ 2) (a : G) (hs : CoverStructure.StarCover K a) :
    MarkedStarCover K a := by
  let : (starComponent 3 K).Normal :=
    (inferInstance : K.Normal).map _ (QuotientGroup.mk'_surjective _)
  let := hs.quasisimple
  obtain ⟨_,u,q,hq,hm,α,ha,ho⟩ := hs.outer
  have he : α = (MulAut.conjNormal (starMap 3 G a) : MulAut (starComponent 3 K)) := by
    apply MulEquiv.ext
    intro l
    exact Subtype.ext (ha l)
  have hc : α ^ 3 = 1 := by
    have hp : starMap 3 G a ^ 3 = 1 := by
      simpa only [hs.order] using pow_orderOf_eq_one (starMap 3 G a)
    rw [he,←map_pow,hp,map_one]
  refine ⟨hs,u,q,hq,cover_congruence hs.outer.1 u q hq hm,hm,α,ha,ho,?_⟩
  rcases hq with ⟨n,hn,rfl,hmod⟩ | ⟨hp,hodd⟩
  · cases u with
    | true => exact Or.inl ⟨rfl,n,hn,rfl⟩
    | false =>
      right
      have heven : Even n := by
        rw [Nat.even_iff]
        simp only [Bool.false_eq_true,↓reduceIte] at hmod
        rw [Nat.BinaryTorusParity.two_pow_mod_three] at hmod
        split_ifs at hmod with h
        · exact h
        · omega
      have hstar : primeRank 3 (Star 3 G) ≤ 2 :=
        (primeRank_quotient_le_of_coprime 3 (pPrimeCore 3 G) pPrimeCore_coprime_card).trans hb
      rw [he]
      exact linear_binary hstar (by omega) heven hm (starMap 3 G a) hs.order hs.outside
  · right
    cases u with
    | false => exact CoverDiagonal.linear_odd hp hodd hm α hc
    | true => exact CoverDiagonal.unitary_odd hp hodd hm α hc

/-- Refine the normal split-prime source domain by discharging all linear
cover field actions and the source congruence, with the same original actor. -/
theorem alternatives_or_marked_star_cover
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {K : Subgroup G} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : G) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ (p = 3 ∧ MarkedStarCover K a) := by
  rcases CoverStructure.alternatives_or_star_cover hG hK hp ho hr a ha haK hgen with halt | ⟨rfl,hs⟩
  · exact Or.inl halt
  · exact Or.inr ⟨rfl,marked_star_cover (hG.stronglyQuasithin 3 Nat.prime_three (by decide)) a hs⟩

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverBinary
