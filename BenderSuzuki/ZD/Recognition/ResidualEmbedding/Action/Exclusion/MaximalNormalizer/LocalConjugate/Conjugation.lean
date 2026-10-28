module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Basic

/-!
# Conjugation after Lemma 7.11

An element of the triple stabilizer taking the ZJ subgroup to a z-invariant
subgroup produces another member of the source admissible family. In particular
the swapping involution remains distinguished, and its invariant Sylow subgroup
is conjugated inside the same triple stabilizer. These are conditional helpers;
the local quotient and ZJ factorization must produce the conjugating element.

Source: GLS, Volume 4, Chapter 2, final paragraph of Proposition 7.1.
Transport arguments are adapted from `BenderSuzuki.SE.Section7Final`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement
universe u

private theorem theorem4bIsSylowSubgroupOf_isPGroup_final
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P E : Subgroup X}
    (hP : theorem4bIsSylowSubgroupOf p P E) : IsPGroup p P := by
  rcases hP with ⟨PE, rfl⟩
  exact PE.isPGroup'.map E.subtype

private theorem theorem4bIsSylowSubgroupOf_le_final
    {X : Type u} [Group X] {p : ℕ} {P E : Subgroup X}
    (hP : theorem4bIsSylowSubgroupOf p P E) : P ≤ E := by
  rcases hP with ⟨PE, rfl⟩
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

private theorem theorem4bIsSylowSubgroupOf_of_subgroup_card_eq_final
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P Q E : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P E)
    (hQE : Q ≤ E) (hcard : Nat.card Q = Nat.card P) :
    theorem4bIsSylowSubgroupOf p Q E := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PE, hP⟩
  have hPcard : Nat.card P = p ^ (Nat.card E).factorization p := by
    rw [hP, Subgroup.card_map_of_injective E.subtype_injective]
    exact Sylow.card_eq_multiplicity PE
  have hQEcard : Nat.card (Q.subgroupOf E) =
      p ^ (Nat.card E).factorization p := by
    rw [natCard_subgroupOf_eq Q E hQE, hcard, hPcard]
  let QE : Sylow p E := Sylow.ofCard (Q.subgroupOf E) hQEcard
  refine ⟨QE, ?_⟩
  change Q = (Q.subgroupOf E).map E.subtype
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQE]

private theorem theorem4b_section7_subgroup_conjBy_eq_self_of_mem
    {G : Type*} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H) :
    H.conjBy g = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)
  · intro hx
    apply Subgroup.mem_map.mpr
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg
    · simp [MulAut.conj_apply, mul_assoc]

private theorem theorem4b_omega1_map_mulEquiv
    {G H : Type*} [Group G] [Group H] {p : ℕ} (e : G ≃* H) :
    (omega₁ (G := G) (p := p)).map e.toMonoidHom =
      omega₁ (G := H) (p := p) := by
  rw [omega₁, omega, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [pow_one] using congrArg e.toMonoidHom hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    simpa [pow_one] using congrArg e.symm.toMonoidHom hy

/-- The Thompson subgroup commutes with transport along an ambient group
equivalence. -/
private theorem theorem4b_thompsonSubgroup_map_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (P : Subgroup G) (e : G ≃* H) :
    (thompsonSubgroup (G := G) P).map e.toMonoidHom =
      thompsonSubgroup (G := H) (P.map e.toMonoidHom) := by
  classical
  let eP : P ≃* P.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective P e.toMonoidHom e.injective
  have hcomp :
      ((P.map e.toMonoidHom).subtype).comp eP.toMonoidHom =
        e.toMonoidHom.comp P.subtype := by
    ext p
    rfl
  calc
    (thompsonSubgroup (G := G) P).map e.toMonoidHom =
        ((thompsonSubgroup (G := P) (⊤ : Subgroup P)).map P.subtype).map
          e.toMonoidHom := by rw [thompsonSubgroup_top_map_subtype]
    _ = (thompsonSubgroup (G := P) (⊤ : Subgroup P)).map
          (e.toMonoidHom.comp P.subtype) := by rw [Subgroup.map_map]
    _ = ((thompsonSubgroup (G := P) (⊤ : Subgroup P)).map
          eP.toMonoidHom).map (P.map e.toMonoidHom).subtype := by
            rw [Subgroup.map_map, hcomp]
    _ = (thompsonSubgroup (G := P.map e.toMonoidHom)
          (⊤ : Subgroup (P.map e.toMonoidHom))).map
          (P.map e.toMonoidHom).subtype := by
            rw [thompsonSubgroup_top_map_mulEquiv]
    _ = thompsonSubgroup (G := H) (P.map e.toMonoidHom) := by
          rw [thompsonSubgroup_top_map_subtype]

/-- The Thompson center commutes with transport along an ambient group
equivalence. -/
private theorem theorem4b_thompsonCenter_map_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (P : Subgroup G) (e : G ≃* H) :
    (thompsonCenter (G := G) P).map e.toMonoidHom =
      thompsonCenter (G := H) (P.map e.toMonoidHom) := by
  calc
    (thompsonCenter (G := G) P).map e.toMonoidHom =
        (centerIn (G := G) (thompsonSubgroup (G := G) P)).map
          e.toMonoidHom := by rfl
    _ = centerIn (G := H)
        ((thompsonSubgroup (G := G) P).map e.toMonoidHom) := by
          exact centerIn_map_mulEquiv e (thompsonSubgroup (G := G) P)
    _ = thompsonCenter (G := H) (P.map e.toMonoidHom) := by
          rw [theorem4b_thompsonSubgroup_map_mulEquiv]
          rfl

private theorem theorem4b_corollary64Z_map_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : Nat.Primes} (R : Subgroup G) (e : G ≃* H) :
    (corollary64Z p R).map e.toMonoidHom =
      corollary64Z p (R.map e.toMonoidHom) := by
  let JG : Subgroup G := thompsonCenter (G := G) R
  let JH : Subgroup H := thompsonCenter (G := H) (R.map e.toMonoidHom)
  have hJmap : JG.map e.toMonoidHom = JH := by
    simpa [JG, JH] using theorem4b_thompsonCenter_map_mulEquiv R e
  let eJ0 : JG ≃* JG.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective JG e.toMonoidHom e.injective
  let eJ : JG ≃* JH := eJ0.trans (MulEquiv.subgroupCongr hJmap)
  have hOmega :
      (omega₁ (G := JG) (p := p.val)).map eJ.toMonoidHom =
        omega₁ (G := JH) (p := p.val) :=
    theorem4b_omega1_map_mulEquiv eJ
  have hcomp :
      JH.subtype.comp eJ.toMonoidHom =
        e.toMonoidHom.comp JG.subtype := by
    ext j
    change (((MulEquiv.subgroupCongr hJmap) (eJ0 j) : JH) : H) = e (j : G)
    calc
      (((MulEquiv.subgroupCongr hJmap) (eJ0 j) : JH) : H) =
          ((eJ0 j : JG.map e.toMonoidHom) : H) :=
        MulEquiv.subgroupCongr_apply hJmap (eJ0 j)
      _ = e (j : G) :=
        Subgroup.coe_equivMapOfInjective_apply JG e.toMonoidHom e.injective j
  calc
    (corollary64Z p R).map e.toMonoidHom =
        ((omega₁ (G := JG) (p := p.val)).map JG.subtype).map
          e.toMonoidHom := by rfl
    _ = (omega₁ (G := JG) (p := p.val)).map
          (e.toMonoidHom.comp JG.subtype) := by rw [Subgroup.map_map]
    _ = ((omega₁ (G := JG) (p := p.val)).map eJ.toMonoidHom).map
          JH.subtype := by rw [Subgroup.map_map, hcomp]
    _ = (omega₁ (G := JH) (p := p.val)).map JH.subtype := by rw [hOmega]
    _ = corollary64Z p (R.map e.toMonoidHom) := by rfl

/-- In particular, `Omega₁(Z(J(R)))` conjugates with `R`. -/
public theorem action_corollary64Z_conjBy
    {G : Type*} [Group G] [Finite G] {p : Nat.Primes}
    (R : Subgroup G) (x : G) :
    (corollary64Z p R).conjBy x = corollary64Z p (R.conjBy x) := by
  simpa [Subgroup.conjBy] using
    theorem4b_corollary64Z_map_mulEquiv R (MulAut.conj x)

/-- All admissibility clauses follow from normalization of the conjugated
ZJ subgroup by `z`. This does not assume the final Sylow conclusion. -/
public theorem action_admissible_ZJ_conjugate_of_normalized
    {X : Type u} [Group X] [Finite X] {Z₀ : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z₀ M)
    (d : ActionCounterexample Z₀ M) {beta : X ⧸ M}
    (q : ActionMaximalNormalizerData d beta)
    {x : X} (hxE : x ∈ theorem4bSection7E M d.z beta)
    (hzNormZx : d.z ∈ Subgroup.normalizer
      ((corollary64Z ⟨d.p, d.hp⟩ q.R).conjBy x : Set X)) :
    ∃ a : ActionAdmissibleQ d beta,
      a.Q = corollary64Z ⟨d.p, d.hp⟩ (q.R.conjBy x) ∧
      a.P₁ = q.chosen.P₁.conjBy x ∧
      a.t = (MulAut.conj x) q.chosen.t := by
  classical
  let : Fact d.p.Prime := ⟨d.hp⟩
  let D : Subgroup X := theorem4bSection7D M beta
  let E : Subgroup X := theorem4bSection7E M d.z beta
  let R : Subgroup X := q.R
  let Z : Subgroup X := corollary64Z ⟨d.p, d.hp⟩ R
  have hED : E ≤ D := inf_le_left
  have hxD : x ∈ D := hED hxE
  have hxM : x ∈ M := (inf_le_left : D ≤ M) hxD
  have hxBeta : x • beta = beta :=
    MulAction.mem_stabilizer_iff.mp ((inf_le_right : D ≤
      MulAction.stabilizer X beta) hxD)
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  have hxAlpha : x • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    simpa [alpha, baseCoset_stabilizer] using hxM
  have hxInvAlpha : x⁻¹ • alpha = alpha := by
    calc
      x⁻¹ • alpha = x⁻¹ • (x • alpha) :=
        (congrArg (fun y => x⁻¹ • y) hxAlpha).symm
      _ = alpha := inv_smul_smul x alpha
  have hRp : IsPGroup d.p R := by
    change IsPGroup d.p q.R
    exact theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow
  have hRne : R ≠ ⊥ := by
    intro hRbot
    have hqRbot : q.R = ⊥ := hRbot
    have hP₁bot : q.chosen.P₁ = ⊥ := by
      exact le_antisymm (q.hP₁R.trans hqRbot.le) bot_le
    have hlt := q.hP₁card_lt_R
    rw [hP₁bot, hqRbot] at hlt
    simp at hlt
  have hZne : Z ≠ ⊥ := by
    have hJne : thompsonCenter R ≠ ⊥ :=
      section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot hRp hRne
    have hJp : IsPGroup d.p (thompsonCenter R) :=
      hRp.to_le (thompsonCenter_le R)
    have hpdiv : d.p ∣ Nat.card (thompsonCenter R) := by
      rcases hJp.card_eq_or_dvd with hcard | hdiv
      · have hJbot : thompsonCenter R = ⊥ :=
          Subgroup.card_eq_one.mp hcard
        exact False.elim (hJne hJbot)
      · exact hdiv
    have h := omega₁_map_subtype_ne_bot (thompsonCenter R) d.p hpdiv
    convert h using 1
    ext x
    rfl
  have hZR : Z ≤ R := by
    change (omega₁ (G := thompsonCenter R) (p := d.p)).map
        (thompsonCenter R).subtype ≤ R
    exact (Subgroup.map_subtype_le _).trans (thompsonCenter_le R)
  let Zx : Subgroup X := Z.conjBy x
  let Rx : Subgroup X := R.conjBy x
  let P₁x : Subgroup X := q.chosen.P₁.conjBy x
  let t₁ : X := (MulAut.conj x) q.chosen.t
  have hZxp : IsPGroup d.p Zx := by
    change IsPGroup d.p
      (Z.map (MulAut.conj x).toMonoidHom)
    exact (hRp.to_le hZR).map (MulAut.conj x).toMonoidHom
  have hZxne : Zx ≠ ⊥ := by
    intro hbot
    apply hZne
    have hconj := congrArg (fun H : Subgroup X => H.conjBy x⁻¹) hbot
    have hbotConj : (⊥ : Subgroup X).conjBy x⁻¹ = ⊥ := by
      ext y
      simp [Subgroup.conjBy]
    simpa [Zx, Subgroup.conjBy_inv, hbotConj] using hconj
  have hRD : R ≤ D := by
    exact (theorem4bIsSylowSubgroupOf_le_final q.hRsylow).trans inf_le_left
  have hRxD : Rx ≤ D := by
    calc
      Rx ≤ D.conjBy x := Subgroup.map_mono hRD
      _ = D := theorem4b_section7_subgroup_conjBy_eq_self_of_mem D hxD
  have hZxRx : Zx ≤ Rx := Subgroup.map_mono hZR
  have hZxD : Zx ≤ D := hZxRx.trans hRxD
  have hZxE : Zx ≤ E := by
    simpa [D, E, theorem4bSection7D, theorem4bSection7E] using
      theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer
        (by simpa [Zx, Z] using hzNormZx) hZxD
  have htNormZ : q.chosen.t ∈ Subgroup.normalizer (Z : Set X) := by
    exact normalizer_le_normalizer_corollary64Z R q.htNormR
  have ht₁Z : t₁ ∈ Z₀ := h.invariant x q.chosen.t q.chosen.htZ
  have ht₁NormZx : t₁ ∈ Subgroup.normalizer (Zx : Set X) := by
    have hle := section11_conjBy_le_normalizer_conjBy_of_le_normalizer
      (H := Subgroup.zpowers q.chosen.t) (K := Z)
      (Subgroup.zpowers_le.mpr htNormZ) x
    apply hle
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨q.chosen.t, Subgroup.mem_zpowers q.chosen.t, rfl⟩
  have ht₁Alpha : t₁ • alpha = beta := by
    change (x * q.chosen.t * x⁻¹) • alpha = beta
    calc
      _ = x • (q.chosen.t • (x⁻¹ • alpha)) := by
        simp [mul_smul, mul_assoc]
      _ = x • (q.chosen.t • alpha) := by rw [hxInvAlpha]
      _ = x • beta := by rw [q.chosen.htBase]
      _ = beta := hxBeta
  have hP₁E : q.chosen.P₁ ≤ E :=
    theorem4bIsSylowSubgroupOf_le_final q.chosen.hP₁sylow
  have hP₁xE : P₁x ≤ E := by
    calc
      P₁x ≤ E.conjBy x := Subgroup.map_mono hP₁E
      _ = E := theorem4b_section7_subgroup_conjBy_eq_self_of_mem E hxE
  have hP₁xcard : Nat.card P₁x = Nat.card q.chosen.P₁ := by
    exact Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hP₁xsyl : theorem4bIsSylowSubgroupOf d.p P₁x E :=
    theorem4bIsSylowSubgroupOf_of_subgroup_card_eq_final d.hp
      q.chosen.hP₁sylow hP₁xE hP₁xcard
  have hP₁NormZ : q.chosen.P₁ ≤
      Subgroup.normalizer (Z : Set X) := by
    exact q.hP₁R.trans
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_corollary64Z R))
  have hP₁xNormZx : P₁x ≤ Subgroup.normalizer (Zx : Set X) := by
    simpa [P₁x, Zx] using
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer hP₁NormZ x
  have ht₁NormP₁x : t₁ ∈ Subgroup.normalizer (P₁x : Set X) := by
    have hle := section11_conjBy_le_normalizer_conjBy_of_le_normalizer
      (H := Subgroup.zpowers q.chosen.t) (K := q.chosen.P₁)
      (Subgroup.zpowers_le.mpr q.chosen.htNormP₁) x
    apply hle
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨q.chosen.t, Subgroup.mem_zpowers q.chosen.t, rfl⟩
  let a : ActionAdmissibleQ d beta := {
    Q := Zx
    hQp := hZxp
    hQne := hZxne
    hQE := hZxE
    hzNormQ := by simpa [Zx, Z] using hzNormZx
    t := t₁
    htZ := ht₁Z
    htNormQ := ht₁NormZx
    htBase := by simpa [alpha, baseCoset_stabilizer] using ht₁Alpha
    P₁ := P₁x
    hP₁sylow := hP₁xsyl
    hP₁NormQ := hP₁xNormZx
    htNormP₁ := ht₁NormP₁x }
  refine ⟨a, ?_, rfl, rfl⟩
  exact action_corollary64Z_conjBy R x

end BenderSuzuki.ZD
