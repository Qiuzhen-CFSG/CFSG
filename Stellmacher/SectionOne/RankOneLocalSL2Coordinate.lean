module

public import Stellmacher.SectionOne.LemmaOneFour
public import FeitThompson.PCore.PPrimeCoreFactorization
public import Theory.Representation.CardFourCommutingActions
public import Theory.GroupAction.FourElementInvolutionLines

/-!
# Local `SL₂(2)` coordinates in Stellmacher (1.6)

`RankOneLocalSL2Data` records the local direct-product alternative produced
recursively in the rank-at-least-two part of Lemma (1.6).  This module proves
that a Sylow `2`-subgroup meets every `SL₂(2)` factor in an order-two
coordinate, that this coordinate has full commutator with the factor's
derived order-three subgroup, and that it has fixed-point index two on the
full odd-core commutator module. The elementary order-two action calculus
is shared through `Theory.GroupAction.FourElementInvolutionLines`.

The proof first intersects the Sylow subgroup with each normal direct factor.
The resulting subgroup has order two by Sylow conjugacy and divisibility in a
group of order six.  The derived subgroup has order three and its commutator
with that coordinate is nontrivial, hence full.  Its action on its own
four-point commutator module is faithful; the coordinate therefore acts as a
nontrivial involution and has a two-point fixed subgroup.  Distinct
coordinates act trivially on this module by the `GL₂(2)` centralizer
calculation in `Theory.Representation.CardFourCommutingActions`.  More
generally, the module exposes the two support-detection consequences used on
page 18: an order-two subgroup centralizing such an order-three factor fixes
its commutator module, while a subgroup having full commutator with the factor
cannot fix that module.  Finally the prime-to-two core factorization expresses
the odd core as the join of the derived factors, so the same fixed-point index
holds on the entire odd-core commutator module.

Source: `refs/latex/stellmacher-n-group.tex`, proof of Lemma (1.6), journal
page 18, especially the assertions for the factors `E_i`, their intersections
`A_i`, and the modules `[V,F_i]`.
-/

@[expose] public section

namespace Stellmacher.SectionOne

universe u

open scoped Pointwise IsMulCommutative

open Stellmacher SectionOne

structure RankOneLocalSL2Data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (T : Subgroup G) : Prop where
  product : ∃ F : Finset (Subgroup G),
    (∀ E : Subgroup G, E ∈ F →
      IsSL2Two (↑E) ∧
        oneOmega (G := G) (V := V) ((commutator (↑E)).map E.subtype)) ∧
      IsInternalDirectProduct (oddCore G ⊔ T) F
  quadratic : commutatorAction₂ T V = ⊥
  fixed_card : fixedQuotientCard (G := G) (V := V) T
    (commutatorAction (oddCore G) V) = (Nat.card T : ℚ)

private theorem elementaryAbelian_subgroup_local
    {V : Type u} [Group V] [IsElementaryAbelian 2 V]
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

/-- An action commutator is invariant under every subgroup normalizing its
actor.  The subgroup formulation avoids introducing an action of the ambient
normalizer as a separate parameter. -/
private theorem commutatorAction_isInvariant_of_normal_subgroup
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (E D : Subgroup G) (hDE : D ≤ E) [(D.subgroupOf E).Normal] :
    IsInvariant E V (commutatorAction D V) := by
  have hforward : ∀ e : E, ∀ v : V,
      v ∈ commutatorAction D V → e • v ∈ commutatorAction D V := by
    intro e v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction
      (p := fun x _ => e • x ∈ Subgroup.closure
        {z : V | ∃ d : D, ∃ w : V, z = w⁻¹ * d • w})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨d, w, rfl⟩
      have hconj : (e : G) * (d : G) * (e : G)⁻¹ ∈ D := by
        have hdsub : (⟨(d : G), hDE d.property⟩ : E) ∈ D.subgroupOf E :=
          d.property
        have hc := (inferInstance : (D.subgroupOf E).Normal).conj_mem
          (⟨(d : G), hDE d.property⟩ : E) hdsub e
        exact hc
      let de : D := ⟨(e : G) * (d : G) * (e : G)⁻¹, hconj⟩
      refine Subgroup.subset_closure ⟨de, e • w, ?_⟩
      change e • (w⁻¹ * (d : G) • w) =
        (e • w)⁻¹ * ((e : G) * (d : G) * (e : G)⁻¹) • (e • w)
      simp only [smul_mul', smul_inv']
      congr 1
      change (e : G) • ((d : G) • w) =
        ((e : G) * (d : G) * (e : G)⁻¹) • ((e : G) • w)
      simp only [← mul_smul]
      congr 1
      group
    · simp
    · intro x y _ _ hx hy
      simpa [smul_mul'] using
        (Subgroup.closure {z : V | ∃ d : D, ∃ w : V, z = w⁻¹ * d • w}).mul_mem hx hy
    · intro x _ hx
      simpa [smul_inv'] using
        (Subgroup.closure {z : V | ∃ d : D, ∃ w : V, z = w⁻¹ * d • w}).inv_mem hx
  refine ⟨?_⟩
  intro e v
  constructor
  · exact hforward e v
  · intro hev
    have := hforward e⁻¹ (e • v) hev
    simpa [inv_smul_smul] using this

private theorem commutatorAction_isInvariant_of_commuting_subgroups_local
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (P D : Subgroup G) (hPD : ⁅P, D⁆ = ⊥) :
    IsInvariant P V (commutatorAction D V) := by
  have hcomm : P ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPD
  have hpd (p : P) (d : D) :
      (p : G) * (d : G) = (d : G) * (p : G) := by
    exact (Subgroup.mem_centralizer_iff.mp (hcomm p.property)
      (d : G) d.property).symm
  have hsmul (p : P) (d : D) (v : V) : p • (d • v) = d • (p • v) := by
    change (p : G) • ((d : G) • v) = (d : G) • ((p : G) • v)
    rw [← mul_smul, ← mul_smul, hpd]
  have hforward : ∀ p : P, ∀ v : V,
      v ∈ commutatorAction D V → p • v ∈ commutatorAction D V := by
    intro p v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction
      (p := fun x _ => p • x ∈ Subgroup.closure
        {z : V | ∃ d : D, ∃ w : V, z = w⁻¹ * d • w})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨d, w, rfl⟩
      refine Subgroup.subset_closure ⟨d, p • w, ?_⟩
      simp only [smul_mul', smul_inv', hsmul]
    · simp
    · intro x y _ _ hx hy
      simpa [smul_mul'] using
        (Subgroup.closure {z : V | ∃ d : D, ∃ w : V, z = w⁻¹ * d • w}).mul_mem hx hy
    · intro x _ hx
      simpa [smul_inv'] using
        (Subgroup.closure {z : V | ∃ d : D, ∃ w : V, z = w⁻¹ * d • w}).inv_mem hx
  refine ⟨?_⟩
  intro p v
  constructor
  · exact hforward p v
  · intro hpv
    have := hforward p⁻¹ (p • v) hpv
    simpa [inv_smul_smul] using this

private theorem isInvariant_of_subgroup_local
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (E Q : Subgroup G) (U : Subgroup V) [IsInvariant E V U]
    (hQE : Q ≤ E) : IsInvariant Q V U := by
  refine ⟨?_⟩
  intro q v
  exact IsInvariant.invariant (A := E) (G := V) (H := U)
    ⟨q, hQE q.property⟩ v

private theorem commutatorAction_subgroup_mono_local
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {A B : Subgroup G} (hAB : A ≤ B) :
    commutatorAction A V ≤ commutatorAction B V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  refine Subgroup.closure_mono ?_
  rintro x ⟨a, w, rfl⟩
  exact ⟨⟨a, hAB a.property⟩, w, rfl⟩

private theorem commutatorAction_eq_iSup_of_eq_iSup_local
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {A : Subgroup G} {I : Sort*} (D : I → Subgroup G)
    (hA : A = ⨆ i, D i) :
    commutatorAction A V = ⨆ i, commutatorAction (D i) V := by
  apply le_antisymm
  · let U : Subgroup V := ⨆ i, commutatorAction (D i) V
    let P : Subgroup G :=
      { carrier := {a : G | ∀ w : V, w⁻¹ * (a • w) ∈ U}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb w
          have hbmem := hb w
          have hamem := ha (b • w)
          have hmul :
              w⁻¹ * ((a * b) • w) =
                (w⁻¹ * (b • w)) * ((b • w)⁻¹ * (a • (b • w))) := by
            simp [smul_smul, mul_assoc]
          rw [hmul]
          exact U.mul_mem hbmem hamem
        inv_mem' := by
          intro a ha w
          have hmem := ha (a⁻¹ • w)
          have hinv :
              w⁻¹ * (a⁻¹ • w) =
                ((a⁻¹ • w)⁻¹ * (a • (a⁻¹ • w)))⁻¹ := by
            simp [smul_smul]
          rw [hinv]
          exact U.inv_mem hmem }
    have hDleP (i : I) : D i ≤ P := by
      intro a ha w
      apply (show commutatorAction (D i) V ≤ U from
        le_iSup (fun j => commutatorAction (D j) V) i)
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨a, ha⟩, w, rfl⟩
    have hAleP : A ≤ P := by
      rw [hA]
      exact iSup_le hDleP
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le U).2 ?_
    rintro x ⟨a, w, rfl⟩
    exact hAleP a.property w
  · refine iSup_le ?_
    intro i
    apply commutatorAction_subgroup_mono_local
    rw [hA]
    exact le_iSup (fun j => D j) i

/-- An order-three actor acts faithfully on its own nontrivial coprime action
commutator. -/
private theorem restricted_commutatorAction_faithful_card_three
    {D V : Type u} [Group D] [Group V] [Finite D] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction D V]
    (hDcard : Nat.card D = 3)
    (hUcard : Nat.card (commutatorAction D V) = 4) :
    let U : Subgroup V := commutatorAction D V
    letI : IsInvariant D V U := commutatorAction_isInvariant
    letI : IsElementaryAbelian 2 U := elementaryAbelian_subgroup_local U
    Function.Injective
      (Representation.ofElementaryAbelianAction
        (A := D) (G := U) (p := 2)).asGroupHom := by
  let U : Subgroup V := commutatorAction D V
  let hUinv : IsInvariant D V U := commutatorAction_isInvariant
  let _ : IsInvariant D V U := hUinv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup_local U
  let _ : IsElementaryAbelian 2 U := hUelem
  let ρ := Representation.ofElementaryAbelianAction
    (A := D) (G := U) (p := 2)
  rw [← MonoidHom.ker_eq_bot_iff]
  let K : Subgroup D := ρ.asGroupHom.ker
  let hprime : Fact (Nat.card D).Prime := ⟨hDcard ▸ Nat.prime_three⟩
  let _ : Fact (Nat.card D).Prime := hprime
  rcases K.eq_bot_or_eq_top_of_prime_card with hKbot | hKtop
  · simpa [K] using hKbot
  · exfalso
    have htriv : ActsTrivially (A := D) (G := U) := by
      intro d x
      have hdker : d ∈ K := by rw [hKtop]; trivial
      have hdρ : ρ d = 1 :=
        congrArg Units.val (MonoidHom.mem_ker.mp hdker)
      apply Additive.ofMul.injective
      have happ := LinearMap.congr_fun hdρ (Additive.ofMul x)
      simpa [ρ] using happ
    have hrestrictedBot : commutatorAction D U = ⊥ := by
      rw [commutatorAction_eq_closure]
      apply le_antisymm
      · apply (Subgroup.closure_le (⊥ : Subgroup U)).2
        rintro z ⟨d, x, rfl⟩
        simp [htriv d x]
      · exact bot_le
    have hcop : Nat.Coprime (Nat.card D) (Nat.card V) := by
      obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
      rw [hDcard, hn]
      change Nat.Coprime (3 ^ 1) (2 ^ n)
      exact Nat.Coprime.pow 1 n (by decide)
    have hmap : (commutatorAction D U).map U.subtype = U := by
      calc
        (commutatorAction D U).map U.subtype = commutatorAction₂ D V :=
          commutatorAction_map_subtype_eq_commutatorAction₂
        _ = commutatorAction D V :=
          commutatorAction₂_eq_commutatorAction_of_coprime hcop
        _ = U := rfl
    rw [hrestrictedBot, Subgroup.map_bot] at hmap
    have hUbot : U = ⊥ := hmap.symm
    have hUone : Nat.card U = 1 := by rw [hUbot]; simp
    have hUfour : Nat.card U = 4 := hUcard
    omega

/-- An order-two subgroup centralizing an ambient omega factor fixes that
factor's four-point commutator module pointwise.  This is the coordinate
form of the `GL₂(2)` centralizer calculation. -/
public theorem oneOmega_card_two_centralizer_fixes_commutator
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (D Q : Subgroup G) (hD : oneOmega (G := G) (V := V) D)
    (hQcard : Nat.card Q = 2) (hcomm : ⁅D, Q⁆ = ⊥) :
    Q ≤ fixingSubgroup G (commutatorAction D V : Set V) := by
  let U : Subgroup V := commutatorAction D V
  let hDinv : IsInvariant D V U := commutatorAction_isInvariant
  let _ : IsInvariant D V U := hDinv
  have hQD : ⁅Q, D⁆ = ⊥ := by
    simpa only [Subgroup.commutator_comm] using hcomm
  let hQinv : IsInvariant Q V U :=
    commutatorAction_isInvariant_of_commuting_subgroups_local Q D hQD
  let _ : IsInvariant Q V U := hQinv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup_local U
  let _ : IsElementaryAbelian 2 U := hUelem
  have hfaith := restricted_commutatorAction_faithful_card_three
    (D := D) (V := V) hD.2.1 hD.2.2
  have hactions : ∀ d : D, ∀ q : Q, ∀ u : U,
      d • (q • u) = q • (d • u) := by
    intro d q u
    apply Subtype.ext
    change (d : G) • ((q : G) • (u : V)) =
      (q : G) • ((d : G) • (u : V))
    rw [← mul_smul, ← mul_smul]
    have hcent : D ≤ Subgroup.centralizer (Q : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact congrArg (fun x : G => x • (u : V))
      ((Subgroup.mem_centralizer_iff.mp (hcent d.property)
        (q : G) q.property).symm)
  have htriv :=
    Representation.actsTrivially_card_four_of_commuting_card_three_action
      (D := D) (Q := Q) (U := U) hD.2.2 hD.2.1 hfaith hQcard hactions
  intro q hq
  rw [mem_fixingSubgroup_iff]
  intro u hu
  exact congrArg Subtype.val (htriv ⟨q, hq⟩ ⟨u, hu⟩)

/-- If an order-two complement has full group commutator with an order-three
actor, then it acts nontrivially on the actor's faithful card-four
commutator module. -/
private theorem restricted_complement_action_nontrivial
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (E D Q : Subgroup G) (hDE : D ≤ E) (hQE : Q ≤ E)
    [(D.subgroupOf E).Normal]
    (hDcard : Nat.card D = 3)
    (hUcard : Nat.card (commutatorAction D V) = 4)
    (hcomm : ⁅D, Q⁆ = D) :
    let U : Subgroup V := commutatorAction D V
    letI : IsInvariant E V U :=
      commutatorAction_isInvariant_of_normal_subgroup E D hDE
    letI : IsInvariant Q V U := isInvariant_of_subgroup_local E Q U hQE
    commutatorAction Q U ≠ ⊥ := by
  let U : Subgroup V := commutatorAction D V
  let hEinv : IsInvariant E V U :=
    commutatorAction_isInvariant_of_normal_subgroup E D hDE
  let _ : IsInvariant E V U := hEinv
  let hQinv : IsInvariant Q V U := isInvariant_of_subgroup_local E Q U hQE
  let _ : IsInvariant Q V U := hQinv
  let hDinv : IsInvariant D V U := commutatorAction_isInvariant
  let _ : IsInvariant D V U := hDinv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup_local U
  let _ : IsElementaryAbelian 2 U := hUelem
  let ρE : E →* MulAut U := MulDistribMulAction.toMulAut E U
  let DE : Subgroup E := D.subgroupOf E
  let QE : Subgroup E := Q.subgroupOf E
  have hcommE : ⁅DE, QE⁆ = DE := by
    apply (Subgroup.map_injective E.subtype_injective)
    have hmap := commutator_subgroupOf_map_eq E Q D hQE hDE
    rw [hmap, hcomm, Subgroup.map_subgroupOf_eq_of_le hDE]
  change commutatorAction Q U ≠ ⊥
  intro hQbot
  have hQEimage : QE.map ρE = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    rcases ha with ⟨q, hq, rfl⟩
    apply DFunLike.ext _ _
    intro u
    let qQ : Q := ⟨(q : E), hq⟩
    have hgen : commutatorAction Q U =
        Subgroup.closure {z : U | ∃ q : Q, ∃ w : U, z = w⁻¹ * q • w} :=
      commutatorAction_eq_closure
    have hdelta : u⁻¹ * qQ • u ∈
        commutatorAction Q U := by
      rw [hgen]
      exact Subgroup.subset_closure ⟨qQ, u, rfl⟩
    rw [hQbot] at hdelta
    have hfix : qQ • u = u :=
      (eq_of_inv_mul_eq_one hdelta).symm
    change q • u = u
    apply Subtype.ext
    exact congrArg Subtype.val hfix
  have hDEimage : DE.map ρE = ⊥ := by
    calc
      DE.map ρE = (⁅DE, QE⁆).map ρE := by rw [hcommE]
      _ = ⁅DE.map ρE, QE.map ρE⁆ :=
        Subgroup.map_commutator DE QE ρE
      _ = ⊥ := by rw [hQEimage, Subgroup.commutator_bot_right]
  have hfaith := restricted_commutatorAction_faithful_card_three hDcard hUcard
  have hDbot : D = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro d hd
    let dD : D := ⟨d, hd⟩
    let dE : DE := ⟨⟨d, hDE hd⟩, hd⟩
    have himage : ρE dE = 1 := by
      have : ρE dE ∈ DE.map ρE := ⟨dE, dE.property, rfl⟩
      rw [hDEimage] at this
      simpa using this
    have hdDone : dD = 1 := by
      let ρD := Representation.ofElementaryAbelianAction
        (A := D) (G := U) (p := 2)
      apply hfaith
      change ρD.asGroupHom dD = ρD.asGroupHom 1
      apply Units.ext
      apply LinearMap.ext
      intro u
      change ρD dD u = ρD 1 u
      have hu := congrArg (fun f : MulAut U => f (Additive.toMul u)) himage
      have huU : dD • Additive.toMul u = Additive.toMul u := by
        apply Subtype.ext
        exact congrArg Subtype.val hu
      simpa only [ρD, Representation.ofElementaryAbelianAction_apply,
        one_smul] using congrArg Additive.ofMul huU
    exact congrArg Subtype.val hdDone
  have hDone : Nat.card D = 1 := by rw [hDbot]; simp
  omega

/-- An order-two subgroup having full commutator with an omega factor acts
nontrivially on that factor's four-point commutator module. -/
public theorem oneOmega_full_commutator_nontrivial
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (D Q : Subgroup G) (hD : oneOmega (G := G) (V := V) D)
    (hcomm : ⁅D, Q⁆ = D) :
    ¬ Q ≤ fixingSubgroup G (commutatorAction D V : Set V) := by
  let E : Subgroup G := D ⊔ Q
  let U : Subgroup V := commutatorAction D V
  have hQnormD : Q ≤ Subgroup.normalizer D := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact hcomm.le
  have hEnormD : E ≤ Subgroup.normalizer D :=
    sup_le D.le_normalizer hQnormD
  let hDnormalE : (D.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hEnormD
  let _ : (D.subgroupOf E).Normal := hDnormalE
  let hEinv : IsInvariant E V U :=
    commutatorAction_isInvariant_of_normal_subgroup E D le_sup_left
  let _ : IsInvariant E V U := hEinv
  let hQinv : IsInvariant Q V U :=
    isInvariant_of_subgroup_local E Q U le_sup_right
  let _ : IsInvariant Q V U := hQinv
  have hnontriv := restricted_complement_action_nontrivial
    E D Q le_sup_left le_sup_right
    hD.2.1 hD.2.2 hcomm
  intro hfix
  have htriv : ActsTrivially (A := Q) (G := U) := by
    intro q u
    apply Subtype.ext
    exact ((mem_fixingSubgroup_iff (M := G) (s := (U : Set V))).mp
      (hfix q.property)) (u : V) u.property
  have hbot : commutatorAction Q U = ⊥ := by
    rw [commutatorAction_eq_closure]
    refine le_antisymm ((Subgroup.closure_le (K := (⊥ : Subgroup U))).2 ?_) bot_le
    rintro x ⟨q, u, rfl⟩
    simp [htriv q u]
  exact hnontriv hbot

/-- Rank-nullity for the displacement map of an involution on an elementary
abelian two-group. -/
private theorem cardTwo_fixed_commutator_card_data
    {Q U : Type u} [Group Q] [Group U] [Finite Q] [Finite U]
    [Nontrivial U] [IsElementaryAbelian 2 U] [MulDistribMulAction Q U]
    (x : Q) (hx : IsInvolution x) (hcardQ : Nat.card Q = 2) :
    Nat.card U = Nat.card (FixedPoints.subgroup Q U) *
        Nat.card (commutatorAction Q U) ∧
      commutatorAction Q U ≤ FixedPoints.subgroup Q U :=
  _root_.card_two_action_fixed_commutator_card_data x hx hcardQ

private theorem fixed_and_commutator_card_two_of_nontrivial_card_two_action
    {Q U : Type u} [Group Q] [Group U] [Finite Q] [Finite U]
    [IsElementaryAbelian 2 U] [MulDistribMulAction Q U]
    (hQcard : Nat.card Q = 2) (hUcard : Nat.card U = 4)
    (hne : commutatorAction Q U ≠ ⊥) :
    Nat.card (FixedPoints.subgroup Q U) = 2 ∧
      Nat.card (commutatorAction Q U) = 2 :=
  _root_.four_element_action_fixed_commutator_card_two hQcard hUcard hne

private noncomputable def sl2TwoEquivGL :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL ⟨
    Matrix.SpecialLinearGroup.toGL_injective,
    by
      intro A
      have hdet : Matrix.det (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
        have hu : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
        exact congrArg Units.val hu
      refine ⟨⟨(A : Matrix (Fin 2) (Fin 2) (ZMod 2)), hdet⟩, ?_⟩
      exact Units.ext rfl⟩

private theorem isSL2Two_card
    {E : Type u} [Group E] [Finite E] (hE : IsSL2Two E) :
    Nat.card E = 6 := by
  rcases hE with ⟨e⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_congr sl2TwoEquivGL.toEquiv,
    Matrix.card_GL_field]
  decide

/-- A Sylow 2-subgroup meets a normal subgroup of order six in order two. -/
public theorem natCard_inf_sylow_normal_card_six
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) (E : Subgroup G) [E.Normal]
    (hEcard : Nat.card E = 6) :
    Nat.card ↥((P : Subgroup G) ⊓ E) = 2 := by
  let hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 2) := hp
  obtain ⟨r, hr⟩ : ∃ r : E, orderOf r = 2 := by
    apply exists_prime_orderOf_dvd_card' 2
    rw [hEcard]
    norm_num
  have hrG : orderOf (r : G) = 2 := by
    exact (orderOf_injective E.subtype E.subtype_injective r).trans hr
  let L : Subgroup G := Subgroup.zpowers (r : G)
  have hLcard : Nat.card L = 2 := by
    simpa only [L, Nat.card_zpowers] using hrG
  have hLp : IsPGroup 2 L :=
    IsPGroup.of_card (n := 1) (by simpa using hLcard)
  obtain ⟨R, hLR⟩ : ∃ R : Sylow 2 G, L ≤ (R : Subgroup G) :=
    hLp.exists_le_sylow
  obtain ⟨g, hg⟩ : ∃ g : G, g • R = P :=
    MulAction.IsPretransitive.exists_smul_eq R P
  let x : G := (MulAut.conj g) (r : G)
  have hrL : (r : G) ∈ L := Subgroup.mem_zpowers (r : G)
  have hxSmul : x ∈
      ((MulAut.conj g) • (R : Subgroup G) : Subgroup G) :=
    by
      change (MulAut.conj g) • (r : G) ∈
        ((MulAut.conj g) • (R : Subgroup G) : Subgroup G)
      exact Subgroup.smul_mem_pointwise_smul (α := MulAut G) (G := G)
        (r : G) (MulAut.conj g) (R : Subgroup G) (hLR hrL)
  have hxP : x ∈ (P : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul, hg] at hxSmul
    exact hxSmul
  have hxE : x ∈ E := by
    simpa only [x, MulAut.conj_apply] using
      (inferInstance : E.Normal).conj_mem (r : G) r.property g
  have hxne : x ≠ 1 := by
    intro hx
    have hconj : (MulAut.conj g) (r : G) = (MulAut.conj g) 1 := by
      simpa only [x, map_one] using hx
    have hrone : (r : G) = 1 := (MulAut.conj g).injective hconj
    have hrEone : r = 1 := Subtype.ext hrone
    rw [hrEone, orderOf_one] at hr
    norm_num at hr
  let Q : Subgroup G := (P : Subgroup G) ⊓ E
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hxone : x = 1 := by
      apply (Subgroup.eq_bot_iff_forall Q).mp hbot x
      exact ⟨hxP, hxE⟩
    exact hxne hxone
  have hQp : IsPGroup 2 Q := by
    exact P.isPGroup'.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
  have hQdvd : Nat.card Q ∣ Nat.card E := by
    rw [← natCard_subgroupOf_eq Q E inf_le_right]
    exact Subgroup.card_subgroup_dvd_card (Q.subgroupOf E)
  have hnle : n ≤ 1 := by
    have hdvd : 2 ^ n ∣ 6 := by simpa only [hn, hEcard] using hQdvd
    by_contra hnle
    have hn2 : 2 ≤ n := by omega
    have hfour : 4 ∣ 6 := by
      have hp : 2 ^ 2 ∣ 2 ^ n := Nat.pow_dvd_pow 2 hn2
      simpa using hp.trans hdvd
    norm_num at hfour
  have hnpos : 0 < n := by
    by_contra hnzero
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnzero
    have hQone : Nat.card Q = 1 := by simpa [hn0] using hn
    have hQgt : 1 < Nat.card Q :=
      (Subgroup.one_lt_card_iff_ne_bot Q).mpr hQne
    omega
  have hn1 : n = 1 := by omega
  simp only [Q, hn, hn1, pow_one]

private theorem local_factor_intersection_card_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (P : Sylow 2 G) (F : Finset (Subgroup G))
    (hEF : ∀ E : Subgroup G, E ∈ F →
      IsSL2Two (↑E) ∧
        oneOmega (G := G) (V := V) ((commutator (↑E)).map E.subtype))
    (hprod : IsInternalDirectProduct (oddCore G ⊔ (P : Subgroup G)) F)
    (E : Subgroup G) (hE : E ∈ F) :
    Nat.card ↥((P : Subgroup G) ⊓ E) = 2 := by
  let K : Subgroup G := oddCore G ⊔ (P : Subgroup G)
  have hEleK : E ≤ K := by
    change E ≤ oddCore G ⊔ (P : Subgroup G)
    rw [hprod.1]
    exact le_iSup (fun D : {D : Subgroup G // D ∈ F} => (D : Subgroup G))
      ⟨E, hE⟩
  let PK : Sylow 2 K := P.subtype le_sup_right
  let EK : Subgroup K := E.subgroupOf K
  let hEKnormal : EK.Normal := hprod.2.1 E hE
  let _ : EK.Normal := hEKnormal
  have hEKcard : Nat.card EK = 6 := by
    rw [natCard_subgroupOf_eq E K hEleK]
    exact isSL2Two_card (hEF E hE).1
  have hcardK : Nat.card ↥((PK : Subgroup K) ⊓ EK) = 2 :=
    natCard_inf_sylow_normal_card_six PK EK hEKcard
  have hmapInf :
      (((PK : Subgroup K) ⊓ EK).map K.subtype) =
        (P : Subgroup G) ⊓ E := by
    rw [Subgroup.map_inf _ _ K.subtype K.subtype_injective,
      Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le le_sup_right,
      Subgroup.map_subgroupOf_eq_of_le hEleK]
  calc
    Nat.card ↥((P : Subgroup G) ⊓ E) =
        Nat.card ↥(((PK : Subgroup K) ⊓ EK).map K.subtype) := by rw [hmapInf]
    _ = Nat.card ↥((PK : Subgroup K) ⊓ EK) :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective ((PK : Subgroup K) ⊓ EK) K.subtype
          K.subtype_injective).symm.toEquiv
    _ = 2 := hcardK

/-- In a group of order six whose derived subgroup has order three, every
order-two subgroup acts nontrivially on the derived subgroup and hence has
full commutator with it. -/
private theorem commutator_derived_order_three_order_two_eq
    {E : Type u} [Group E] [Finite E]
    (hEcard : Nat.card E = 6)
    (hDcard : Nat.card (commutator E) = 3)
    (Q : Subgroup E) (hQcard : Nat.card Q = 2) :
    ⁅commutator E, Q⁆ = commutator E := by
  let D : Subgroup E := commutator E
  have hDnormal : D.Normal := by infer_instance
  let _ : D.Normal := hDnormal
  have hDQdisj : Disjoint D Q := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [show Nat.card D = 3 from hDcard, hQcard]
    decide
  have hcomp := isComplement'_subgroupOf_sup_of_disjoint D Q hDQdisj
  have hsupCard : Nat.card ↥(D ⊔ Q) = 6 := by
    have hc := hcomp.card_mul_card
    rw [natCard_subgroupOf_eq D (D ⊔ Q) le_sup_left,
      natCard_subgroupOf_eq Q (D ⊔ Q) le_sup_right,
      show Nat.card D = 3 from hDcard, hQcard] at hc
    omega
  have hsupTop : D ⊔ Q = ⊤ :=
    Subgroup.eq_of_le_of_card_ge le_top (by
      rw [Subgroup.card_top, hEcard, hsupCard])
  have hCleD : ⁅D, Q⁆ ≤ D := Subgroup.commutator_le_left D Q
  let I : Subgroup D := ⁅D, Q⁆.subgroupOf D
  let hprime : Fact (Nat.card D).Prime := ⟨hDcard ▸ Nat.prime_three⟩
  let _ : Fact (Nat.card D).Prime := hprime
  rcases I.eq_bot_or_eq_top_of_prime_card with hIbot | hItop
  · have hCbot : ⁅D, Q⁆ = ⊥ := by
      calc
        ⁅D, Q⁆ = I.map D.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hCleD).symm
        _ = ⊥ := by rw [hIbot, Subgroup.map_bot]
    have hDcentQ : D ≤ Subgroup.centralizer (Q : Set E) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCbot
    have hQcentD : Q ≤ Subgroup.centralizer (D : Set E) :=
      Subgroup.le_centralizer_iff.mp hDcentQ
    let hDcyc : IsCyclic D := isCyclic_of_prime_card hDcard
    let _ : IsCyclic D := hDcyc
    let hQcyc : IsCyclic Q := by
      let hqprime : Fact (Nat.card Q).Prime := ⟨hQcard ▸ Nat.prime_two⟩
      let _ : Fact (Nat.card Q).Prime := hqprime
      exact isCyclic_of_prime_card hQcard
    let _ : IsCyclic Q := hQcyc
    have hDcentD : D ≤ Subgroup.centralizer (D : Set E) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hQcentQ : Q ≤ Subgroup.centralizer (Q : Set E) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hsupCent : D ⊔ Q ≤ Subgroup.centralizer ((D ⊔ Q : Subgroup E) : Set E) := by
      apply sup_le
      · rw [Subgroup.le_centralizer_iff]
        exact sup_le hDcentD hQcentD
      · rw [Subgroup.le_centralizer_iff]
        exact sup_le hDcentQ hQcentQ
    rw [hsupTop] at hsupCent
    have htopComm : IsMulCommutative (⊤ : Subgroup E) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mp hsupCent
    have hEcomm : IsMulCommutative E := by
      rw [isMulCommutative_iff]
      intro x y
      exact congrArg Subtype.val
        (htopComm.is_comm.comm ⟨x, trivial⟩ ⟨y, trivial⟩)
    let _ : IsMulCommutative E := hEcomm
    have hDbot : D = ⊥ := by
      change commutator E = ⊥
      exact commutator_eq_bot E
    have : Nat.card D = 1 := by rw [hDbot]; simp
    have hDthree : Nat.card D = 3 := hDcard
    omega
  · calc
      ⁅D, Q⁆ = I.map D.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hCleD).symm
      _ = D := by
        rw [hItop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem local_factor_commutator_eq
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (P : Sylow 2 G) (F : Finset (Subgroup G))
    (hEF : ∀ E : Subgroup G, E ∈ F →
      IsSL2Two (↑E) ∧
        oneOmega (G := G) (V := V) ((commutator (↑E)).map E.subtype))
    (hprod : IsInternalDirectProduct (oddCore G ⊔ (P : Subgroup G)) F)
    (E : Subgroup G) (hE : E ∈ F) :
    ⁅(commutator (↑E)).map E.subtype, (P : Subgroup G) ⊓ E⁆ =
      (commutator (↑E)).map E.subtype := by
  let D : Subgroup G := (commutator (↑E)).map E.subtype
  let Q : Subgroup G := (P : Subgroup G) ⊓ E
  let DE : Subgroup E := commutator E
  let QE : Subgroup E := Q.subgroupOf E
  have hDleE : D ≤ E := by
    exact Subgroup.map_le_iff_le_comap.mpr (fun x hx => x.property)
  have hQleE : Q ≤ E := inf_le_right
  have hDEmap : DE.map E.subtype = D := by
    rfl
  have hDEcard : Nat.card DE = 3 := by
    calc
      Nat.card DE = Nat.card (DE.map E.subtype) :=
        (Nat.card_congr
          (Subgroup.equivMapOfInjective DE E.subtype E.subtype_injective).toEquiv)
      _ = Nat.card D := by rw [hDEmap]
      _ = 3 := (hEF E hE).2.2.1
  have hQEcard : Nat.card QE = 2 := by
    rw [natCard_subgroupOf_eq Q E hQleE]
    exact local_factor_intersection_card_two P F hEF hprod E hE
  have hlocal : ⁅DE, QE⁆ = DE :=
    commutator_derived_order_three_order_two_eq
      (isSL2Two_card (hEF E hE).1) hDEcard QE hQEcard
  have hDsub : D.subgroupOf E = DE := by
    change (DE.map E.subtype).subgroupOf E = DE
    exact subgroupOf_map_subtype_eq DE
  have hQsub : Q.subgroupOf E = QE := rfl
  have hmapComm : (⁅DE, QE⁆).map E.subtype = ⁅D, Q⁆ := by
    simpa only [hDsub, hQsub] using
      (commutator_subgroupOf_map_eq E Q D hQleE hDleE)
  change ⁅D, Q⁆ = D
  calc
    ⁅D, Q⁆ = (⁅DE, QE⁆).map E.subtype := hmapComm.symm
    _ = DE.map E.subtype := by rw [hlocal]
    _ = D := hDEmap

/-- The Sylow-two coordinate of a local `SL₂(2)` factor has a single
fixed-point codimension on that factor's order-four action module. -/
private theorem local_factor_own_module_cards
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (P : Sylow 2 G) (F : Finset (Subgroup G))
    (hEF : ∀ E : Subgroup G, E ∈ F →
      IsSL2Two (↑E) ∧
        oneOmega (G := G) (V := V) ((commutator (↑E)).map E.subtype))
    (hprod : IsInternalDirectProduct (oddCore G ⊔ (P : Subgroup G)) F)
    (E : Subgroup G) (hE : E ∈ F) :
    let D : Subgroup G := (commutator (↑E)).map E.subtype
    let Q : Subgroup G := (P : Subgroup G) ⊓ E
    let U : Subgroup V := commutatorAction D V
    Nat.card (↥(U ⊓ FixedPoints.subgroup Q V)) = 2 := by
  let D : Subgroup G := (commutator (↑E)).map E.subtype
  let Q : Subgroup G := (P : Subgroup G) ⊓ E
  let U : Subgroup V := commutatorAction D V
  have hDleE : D ≤ E := Subgroup.map_subtype_le (commutator E)
  have hDsub : D.subgroupOf E = commutator E := by
    change ((commutator E).map E.subtype).subgroupOf E = commutator E
    exact subgroupOf_map_subtype_eq (commutator E)
  let hDnormal : (D.subgroupOf E).Normal := by
    rw [hDsub]
    infer_instance
  let _ : (D.subgroupOf E).Normal := hDnormal
  let hEinv : IsInvariant E V U :=
    commutatorAction_isInvariant_of_normal_subgroup E D hDleE
  let _ : IsInvariant E V U := hEinv
  let hQinv : IsInvariant Q V U :=
    isInvariant_of_subgroup_local E Q U inf_le_right
  let _ : IsInvariant Q V U := hQinv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup_local U
  let _ : IsElementaryAbelian 2 U := hUelem
  have hDcard : Nat.card D = 3 := (hEF E hE).2.2.1
  have hUcard : Nat.card U = 4 := (hEF E hE).2.2.2
  have hQcard : Nat.card Q = 2 :=
    local_factor_intersection_card_two P F hEF hprod E hE
  have hcomm : ⁅D, Q⁆ = D :=
    local_factor_commutator_eq P F hEF hprod E hE
  have hnontriv : commutatorAction Q U ≠ ⊥ :=
    restricted_complement_action_nontrivial E D Q hDleE inf_le_right
      hDcard hUcard hcomm
  have hcards := fixed_and_commutator_card_two_of_nontrivial_card_two_action
    hQcard hUcard hnontriv
  calc
    Nat.card (↥(U ⊓ FixedPoints.subgroup Q V)) =
        Nat.card ((FixedPoints.subgroup Q U).map U.subtype) := by
      rw [fixedPoints_subgroup_map_subtype_eq_inf]
    _ = Nat.card (FixedPoints.subgroup Q U) :=
      Subgroup.card_map_of_injective U.subtype_injective
    _ = 2 := hcards.1

/-- The local direct product forces its odd core to be generated by the
derived order-three subgroups of the `SL₂(2)` factors. -/
public theorem rankOneLocalSL2Data_oddCore_generated
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (T : Subgroup G)
    (hdata : RankOneLocalSL2Data (G := G) (V := V) T) :
    ∃ F : Finset (Subgroup G),
      (∀ E : Subgroup G, E ∈ F →
        IsSL2Two (↑E) ∧
          oneOmega (G := G) (V := V)
            ((commutator (↑E)).map E.subtype)) ∧
      IsInternalDirectProduct (oddCore G ⊔ T) F ∧
      oddCore G =
        ⨆ E : {E : Subgroup G // E ∈ F},
          (commutator (E : Subgroup G)).map E.val.subtype := by
  classical
  obtain ⟨F, hEF, hprod⟩ := hdata.product
  let H : Subgroup G := pPrimeCore 2 G ⊔ T
  have hEleH (E : Subgroup G) (hE_mem : E ∈ F) : E ≤ H := by
    change E ≤ oddCore G ⊔ T
    rw [hprod.1]
    exact le_iSup (fun E' : {E' : Subgroup G // E' ∈ F} =>
      (E' : Subgroup G)) ⟨E, hE_mem⟩
  let EH (E : Subgroup G) : Subgroup H := E.subgroupOf H
  let DE (E : Subgroup G) : Subgroup H := ⁅EH E, EH E⁆
  have hEHnormal (E : Subgroup G) (hE_mem : E ∈ F) :
      (EH E).Normal := by
    have hnormal := hprod.2.1 E hE_mem
    have hH : oddCore G ⊔ T = H := rfl
    rw [hH] at hnormal
    exact hnormal
  have hDEmap (E : Subgroup G) (hE_mem : E ∈ F) :
      (DE E).map H.subtype = (commutator E).map E.subtype := by
    calc
      (DE E).map H.subtype = ⁅E, E⁆ :=
        commutator_subgroupOf_map_eq H E E
          (hEleH E hE_mem) (hEleH E hE_mem)
      _ = (commutator E).map E.subtype :=
        (Subgroup.map_subtype_commutator E).symm
  have hDEcard (E : Subgroup G) (hE_mem : E ∈ F) :
      Nat.card (DE E) = 3 := by
    have hcardAmbient : Nat.card ((commutator E).map E.subtype) = 3 :=
      (hEF E hE_mem).2.2.1
    rw [← hDEmap E hE_mem] at hcardAmbient
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective (DE E) H.subtype
        H.subtype_injective).toEquiv).trans hcardAmbient
  have hDEp (E : Subgroup G) (hE_mem : E ∈ F) : IsPGroup 3 (DE E) :=
    IsPGroup.of_card (p := 3) (n := 1) (by
      simpa using hDEcard E hE_mem)
  have hEHcard (E : Subgroup G) (hE_mem : E ∈ F) :
      Nat.card (EH E) = 6 := by
    rw [natCard_subgroupOf_eq E H (hEleH E hE_mem)]
    exact isSL2Two_card (hEF E hE_mem).1
  have hDEleEH (E : Subgroup G) : DE E ≤ EH E :=
    Subgroup.commutator_le_self (EH E)
  have hDErelIndex (E : Subgroup G) (hE_mem : E ∈ F) :
      (DE E).relIndex (EH E) = 2 := by
    change ((DE E).subgroupOf (EH E)).index = 2
    have hmul := ((DE E).subgroupOf (EH E)).index_mul_card
    rw [natCard_subgroupOf_eq (DE E) (EH E) (hDEleEH E),
      hDEcard E hE_mem, hEHcard E hE_mem] at hmul
    omega
  have hDEeq (E : Subgroup G) :
      DE E = (commutator (EH E)).map (EH E).subtype :=
    (Subgroup.map_subtype_commutator (EH E)).symm
  have hderived_le : ∀ E : Subgroup G, E ∈ F →
      ⁅E, E⁆ ≤ pPrimeCore 2 G := by
    intro E hE_mem
    simpa only [oddCore, Subgroup.map_subtype_commutator] using
      (hEF E hE_mem).2.1
  have hindex : ∀ E : Subgroup G, E ∈ F →
      let H := pPrimeCore 2 G ⊔ T
      ∃ n : ℕ, ((commutator (E.subgroupOf H)).map
        (E.subgroupOf H).subtype).relIndex (E.subgroupOf H) = 2 ^ n := by
    intro E hE_mem
    refine ⟨1, ?_⟩
    change ((commutator (EH E)).map (EH E).subtype).relIndex (EH E) = 2 ^ 1
    rw [← hDEeq E, pow_one]
    exact hDErelIndex E hE_mem
  have hgen : pPrimeCore 2 G ⊔ T =
      ⨆ E : {E : Subgroup G // E ∈ F}, (E : Subgroup G) := by
    simpa only [oddCore] using hprod.1
  have hnorm : ∀ E : Subgroup G, E ∈ F →
      (E.subgroupOf (pPrimeCore 2 G ⊔ T)).Normal :=
    fun E hE_mem => by simpa only [H, EH] using hEHnormal E hE_mem
  have hcoreSub : (pPrimeCore 2 G).subgroupOf (pPrimeCore 2 G ⊔ T) =
    ⨆ E : {E : Subgroup G // E ∈ F},
      ⁅(E : Subgroup G).subgroupOf (pPrimeCore 2 G ⊔ T),
        (E : Subgroup G).subgroupOf (pPrimeCore 2 G ⊔ T)⁆ :=
    pPrimeCore_subgroupOf_eq_iSup_commutator_of_generated_factors
      T F hgen hnorm hderived_le hindex
  have hcoreMap :
      ((pPrimeCore 2 G).subgroupOf H).map H.subtype = pPrimeCore 2 G :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hterm (E : {E : Subgroup G // E ∈ F}) :
      (⁅(E : Subgroup G).subgroupOf H,
          (E : Subgroup G).subgroupOf H⁆).map H.subtype =
        (commutator (E : Subgroup G)).map E.val.subtype := by
    simpa only [DE, EH] using hDEmap (E : Subgroup G) E.property
  have hambient : oddCore G =
      ⨆ E : {E : Subgroup G // E ∈ F},
        (commutator (E : Subgroup G)).map E.val.subtype := by
    calc
      oddCore G = pPrimeCore 2 G := rfl
      _ = ((pPrimeCore 2 G).subgroupOf H).map H.subtype := hcoreMap.symm
      _ = (⨆ E : {E : Subgroup G // E ∈ F},
          ⁅(E : Subgroup G).subgroupOf H,
            (E : Subgroup G).subgroupOf H⁆).map H.subtype := by
        exact congrArg (fun K : Subgroup H => K.map H.subtype) hcoreSub
      _ = ⨆ E : {E : Subgroup G // E ∈ F},
          (⁅(E : Subgroup G).subgroupOf H,
            (E : Subgroup G).subgroupOf H⁆).map H.subtype := by
        rw [Subgroup.map_iSup]
      _ = ⨆ E : {E : Subgroup G // E ∈ F},
          (commutator (E : Subgroup G)).map E.val.subtype := by
        congr 1
        funext E
        exact hterm E
  exact ⟨F, hEF, hprod, hambient⟩

/-- A Sylow-two coordinate belonging to one direct factor fixes the
card-four commutator module of every different factor. -/
private theorem distinct_local_factor_coordinate_actsTrivially
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (P : Sylow 2 G) (F : Finset (Subgroup G))
    (hEF : ∀ E : Subgroup G, E ∈ F →
      IsSL2Two (↑E) ∧
        oneOmega (G := G) (V := V) ((commutator (↑E)).map E.subtype))
    (hprod : IsInternalDirectProduct (oddCore G ⊔ (P : Subgroup G)) F)
    (E : Subgroup G) (hE : E ∈ F)
    (K : Subgroup G) (hK : K ∈ F) (hEK : E ≠ K) :
    let Q : Subgroup G := (P : Subgroup G) ⊓ E
    let D : Subgroup G := (commutator (↑K)).map K.subtype
    let U : Subgroup V := commutatorAction D V
    letI : IsInvariant Q V U :=
      commutatorAction_isInvariant_of_commuting_subgroups_local Q D (by
        apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        exact (hprod.2.2.2 E hE K hK hEK q hq.2 d
          (Subgroup.map_subtype_le (commutator K) hd)).symm)
    letI : IsElementaryAbelian 2 U := elementaryAbelian_subgroup_local U
    ActsTrivially (A := Q) (G := U) := by
  let Q : Subgroup G := (P : Subgroup G) ⊓ E
  let D : Subgroup G := (commutator (↑K)).map K.subtype
  let U : Subgroup V := commutatorAction D V
  have hDleK : D ≤ K := Subgroup.map_subtype_le (commutator K)
  have hQDcomm : ⁅Q, D⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hprod.2.2.2 E hE K hK hEK q hq.2 d (hDleK hd)).symm
  let hQinv : IsInvariant Q V U :=
    commutatorAction_isInvariant_of_commuting_subgroups_local Q D hQDcomm
  let _ : IsInvariant Q V U := hQinv
  let hDinv : IsInvariant D V U := commutatorAction_isInvariant
  let _ : IsInvariant D V U := hDinv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup_local U
  let _ : IsElementaryAbelian 2 U := hUelem
  have hUcard : Nat.card U = 4 := (hEF K hK).2.2.2
  have hDcard : Nat.card D = 3 := (hEF K hK).2.2.1
  have hDfaith :
      Function.Injective
        (Representation.ofElementaryAbelianAction
          (A := D) (G := U) (p := 2)).asGroupHom :=
    restricted_commutatorAction_faithful_card_three hDcard hUcard
  have hQcard : Nat.card Q = 2 :=
    local_factor_intersection_card_two P F hEF hprod E hE
  have hactions_commute : ∀ d : D, ∀ q : Q, ∀ u : U,
      d • (q • u) = q • (d • u) := by
    intro d q u
    apply Subtype.ext
    change (d : G) • ((q : G) • (u : V)) =
      (q : G) • ((d : G) • (u : V))
    rw [← mul_smul, ← mul_smul]
    exact congrArg (fun g : G => g • (u : V))
      (hprod.2.2.2 E hE K hK hEK q q.property.2 d (hDleK d.property)).symm
  exact Representation.actsTrivially_card_four_of_commuting_card_three_action
    hUcard hDcard hDfaith hQcard hactions_commute

/-- On the full odd-core commutator module, a single local Sylow-two
coordinate still has fixed-point index exactly two. -/
private theorem local_factor_fixedQuotientCard_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (P : Sylow 2 G) (F : Finset (Subgroup G))
    (hEF : ∀ E : Subgroup G, E ∈ F →
      IsSL2Two (↑E) ∧
        oneOmega (G := G) (V := V) ((commutator (↑E)).map E.subtype))
    (hprod : IsInternalDirectProduct (oddCore G ⊔ (P : Subgroup G)) F)
    (hodd : oddCore G =
      ⨆ K : {K : Subgroup G // K ∈ F},
        (commutator (K : Subgroup G)).map K.val.subtype)
    (E : Subgroup G) (hE : E ∈ F) :
    fixedQuotientCard (G := G) (V := V)
      ((P : Subgroup G) ⊓ E) (commutatorAction (oddCore G) V) = 2 := by
  classical
  let Q : Subgroup G := (P : Subgroup G) ⊓ E
  let D : Subgroup G := (commutator (↑E)).map E.subtype
  let U : Subgroup V := commutatorAction D V
  let W : Subgroup V := commutatorAction (oddCore G) V
  let DU (K : {K : Subgroup G // K ∈ F}) : Subgroup G :=
    (commutator (K : Subgroup G)).map K.val.subtype
  let UV (K : {K : Subgroup G // K ∈ F}) : Subgroup V :=
    commutatorAction (DU K) V
  have hWgen : W = ⨆ K : {K : Subgroup G // K ∈ F}, UV K := by
    change commutatorAction (oddCore G) V =
      ⨆ K : {K : Subgroup G // K ∈ F},
        commutatorAction
          ((commutator (K : Subgroup G)).map K.val.subtype) V
    exact commutatorAction_eq_iSup_of_eq_iSup_local
      (fun K : {K : Subgroup G // K ∈ F} =>
        (commutator (K : Subgroup G)).map K.val.subtype) hodd
  let hOddNormal : (oddCore G).Normal := pPrimeCore_normal
  let _ : (oddCore G).Normal := hOddNormal
  let hOddSubTopNormal : ((oddCore G).subgroupOf (⊤ : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).2
      Subgroup.le_normalizer_of_normal
  let _ : ((oddCore G).subgroupOf (⊤ : Subgroup G)).Normal :=
    hOddSubTopNormal
  let hTopWInv : IsInvariant (⊤ : Subgroup G) V W :=
    commutatorAction_isInvariant_of_normal_subgroup
      (⊤ : Subgroup G) (oddCore G) le_top
  let _ : IsInvariant (⊤ : Subgroup G) V W := hTopWInv
  let hQWInv : IsInvariant Q V W :=
    isInvariant_of_subgroup_local (⊤ : Subgroup G) Q W le_top
  let _ : IsInvariant Q V W := hQWInv
  let hWelem : IsElementaryAbelian 2 W := elementaryAbelian_subgroup_local W
  let _ : IsElementaryAbelian 2 W := hWelem
  have hDleE : D ≤ E := Subgroup.map_subtype_le (commutator E)
  have hDsub : D.subgroupOf E = commutator E := by
    change ((commutator E).map E.subtype).subgroupOf E = commutator E
    exact subgroupOf_map_subtype_eq (commutator E)
  let hDnormal : (D.subgroupOf E).Normal := by
    rw [hDsub]
    infer_instance
  let _ : (D.subgroupOf E).Normal := hDnormal
  let hEUInv : IsInvariant E V U :=
    commutatorAction_isInvariant_of_normal_subgroup E D hDleE
  let _ : IsInvariant E V U := hEUInv
  let hQUInv : IsInvariant Q V U :=
    isInvariant_of_subgroup_local E Q U inf_le_right
  let _ : IsInvariant Q V U := hQUInv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup_local U
  let _ : IsElementaryAbelian 2 U := hUelem
  let Eidx : {K : Subgroup G // K ∈ F} := ⟨E, hE⟩
  have hUEq : UV Eidx = U := rfl
  have hUleW : U ≤ W := by
    rw [hWgen]
    simpa only [hUEq] using
      (le_iSup (fun K : {K : Subgroup G // K ∈ F} => UV K) Eidx)
  let C : Subgroup V := (commutatorAction Q U).map U.subtype
  let R : Subgroup V :=
    { carrier := {w : V | ∀ q : Q, w⁻¹ * (q : G) • w ∈ C}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy q
        have hxq := hx q
        have hyq := hy q
        have heq :
            (x * y)⁻¹ * (q : G) • (x * y) =
              (x⁻¹ * (q : G) • x) * (y⁻¹ * (q : G) • y) := by
          simp only [mul_inv_rev, smul_mul']
          ac_rfl
        rw [heq]
        exact C.mul_mem hxq hyq
      inv_mem' := by
        intro x hx q
        have h := C.inv_mem (hx q)
        simpa [smul_inv', mul_comm] using h }
  have hUVleR (K : {K : Subgroup G // K ∈ F}) : UV K ≤ R := by
    intro w hw q
    by_cases hKE : (K : Subgroup G) = E
    · have hKid : K = Eidx := Subtype.ext hKE
      subst K
      rw [hUEq] at hw
      change w⁻¹ * (q : G) • w ∈
        (commutatorAction Q U).map U.subtype
      let u : U := ⟨w, hw⟩
      have hdelta : u⁻¹ * q • u ∈ commutatorAction Q U := by
        rw [commutatorAction_eq_closure]
        exact Subgroup.subset_closure ⟨q, u, rfl⟩
      exact ⟨u⁻¹ * q • u, hdelta, rfl⟩
    · have htriv :=
        distinct_local_factor_coordinate_actsTrivially
          P F hEF hprod E hE (K : Subgroup G) K.property (Ne.symm hKE)
      have hfix := htriv q ⟨w, hw⟩
      have hfixV : (q : G) • w = w := congrArg Subtype.val hfix
      rw [hfixV, inv_mul_cancel]
      exact C.one_mem
  have hWleR : W ≤ R := by
    rw [hWgen]
    exact iSup_le hUVleR
  have hCWleC :
      (commutatorAction Q W).map W.subtype ≤ C := by
    rw [commutatorAction_eq_closure, MonoidHom.map_closure]
    refine (Subgroup.closure_le C).2 ?_
    rintro z ⟨x, ⟨q, w, rfl⟩, rfl⟩
    exact hWleR w.property q
  have hCleCW :
      C ≤ (commutatorAction Q W).map W.subtype := by
    dsimp only [C]
    rw [commutatorAction_eq_closure, MonoidHom.map_closure,
      commutatorAction_eq_closure, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro z ⟨x, ⟨q, u, rfl⟩, rfl⟩
    let w : W := ⟨(u : V), hUleW u.property⟩
    exact ⟨w⁻¹ * q • w, ⟨q, w, rfl⟩, rfl⟩
  have hcommMap : (commutatorAction Q W).map W.subtype = C :=
    le_antisymm hCWleC hCleCW
  have hUcard : Nat.card U = 4 := (hEF E hE).2.2.2
  have hDcard : Nat.card D = 3 := (hEF E hE).2.2.1
  have hQcard : Nat.card Q = 2 :=
    local_factor_intersection_card_two P F hEF hprod E hE
  have hcommDQ : ⁅D, Q⁆ = D :=
    local_factor_commutator_eq P F hEF hprod E hE
  have hOwnNontriv : commutatorAction Q U ≠ ⊥ :=
    restricted_complement_action_nontrivial E D Q hDleE inf_le_right
      hDcard hUcard hcommDQ
  have hOwnCards :=
    fixed_and_commutator_card_two_of_nontrivial_card_two_action
      hQcard hUcard hOwnNontriv
  have hCcard : Nat.card C = 2 := by
    dsimp only [C]
    rw [Subgroup.card_map_of_injective U.subtype_injective]
    exact hOwnCards.2
  have hcommWcard : Nat.card (commutatorAction Q W) = 2 := by
    rw [← Subgroup.card_map_of_injective
      (K := commutatorAction Q W) W.subtype_injective, hcommMap]
    exact hCcard
  let hWnontrivial : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by
    have hCLeW : C ≤ W := hcommMap ▸ Subgroup.map_subtype_le _
    have hcardLe : Nat.card C ≤ Nat.card W :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hCLeW)
        (Subgroup.inclusion_injective hCLeW)
    rw [hCcard] at hcardLe
    omega)
  let _ : Nontrivial W := hWnontrivial
  obtain ⟨q, hqne, hquniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQcard
  have hq : IsInvolution q := by
    refine ⟨hqne, ?_⟩
    have hqinv : q⁻¹ ≠ 1 := by simpa using hqne
    have heq : q⁻¹ = q := (hquniq q⁻¹ hqinv).trans (hquniq q hqne).symm
    calc
      q ^ 2 = q * q := pow_two q
      _ = q⁻¹ * q := by rw [heq]
      _ = 1 := inv_mul_cancel q
  obtain ⟨hcardProduct, _⟩ :=
    cardTwo_fixed_commutator_card_data (Q := Q) (U := W) q hq hQcard
  rw [hcommWcard] at hcardProduct
  have hfixedMap :
      (FixedPoints.subgroup Q W).map W.subtype =
        W ⊓ FixedPoints.subgroup Q V :=
    fixedPoints_subgroup_map_subtype_eq_inf W
  have hfixedCard :
      Nat.card (↥(W ⊓ FixedPoints.subgroup Q V)) =
        Nat.card (FixedPoints.subgroup Q W) := by
    rw [← hfixedMap, Subgroup.card_map_of_injective W.subtype_injective]
  have hden : (Nat.card (↥(W ⊓ FixedPoints.subgroup Q V)) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥(W ⊓ FixedPoints.subgroup Q V))).ne'
  change (Nat.card W : ℚ) /
      (Nat.card (↥(W ⊓ FixedPoints.subgroup Q V)) : ℚ) = 2
  apply (div_eq_iff hden).2
  rw [hfixedCard]
  exact_mod_cast (by simpa [Nat.mul_comm] using hcardProduct)

/-- Per-factor Sylow-two coordinates and the matching derived-factor
generation equality in the local direct product from Stellmacher (1.6).
Keeping both conclusions on the same factor family is the interface needed
when the factors are lifted through the recursive quotient. -/
public theorem rankOneLocalSL2Data_coordinates_generated
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (P : Sylow 2 G)
    (hdata : RankOneLocalSL2Data (G := G) (V := V) (P : Subgroup G)) :
    ∃ F : Finset (Subgroup G),
      (∀ E : Subgroup G, E ∈ F →
        IsSL2Two (↑E) ∧
          oneOmega (G := G) (V := V)
            ((commutator (↑E)).map E.subtype)) ∧
      IsInternalDirectProduct (oddCore G ⊔ (P : Subgroup G)) F ∧
      oddCore G =
        ⨆ E : {E : Subgroup G // E ∈ F},
          (commutator (E : Subgroup G)).map E.val.subtype ∧
      ∀ E : Subgroup G, E ∈ F →
        Nat.card (↥((P : Subgroup G) ⊓ E)) = 2 ∧
        ⁅(commutator (↑E)).map E.subtype, (P : Subgroup G) ⊓ E⁆ =
          (commutator (↑E)).map E.subtype ∧
        fixedQuotientCard (G := G) (V := V)
          ((P : Subgroup G) ⊓ E) (commutatorAction (oddCore G) V) = 2 := by
  obtain ⟨F, hEF, hprod, hodd⟩ :=
    rankOneLocalSL2Data_oddCore_generated (P : Subgroup G) hdata
  refine ⟨F, hEF, hprod, hodd, ?_⟩
  intro E hE
  exact ⟨local_factor_intersection_card_two P F hEF hprod E hE,
    local_factor_commutator_eq P F hEF hprod E hE,
    local_factor_fixedQuotientCard_two P F hEF hprod hodd E hE⟩

/-- Per-factor Sylow-two coordinates in the local direct product from
Stellmacher (1.6). -/
public theorem rankOneLocalSL2Data_coordinates
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (P : Sylow 2 G)
    (hdata : RankOneLocalSL2Data (G := G) (V := V) (P : Subgroup G)) :
    ∃ F : Finset (Subgroup G),
      (∀ E : Subgroup G, E ∈ F →
        IsSL2Two (↑E) ∧
          oneOmega (G := G) (V := V)
            ((commutator (↑E)).map E.subtype)) ∧
      IsInternalDirectProduct (oddCore G ⊔ (P : Subgroup G)) F ∧
      ∀ E : Subgroup G, E ∈ F →
        Nat.card (↥((P : Subgroup G) ⊓ E)) = 2 ∧
        ⁅(commutator (↑E)).map E.subtype, (P : Subgroup G) ⊓ E⁆ =
          (commutator (↑E)).map E.subtype ∧
        fixedQuotientCard (G := G) (V := V)
          ((P : Subgroup G) ⊓ E) (commutatorAction (oddCore G) V) = 2 := by
  obtain ⟨F, hEF, hprod, _hodd, hcoord⟩ :=
    rankOneLocalSL2Data_coordinates_generated P hdata
  exact ⟨F, hEF, hprod, hcoord⟩

end Stellmacher.SectionOne
