module

public import Stellmacher.SectionsOneToFourDefs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.GroupAction.CoprimeHall
public import Theory.Representation.ElementaryAbelianAction

open scoped BigOperators Pointwise IsMulCommutative

namespace Stellmacher.SectionOne

universe u

/-! # Stellmacher (1.4)

The set `Ω(W)` is finite because `G` is finite; a `Finset` representative
makes the source's two internal direct products explicit.

For two factors `D` and `E`, their join acts faithfully on
`[V, D] ⋁ [V, E]`, an elementary abelian group of order at most `16`.
The order formula for `GL(n, 2)`, `n ≤ 4`, then bounds `|D ⋁ E|` by `9`;
if the two action factors overlap, their join has order below `16` and the
stronger bound `|D ⋁ E| ≤ 3` gives a contradiction.  Thus both families
are pairwise disjoint, and the order-nine join of distinct factors is abelian.
Finally coprime action splits `V` into the fixed points of `W₀` and its
commutator subgroup.  This formalizes the source's appeal to the structure of
`GL₄(2)` without assuming an additional classification lemma.

The two pairwise disjointness lemmas are also exported for the global
SL2-factor assembly in (1.7), where each relevant derived C3 subgroup has
already been placed in `O₃(G)` by its normality in the odd core.

Source: `refs/latex/stellmacher-n-group.tex`, Lemma (1.4). -/

public structure LemmaOneFourConclusion
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V]
    (W0 : Subgroup G) (F : Finset (Subgroup G)) : Prop where
  part_a : IsInternalDirectProduct W0 F
  part_b :
    IsInternalDirectProductFamily (⊤ : Subgroup V)
      (fun i : Option {D : Subgroup G // D ∈ F} =>
        match i with
        | none => FixedPoints.subgroup W0 V
        | some D => commutatorAction (D : Subgroup G) V)

private theorem commutatorAction_subgroup_mono
    {G V : Type*} [Group G] [Group V]
    [MulDistribMulAction G V]
    {A B : Subgroup G} (hAB : A ≤ B) :
    commutatorAction A V ≤ commutatorAction B V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  refine Subgroup.closure_mono ?_
  rintro x ⟨a, w, rfl⟩
  exact ⟨⟨a, hAB a.property⟩, w, rfl⟩

private theorem commutatorAction_le_iSup_of_eq_iSup
    {G V : Type*} [Group G] [Group V]
    [MulDistribMulAction G V]
    {A : Subgroup G} {ι : Sort*} (K : ι → Subgroup G)
    (hA : A = ⨆ i, K i) :
    commutatorAction A V ≤ ⨆ i, commutatorAction (K i) V := by
  let U : Subgroup V := ⨆ i, commutatorAction (K i) V
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
  have hKleP (i : ι) : K i ≤ P := by
    intro a ha w
    apply (show commutatorAction (K i) V ≤ U from
      le_iSup (fun j => commutatorAction (K j) V) i)
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨a, ha⟩, w, rfl⟩
  have hAleP : A ≤ P := by
    rw [hA]
    exact iSup_le hKleP
  rw [commutatorAction_eq_closure]
  refine (Subgroup.closure_le (K := U)).2 ?_
  rintro x ⟨a, w, rfl⟩
  exact hAleP a.property w

private theorem commutatorAction_eq_iSup_of_eq_iSup
    {G V : Type*} [Group G] [Group V]
    [MulDistribMulAction G V]
    {A : Subgroup G} {ι : Sort*} (K : ι → Subgroup G)
    (hA : A = ⨆ i, K i) :
    commutatorAction A V = ⨆ i, commutatorAction (K i) V := by
  apply le_antisymm
  · exact commutatorAction_le_iSup_of_eq_iSup K hA
  · refine iSup_le ?_
    intro i
    apply commutatorAction_subgroup_mono
    rw [hA]
    exact le_iSup (fun j => K j) i

private theorem card_sup_le_mul_of_isMulCommutative
    {X : Type u} [Group X] [Finite X] (A B : Subgroup X)
    (hcomm : IsMulCommutative X) :
    Nat.card ↑(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  let hAnorm : A.Normal :=
    ⟨fun a ha x => by
      rw [hcomm.is_comm.comm x a]
      simpa [mul_assoc] using ha⟩
  let _ : A.Normal := hAnorm
  let μ : A × B → ↑(A ⊔ B) := fun x =>
    ⟨(x.1 : X) * (x.2 : X), Subgroup.mul_mem_sup x.1.property x.2.property⟩
  have hμ : Function.Surjective μ := by
    intro x
    rcases (Subgroup.mem_sup_of_normal_left.mp x.property) with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  simpa [Nat.card_prod] using Nat.card_le_card_of_surjective μ hμ

private theorem elementaryAbelianSubgroup
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

private theorem restricted_commutator_action_faithful
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (K : Subgroup G) (hKle : K ≤ pCore 3 G) :
    let U : Subgroup V := commutatorAction K V
    letI : IsInvariant K V U := commutatorAction_isInvariant
    letI : IsElementaryAbelian 2 U := elementaryAbelianSubgroup U
    Function.Injective
      (Representation.ofElementaryAbelianAction
        (A := K) (G := U) (p := 2)).asGroupHom := by
  let U : Subgroup V := commutatorAction K V
  let hUinv : IsInvariant K V U := commutatorAction_isInvariant
  let _ : IsInvariant K V U := hUinv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelianSubgroup U
  let _ : IsElementaryAbelian 2 U := hUelem
  let ρ := Representation.ofElementaryAbelianAction
    (A := K) (G := U) (p := 2)
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro k hk
    have hρk : ρ k = 1 := by
      exact congrArg Units.val (MonoidHom.mem_ker.mp hk)
    have hkfixU (w : U) : k • w = w := by
      apply Additive.ofMul.injective
      have happ := LinearMap.congr_fun hρk (Additive.ofMul w)
      simpa [ρ] using happ
    have hKp : IsPGroup 3 K := by
      intro k
      rcases pCore_isPGroup (p := 3) (G := G) ⟨k, hKle k.property⟩ with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      apply Subtype.ext
      exact congrArg (fun z : pCore 3 G => (z : G)) hn
    obtain ⟨n, hn⟩ := hKp.exists_card_eq
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    have hcop : Nat.Coprime (Nat.card K) (Nat.card V) := by
      rw [hn, hm]
      exact Nat.Coprime.pow n m (by decide)
    have hcompl :
        IsCompl (FixedPoints.subgroup K V) U :=
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := V) (A := K)
        (Group.isSolvable_of_comm fun x y =>
          (IsMulCommutative.is_comm (M := V)).comm x y)
        hcop (inferInstance : IsMulCommutative V)
    have hkfixV (w : V) : (k : G) • w = w := by
      have hwtop : w ∈ (FixedPoints.subgroup K V ⊔ U) := by
        rw [hcompl.sup_eq_top]
        exact Subgroup.mem_top w
      let hfixnorm : (FixedPoints.subgroup K V).Normal :=
        Subgroup.normal_of_isMulCommutative _
      let _ : (FixedPoints.subgroup K V).Normal := hfixnorm
      rcases Subgroup.mem_sup_of_normal_left.mp hwtop with
        ⟨c, hc, z, hz, hcz⟩
      have hkc : k • c = c :=
        (FixedPoints.mem_subgroup (M := K) (a := c)).1 hc k
      have hkc' : (k : G) • c = c := by
        simpa only [Subgroup.smul_def] using hkc
      have hkz : (k : G) • z = z := by
        exact congrArg Subtype.val (hkfixU ⟨z, hz⟩)
      rw [← hcz, smul_mul', hkc', hkz]
    have hkG : (k : G) ∈ fixingSubgroup G (Set.univ : Set V) :=
      (mem_fixingSubgroup_iff (M := G) (s := (Set.univ : Set V))).2
        (fun w _ => hkfixV w)
    rw [h.action_faithful] at hkG
    simpa using hkG
  · exact bot_le

private theorem pCore_three_subgroup_card_bounds
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (K : Subgroup G) (hKle : K ≤ pCore 3 G)
    (hcardU : Nat.card (commutatorAction K V) ≤ 16) :
    Nat.card K ≤ 9 ∧
      (Nat.card (commutatorAction K V) < 16 → Nat.card K ≤ 3) := by
  let U : Subgroup V := commutatorAction K V
  let hUinv : IsInvariant K V U := commutatorAction_isInvariant
  let _ : IsInvariant K V U := hUinv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelianSubgroup U
  let _ : IsElementaryAbelian 2 U := hUelem
  let ρ := Representation.ofElementaryAbelianAction
    (A := K) (G := U) (p := 2)
  let nU := Module.finrank (ZMod 2) (Additive U)
  let b : Module.Basis (Fin nU) (ZMod 2) (Additive U) :=
    Module.finBasis (ZMod 2) (Additive U)
  let φ : K →* GL (Fin nU) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hρinj : Function.Injective ρ.asGroupHom :=
    restricted_commutator_action_faithful h K hKle
  have hφinj : Function.Injective φ :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hρinj
  have hdiv : Nat.card K ∣ Nat.card (GL (Fin nU) (ZMod 2)) :=
    Subgroup.card_dvd_of_injective φ hφinj
  have hdim : nU ≤ 4 := by
    change Nat.card (Additive U) ≤ 16 at hcardU
    rw [@Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive U)] at hcardU
    norm_num at hcardU
    change 2 ^ nU ≤ 2 ^ 4 at hcardU
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcardU
  have hKp : IsPGroup 3 K := by
    intro k
    rcases pCore_isPGroup (p := 3) (G := G) ⟨k, hKle k.property⟩ with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : pCore 3 G => (z : G)) hn
  obtain ⟨n, hn⟩ := hKp.exists_card_eq
  have hpown : 3 ^ n ∣ Nat.card (GL (Fin nU) (ZMod 2)) := by
    rw [← hn]
    exact hdiv
  have hnle : n ≤ 2 := by
    by_contra hnnot
    have hnthree : 3 ≤ n := by omega
    have h27pow : 3 ^ 3 ∣ 3 ^ n := Nat.pow_dvd_pow 3 hnthree
    have h27GL := h27pow.trans hpown
    clear hφinj hdiv φ b hρinj ρ
    interval_cases nU <;>
      rw [Matrix.card_GL_field] at h27GL <;>
      norm_num [Fin.prod_univ_succ] at h27GL
  have hcardNine : Nat.card K ≤ 9 := by
    rw [hn]
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 3)).mpr hnle
  refine ⟨hcardNine, ?_⟩
  intro hcardUlt
  have hdimlt : nU < 4 := by
    change Nat.card (Additive U) < 16 at hcardUlt
    rw [@Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive U)] at hcardUlt
    norm_num at hcardUlt
    change 2 ^ nU < 2 ^ 4 at hcardUlt
    exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hcardUlt
  have hnleone : n ≤ 1 := by
    by_contra hnnot
    have hntwo : 2 ≤ n := by omega
    have h9pow : 3 ^ 2 ∣ 3 ^ n := Nat.pow_dvd_pow 3 hntwo
    have h9GL := h9pow.trans hpown
    have hdim' : nU ≤ 3 := by omega
    clear hφinj hdiv φ b hρinj ρ
    interval_cases nU <;>
      rw [Matrix.card_GL_field] at h9GL <;>
      norm_num [Fin.prod_univ_succ] at h9GL
  rw [hn]
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 3)).mpr hnleone

private theorem omega_pair_commute
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) {D E W0 : Subgroup G}
    (hD : oneOmega (G := G) (V := V) D)
    (hE : oneOmega (G := G) (V := V) E)
    (hDle : D ≤ W0) (hEle : E ≤ W0) (hW0le : W0 ≤ pCore 3 G) :
    ∀ d : G, d ∈ D → ∀ e : G, e ∈ E → d * e = e * d := by
  intro d hd e he
  have hDcard : Nat.card D = 3 := hD.2.1
  have hEcard : Nat.card E = 3 := hE.2.1
  by_cases hDE : D = E
  · subst E
    let hDcyc : IsCyclic D := isCyclic_of_prime_card hDcard
    let hDcomm : IsMulCommutative D := hDcyc.isMulCommutative
    exact congrArg Subtype.val
      (hDcomm.is_comm.comm ⟨d, hd⟩ ⟨e, he⟩)
  · let K : Subgroup G := D ⊔ E
    let Kf : Bool → Subgroup G := fun i => if i then D else E
    have hKgen : K = ⨆ i, Kf i := by
      simp [K, Kf, iSup_bool_eq]
    have hKle : K ≤ pCore 3 G := by
      exact sup_le (hDle.trans hW0le) (hEle.trans hW0le)
    have hcommK :
        commutatorAction K V =
          commutatorAction D V ⊔ commutatorAction E V := by
      rw [commutatorAction_eq_iSup_of_eq_iSup Kf hKgen]
      simp [Kf, iSup_bool_eq]
    have hcommKcard : Nat.card (commutatorAction K V) ≤ 16 := by
      rw [hcommK]
      calc
        Nat.card ↑(commutatorAction D V ⊔ commutatorAction E V)
            ≤ Nat.card (commutatorAction D V) *
                Nat.card (commutatorAction E V) :=
          card_sup_le_mul_of_isMulCommutative _ _ inferInstance
        _ = 16 := by rw [hD.2.2, hE.2.2]
    have hKcardle : Nat.card K ≤ 9 :=
      (pCore_three_subgroup_card_bounds h K hKle hcommKcard).1
    have hKp : IsPGroup 3 K := by
      intro k
      rcases pCore_isPGroup (p := 3) (G := G) ⟨k, hKle k.property⟩ with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      apply Subtype.ext
      exact congrArg (fun z : pCore 3 G => (z : G)) hn
    obtain ⟨n, hn⟩ := hKp.exists_card_eq
    have hKcardge : 3 ≤ Nat.card K := by
      rw [← hDcard]
      exact Subgroup.card_le_of_le le_sup_left
    have hKcardne : Nat.card K ≠ 3 := by
      intro hKcard
      have hDK : D = K :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hKcard, hDcard])
      have hEK : E = K :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hKcard, hEcard])
      exact hDE (hDK.trans hEK.symm)
    have hnle : n ≤ 2 := by
      apply (Nat.pow_le_pow_iff_right (by omega : 1 < 3)).mp
      norm_num
      simpa [← hn] using hKcardle
    have hKcard : Nat.card K = 3 ^ 2 := by
      have hnpos : 0 < n := by
        by_contra hnpos
        have hnzero : n = 0 := by omega
        have hKcardOne : Nat.card K = 1 := by simpa [hnzero] using hn
        omega
      have hnneone : n ≠ 1 := by
        intro hn1
        have hKcardThree : Nat.card K = 3 := by simpa [hn1] using hn
        exact hKcardne hKcardThree
      have hntwo : n = 2 := by omega
      simpa [hntwo] using hn
    have hKcomm : IsMulCommutative K :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq hKcard
    exact congrArg Subtype.val
      ((hKcomm.is_comm).comm
        ⟨d, Subgroup.mem_sup_left hd⟩
        ⟨e, Subgroup.mem_sup_right he⟩)

/-- Distinct order-three members of the oneOmega family are disjoint. -/
public theorem omega_pair_disjoint
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    {D E : Subgroup G}
    (hD : oneOmega (G := G) (V := V) D)
    (hE : oneOmega (G := G) (V := V) E) (hDE : D ≠ E) :
    Disjoint D E := by
  rw [Subgroup.disjoint_def]
  intro x hxD hxE
  let I : Subgroup D := (D ⊓ E).subgroupOf D
  let hprimeD : Fact (Nat.card D).Prime := ⟨hD.2.1 ▸ Nat.prime_three⟩
  let _ : Fact (Nat.card D).Prime := hprimeD
  rcases I.eq_bot_or_eq_top_of_prime_card with hI | hI
  · have hxI : (⟨x, hxD⟩ : D) ∈ I := by
      change x ∈ D ⊓ E
      exact ⟨hxD, hxE⟩
    rw [hI] at hxI
    simpa using congrArg Subtype.val hxI
  · exfalso
    apply hDE
    apply Subgroup.eq_of_le_of_card_ge
    · intro d hd
      have hdI : (⟨d, hd⟩ : D) ∈ I := by
        rw [hI]
        exact Subgroup.mem_top _
      exact (show (d : G) ∈ D ⊓ E from hdI).2
    · rw [hD.2.1, hE.2.1]

/-- Distinct oneOmega subgroups inside the 3-core have disjoint action modules. -/
public theorem omega_pair_action_disjoint
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) {D E W0 : Subgroup G}
    (hD : oneOmega (G := G) (V := V) D)
    (hE : oneOmega (G := G) (V := V) E) (hDE : D ≠ E)
    (hDle : D ≤ W0) (hEle : E ≤ W0) (hW0le : W0 ≤ pCore 3 G) :
    Disjoint (commutatorAction D V) (commutatorAction E V) := by
  let A : Subgroup V := commutatorAction D V
  let B : Subgroup V := commutatorAction E V
  let U : Subgroup V := A ⊔ B
  let K : Subgroup G := D ⊔ E
  let Kf : Bool → Subgroup G := fun i => if i then D else E
  have hKgen : K = ⨆ i, Kf i := by simp [K, Kf, iSup_bool_eq]
  have hcommK : commutatorAction K V = U := by
    rw [commutatorAction_eq_iSup_of_eq_iSup Kf hKgen]
    simp [U, A, B, Kf, iSup_bool_eq]
  have hKle : K ≤ pCore 3 G :=
    sup_le (hDle.trans hW0le) (hEle.trans hW0le)
  have hUcardle : Nat.card U ≤ 16 := by
    calc
      Nat.card U ≤ Nat.card A * Nat.card B :=
        card_sup_le_mul_of_isMulCommutative A B inferInstance
      _ = 16 := by rw [hD.2.2, hE.2.2]
  by_contra hdisjoint
  have hexists : ∃ x : V, x ∈ A ∧ x ∈ B ∧ x ≠ 1 := by
    rw [Subgroup.disjoint_def] at hdisjoint
    push Not at hdisjoint
    exact hdisjoint
  obtain ⟨x, hxA, hxB, hxne⟩ := hexists
  let hAnorm : A.Normal := Subgroup.normal_of_isMulCommutative _
  let _ : A.Normal := hAnorm
  let μ : A × B → U := fun z =>
    ⟨(z.1 : V) * (z.2 : V), Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have hμsurj : Function.Surjective μ := by
    intro z
    rcases Subgroup.mem_sup_of_normal_left.mp z.property with
      ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hμnotinj : ¬ Function.Injective μ := by
    intro hμinj
    have hpairs :
        (⟨x, hxA⟩, (1 : B)) = ((1 : A), ⟨x, hxB⟩) := by
      apply hμinj
      apply Subtype.ext
      simp [μ]
    have hfirst := congrArg (fun z : A × B => (z.1 : V)) hpairs
    exact hxne (by simpa using hfirst)
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype B := Fintype.ofFinite B
  let _ : Fintype U := Fintype.ofFinite U
  have hUcardlt : Nat.card U < 16 := by
    have hlt := Fintype.card_lt_of_surjective_not_injective μ hμsurj hμnotinj
    have hlt' : Nat.card U < Nat.card A * Nat.card B := by
      simpa [← Nat.card_eq_fintype_card, Nat.card_prod] using hlt
    calc
      Nat.card U < Nat.card A * Nat.card B := hlt'
      _ = 16 := by dsimp [A, B]; rw [hD.2.2, hE.2.2]
  have hKcardle : Nat.card K ≤ 3 :=
    (pCore_three_subgroup_card_bounds h K hKle (hcommK.symm ▸ hUcardle)).2
      (hcommK.symm ▸ hUcardlt)
  have hKcardge : 3 ≤ Nat.card K := by
    rw [← hD.2.1]
    exact Subgroup.card_le_of_le le_sup_left
  have hKcard : Nat.card K = 3 := Nat.le_antisymm hKcardle hKcardge
  have hDK : D = K :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hKcard, hD.2.1])
  have hEK : E = K :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hKcard, hE.2.1])
  exact hDE (hDK.trans hEK.symm)

/-- **Stellmacher (1.4).**

Let `Ω(W) = {F₁, …, Fᵣ}` and `W₀ = ⟨F₁, …, Fᵣ⟩ ≤ O₃(G)`.  Then `W₀` and
`V` split as the internal direct products stated in the paper. -/
public theorem lemma_one_four
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (F : Finset (Subgroup G))
    (hF : ∀ D : Subgroup G, D ∈ F ↔ oneOmega (G := G) (V := V) D)
    (W0 : Subgroup G)
    (hW0 : W0 = ⨆ D : {D : Subgroup G // D ∈ F}, (D : Subgroup G))
    (hW0_le : W0 ≤ pCore 3 G) :
    LemmaOneFourConclusion (G := G) (V := V) W0 F := by
  have _ : S = S := rfl
  have hDleW0 (D : Subgroup G) (hDF : D ∈ F) : D ≤ W0 := by
    rw [hW0]
    exact le_iSup (fun E : {E : Subgroup G // E ∈ F} => (E : Subgroup G)) ⟨D, hDF⟩
  have hDOmega (D : Subgroup G) (hDF : D ∈ F) :
      oneOmega (G := G) (V := V) D :=
    (hF D).mp hDF
  have hpairComm
      (D : Subgroup G) (hDF : D ∈ F)
      (E : Subgroup G) (hEF : E ∈ F) :
      ∀ d : G, d ∈ D → ∀ e : G, e ∈ E → d * e = e * d :=
    omega_pair_commute h (hDOmega D hDF) (hDOmega E hEF)
      (hDleW0 D hDF) (hDleW0 E hEF) hW0_le
  have hpartA : IsInternalDirectProduct W0 F := by
    refine ⟨hW0, ?_, ?_, ?_⟩
    · intro D hDF
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer (hDleW0 D hDF)).2
      rw [hW0]
      refine iSup_le ?_
      intro E
      rw [Subgroup.le_normalizer_iff]
      intro e he d hd
      have hed : e * d = d * e :=
        hpairComm (E : Subgroup G) E.property D hDF e he d hd
      rw [hed]
      simpa [mul_assoc] using hd
    · intro D hDF E hEF hDE
      exact omega_pair_disjoint (hDOmega D hDF) (hDOmega E hEF) hDE
    · intro D hDF E hEF _hDE d hd e he
      exact hpairComm D hDF E hEF d hd e he
  have hcommGenerate :
      commutatorAction W0 V =
        ⨆ D : {D : Subgroup G // D ∈ F},
          commutatorAction (D : Subgroup G) V :=
    commutatorAction_eq_iSup_of_eq_iSup
      (fun D : {D : Subgroup G // D ∈ F} => (D : Subgroup G)) hW0
  have hcommDisjoint
      (D E : {D : Subgroup G // D ∈ F}) (hDE : D ≠ E) :
      Disjoint (commutatorAction (D : Subgroup G) V)
        (commutatorAction (E : Subgroup G) V) := by
    apply omega_pair_action_disjoint h
      (hDOmega D D.property) (hDOmega E E.property)
    · intro hsub
      apply hDE
      exact Subtype.ext hsub
    · exact hDleW0 D D.property
    · exact hDleW0 E E.property
    · exact hW0_le
  have hW0p : IsPGroup 3 W0 := by
    intro w
    rcases pCore_isPGroup (p := 3) (G := G)
      ⟨w, hW0_le w.property⟩ with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : pCore 3 G => (z : G)) hn
  obtain ⟨n, hn⟩ := hW0p.exists_card_eq
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hcop : Nat.Coprime (Nat.card W0) (Nat.card V) := by
    rw [hn, hm]
    exact Nat.Coprime.pow n m (by decide)
  have hcompl :
      IsCompl (FixedPoints.subgroup W0 V) (commutatorAction W0 V) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := W0)
      (Group.isSolvable_of_comm fun x y =>
        (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop inferInstance
  refine ⟨hpartA, ?_⟩
  have hfactorLe (D : {D : Subgroup G // D ∈ F}) :
      commutatorAction (D : Subgroup G) V ≤ commutatorAction W0 V := by
    rw [hcommGenerate]
    exact le_iSup
      (fun E : {E : Subgroup G // E ∈ F} =>
        commutatorAction (E : Subgroup G) V) D
  refine ⟨?_, ?_, ?_⟩
  · rw [iSup_option]
    change (⊤ : Subgroup V) =
      FixedPoints.subgroup W0 V ⊔
        ⨆ D : {D : Subgroup G // D ∈ F},
          commutatorAction (D : Subgroup G) V
    rw [← hcommGenerate, hcompl.sup_eq_top]
  · intro i j hij
    cases i with
    | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some D => exact hcompl.disjoint.mono_right (hfactorLe D)
    | some D =>
        cases j with
        | none => exact hcompl.disjoint.symm.mono_left (hfactorLe D)
        | some E =>
            exact hcommDisjoint D E (fun h => hij (congrArg some h))
  · intro _i _j _hij a _ha b _hb
    exact (IsMulCommutative.is_comm (M := V)).comm a b

end Stellmacher.SectionOne
