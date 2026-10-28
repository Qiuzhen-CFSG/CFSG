module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Theory.GroupAction.NormalizingActor

/-!
# Independent actions and quadratic order-two generators

Distinct omega factors fix one another's commutator modules. The elementary abelian two-group displacement map makes an involution quadratic and gives its fixed-point count.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- Commuting acting subgroups preserve one another's action commutator. -/
private theorem commutatorAction_isInvariant_of_commuting_subgroups
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (P Q : Subgroup G) (hPQ : ⁅P, Q⁆ = ⊥) :
    IsInvariant P V (commutatorAction Q V) := by
  have hcomm : P ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPQ
  have hpq (a : P) (q : Q) :
      (a : G) * (q : G) = (q : G) * (a : G) := by
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
    have := hforward a⁻¹ (a • v) hav
    simpa [inv_smul_smul] using this

public theorem commutatorAction_map_subtype_le_ambient
    {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]
    (U : Subgroup V) [IsInvariant A V U] :
    (commutatorAction A U).map U.subtype ≤ commutatorAction A V := by
  rw [commutatorAction_eq_closure, MonoidHom.map_closure,
    commutatorAction_eq_closure]
  apply Subgroup.closure_mono
  rintro x ⟨z, ⟨a, u, rfl⟩, rfl⟩
  exact ⟨a, (u : V), rfl⟩

/-- Distinct factors in the full `oneOmega` decomposition act trivially on
one another's action modules.  Pairwise disjointness alone would not imply a
genuine multi-factor direct sum; this action-triviality is the stronger fact
needed for coordinate uniqueness. -/
public theorem distinct_oneOmega_factor_acts_trivially
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (D E : Subgroup G)
    (hDmem : D ∈ oneOmegaFinset (G := G) (V := V))
    (hEmem : E ∈ oneOmegaFinset (G := G) (V := V))
    (hDE : D ≠ E)
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V))) :
    E ≤ fixingSubgroup G (commutatorAction D V : Set V) := by
  let U : Subgroup V := commutatorAction D V
  have hcomm : ⁅E, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact hdecomp.part_a.2.2.2 D hDmem E hEmem hDE d hd e he
  let hUinv : IsInvariant E V U :=
    commutatorAction_isInvariant_of_commuting_subgroups E D hcomm
  let _ : IsInvariant E V U := hUinv
  have hdisj : Disjoint U (commutatorAction E V) := by
    let d : {X : Subgroup G // X ∈ oneOmegaFinset (G := G) (V := V)} :=
      ⟨D, hDmem⟩
    let e : {X : Subgroup G // X ∈ oneOmegaFinset (G := G) (V := V)} :=
      ⟨E, hEmem⟩
    have hde : d ≠ e := fun h => hDE (congrArg Subtype.val h)
    simpa only [U] using hdecomp.part_b.2.1 (some d) (some e) (by
      intro h
      exact hde (Option.some.inj h))
  have hmapbot : (commutatorAction E U).map U.subtype = ⊥ := by
    apply le_antisymm
    · apply (le_inf (Subgroup.map_subtype_le _) ?_).trans hdisj.eq_bot.le
      exact commutatorAction_map_subtype_le_ambient U
    · exact bot_le
  have hbot : commutatorAction E U = ⊥ := by
    apply Subgroup.map_injective U.subtype_injective
    simpa using hmapbot
  have htriv : ActsTrivially (A := E) (G := U) :=
    actsTrivially_of_commutatorAction_eq_bot hbot
  intro e he
  rw [mem_fixingSubgroup_iff]
  intro u hu
  exact congrArg Subtype.val (htriv ⟨e, he⟩ ⟨u, hu⟩)

public theorem commutatorAction_eq_bot_of_actsTrivially
    {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]
    (htriv : ActsTrivially (A := A) (G := V)) :
    commutatorAction A V = ⊥ := by
  rw [commutatorAction_eq_closure]
  refine le_antisymm ((Subgroup.closure_le (K := (⊥ : Subgroup V))).2 ?_) bot_le
  rintro x ⟨a, v, rfl⟩
  simp [htriv a v]

/-- The action commutator is quadratic as soon as its first commutator is
pointwise fixed. -/
public theorem commutatorAction₂_eq_bot_of_le_fixedPoints
    {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]
    (hle : commutatorAction A V ≤ FixedPoints.subgroup A V) :
    commutatorAction₂ A V = ⊥ := by
  apply le_antisymm
  · change Subgroup.closure
      {d : V | ∃ a : A, ∃ v : V, v ∈ commutatorAction A V ∧
        d = v⁻¹ * a • v} ≤ ⊥
    apply (Subgroup.closure_le (K := ⊥)).2
    rintro x ⟨a, v, hv, rfl⟩
    have hfix := (FixedPoints.mem_subgroup (M := A) (a := v)).mp
      (hle hv) a
    simp [hfix]
  · exact bot_le

/-- A group action generated on the module side by invariant quadratic
submodules is itself quadratic. -/
public theorem commutatorAction₂_eq_bot_of_iSup_quadratic
    {A V : Type u} [Group A] [Group V] [IsMulCommutative V]
    [MulDistribMulAction A V]
    {I : Sort*} (K : I → Subgroup V)
    (hKinv : ∀ i, IsInvariant A V (K i))
    (hgen : (⊤ : Subgroup V) = ⨆ i, K i)
    (hquad : ∀ i, let _ : IsInvariant A V (K i) := hKinv i
      commutatorAction₂ A (K i) = ⊥) :
    commutatorAction₂ A V = ⊥ := by
  apply commutatorAction₂_eq_bot_of_le_fixedPoints
  rw [commutatorAction_eq_closure]
  apply (Subgroup.closure_le (K := FixedPoints.subgroup A V)).2
  rintro d ⟨a, v, rfl⟩
  let P : Subgroup V :=
    { carrier := {w : V |
        w⁻¹ * (a • w) ∈ FixedPoints.subgroup A V}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change (x * y)⁻¹ * (a • (x * y)) ∈ FixedPoints.subgroup A V
        have hEq : (x * y)⁻¹ * (a • (x * y)) =
            (x⁻¹ * (a • x)) * (y⁻¹ * (a • y)) := by
          simp only [mul_inv_rev, smul_mul']
          ac_rfl
        rw [hEq]
        exact (FixedPoints.subgroup A V).mul_mem hx hy
      inv_mem' := by
        intro x hx
        change (x⁻¹)⁻¹ * (a • x⁻¹) ∈ FixedPoints.subgroup A V
        have hEq : (x⁻¹)⁻¹ * (a • x⁻¹) =
            (x⁻¹ * (a • x))⁻¹ := by
          simp only [inv_inv, smul_inv', mul_inv_rev]
          exact (IsMulCommutative.is_comm (M := V)).comm _ _
        rw [hEq]
        exact (FixedPoints.subgroup A V).inv_mem hx }
  have hKle (i : I) : K i ≤ P := by
    let _ : IsInvariant A V (K i) := hKinv i
    have hlocal : commutatorAction A (K i) ≤
        FixedPoints.subgroup A (K i) := by
      intro d hd
      rw [FixedPoints.mem_subgroup]
      intro b
      have hdelta : d⁻¹ * (b • d) ∈ commutatorAction₂ A (K i) :=
        Subgroup.subset_closure ⟨b, d, hd, rfl⟩
      have hone : d⁻¹ * (b • d) = 1 := by
        rw [hquad i] at hdelta
        simpa using hdelta
      exact (eq_of_inv_mul_eq_one hone).symm
    intro w hw
    change w⁻¹ * (a • w) ∈ FixedPoints.subgroup A V
    let wK : K i := ⟨w, hw⟩
    have hdelta : wK⁻¹ * (a • wK) ∈ commutatorAction A (K i) :=
      Subgroup.subset_closure ⟨a, wK, trivial, rfl⟩
    have hfix := hlocal hdelta
    rw [FixedPoints.mem_subgroup]
    intro b
    exact congrArg Subtype.val
      ((FixedPoints.mem_subgroup (M := A) (a := wK⁻¹ * (a • wK))).mp
        hfix b)
  have htopLe : (⊤ : Subgroup V) ≤ P := by
    rw [hgen]
    exact iSup_le hKle
  exact htopLe trivial

/-- An element of an elementary abelian two-group generates a subgroup of
order two unless it is the identity. -/
public theorem natCard_zpowers_eq_two_of_ne_one_of_elementary
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (s : S) (hs : s ≠ 1) :
    Nat.card (Subgroup.zpowers (s : G)) = 2 := by
  have hs2 : (s : G) ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hS.exponent_dvd_p s)
  rw [Nat.card_zpowers, orderOf_eq_prime hs2]
  exact fun hsone => hs (Subtype.ext hsone)

/-- Every order-two group acts quadratically on an elementary abelian
two-group. -/
public theorem commutatorAction₂_eq_bot_of_actor_card_two
    {A V : Type u} [Group A] [Group V] [Finite A]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hAcard : Nat.card A = 2) :
    commutatorAction₂ A V = ⊥ := by
  have hfirst : commutatorAction A V ≤ FixedPoints.subgroup A V := by
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := FixedPoints.subgroup A V)).2 ?_
    rintro d ⟨a, v, rfl⟩
    change ∀ b : A, b • (v⁻¹ * a • v) = v⁻¹ * a • v
    intro b
    obtain ⟨t, ht_ne, ht⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hAcard
    have ha : a = 1 ∨ a = t := by
      by_cases ha : a = 1
      · exact Or.inl ha
      · exact Or.inr (ht a ha)
    have hb : b = 1 ∨ b = t := by
      by_cases hb : b = 1
      · exact Or.inl hb
      · exact Or.inr (ht b hb)
    have ht2 : t * t = 1 := by
      by_cases htt_one : t * t = 1
      · exact htt_one
      · have htt := ht (t * t) htt_one
        have ht_one : t = 1 := by
          have heq := congrArg (fun z : A => t⁻¹ * z) htt
          simpa [mul_assoc] using heq
        exact (ht_ne ht_one).elim
    have hv_inv : v⁻¹ = v := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 V) v)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · simp
    · simp
    · simp
    · simp only [smul_mul', smul_smul, ht2, one_smul]
      rw [hv_inv]
      exact IsMulCommutative.is_comm.comm _ _
  exact commutatorAction₂_eq_bot_of_le_fixedPoints hfirst

/-- Rank-nullity for the displacement map of a nontrivial order-two action
on a four-point elementary abelian module. -/
public theorem cardTwo_action_fixed_card_two
    {Q U : Type u} [Group Q] [Group U] [Finite Q] [Finite U]
    [IsElementaryAbelian 2 U] [MulDistribMulAction Q U]
    (hQcard : Nat.card Q = 2) (hUcard : Nat.card U = 4)
    (hne : commutatorAction Q U ≠ ⊥) :
    Nat.card (FixedPoints.subgroup Q U) = 2 ∧
      commutatorAction Q U ≤ FixedPoints.subgroup Q U := by
  let _ : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hUcard]
    omega)
  obtain ⟨x, hxne, hxuniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQcard
  have hx : IsInvolution x := by
    refine ⟨hxne, ?_⟩
    have hxinv : x⁻¹ ≠ 1 := by simpa using hxne
    have heq : x⁻¹ = x := (hxuniq x⁻¹ hxinv).trans (hxuniq x hxne).symm
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := by rw [heq]
      _ = 1 := inv_mul_cancel x
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  let d : U →* U :=
    { toFun := fun w => w⁻¹ * (x • w)
      map_one' := by simp
      map_mul' := by
        intro w z
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hker : d.ker = FixedPoints.subgroup Q U := by
    ext w
    constructor
    · intro hw
      rw [FixedPoints.mem_subgroup]
      intro r
      have hwx : x • w = w :=
        (eq_of_inv_mul_eq_one (MonoidHom.mem_ker.mp hw)).symm
      by_cases hr : r = 1
      · simp [hr]
      · have hre : r = x := (hxuniq r hr).trans (hxuniq x hxne).symm
        simpa [hre] using hwx
    · intro hw
      rw [MonoidHom.mem_ker]
      have hwx := (FixedPoints.mem_subgroup (M := Q) (a := w)).mp hw x
      exact inv_mul_eq_one.mpr hwx.symm
  have hrange : d.range = commutatorAction Q U := by
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨w, rfl⟩
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨x, w, rfl⟩
    · rw [commutatorAction_eq_closure]
      refine (Subgroup.closure_le (K := d.range)).2 ?_
      rintro z ⟨r, w, rfl⟩
      by_cases hr : r = 1
      · subst r
        exact ⟨1, by simp [d]⟩
      · have hre : r = x := (hxuniq r hr).trans (hxuniq x hxne).symm
        exact ⟨w, by simp [d, hre]⟩
  have hrangeLeKer : d.range ≤ d.ker := by
    intro z hz
    rcases hz with ⟨w, rfl⟩
    rw [MonoidHom.mem_ker]
    have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
    have hxx : x * x = 1 := by simpa [pow_two] using hx.2
    have hexp : Monoid.exponent U = 2 :=
      IsElementaryAbelian.exponent_eq_prime
    have hpow2 (y : U) : y * y = 1 := by
      have hy := Monoid.pow_exponent_eq_one y
      rw [hexp] at hy
      simpa [pow_two] using hy
    have hinvself (y : U) : y⁻¹ = y :=
      (eq_inv_of_mul_eq_one_left (hpow2 y)).symm
    change ((w⁻¹ * (x • w))⁻¹ *
      (x • (w⁻¹ * (x • w)))) = 1
    simp only [mul_inv_rev, smul_mul', smul_inv', ← mul_smul, hxx,
      one_smul]
    simp_rw [hinvself]
    calc
      (x • w) * w * ((x • w) * w) =
          (w * w) * ((x • w) * (x • w)) := by ac_rfl
      _ = 1 := by rw [hpow2, hpow2, one_mul]
  have hproduct : Nat.card U = Nat.card d.ker * Nat.card d.range := by
    calc
      Nat.card U = Nat.card d.ker * d.ker.index := d.ker.card_mul_index.symm
      _ = Nat.card d.ker * Nat.card d.range := by rw [Subgroup.index_ker]
  have hcommGt : 1 < Nat.card d.range := by
    rw [hrange]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hcommLe : Nat.card d.range ≤ Nat.card d.ker :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hrangeLeKer)
      (Subgroup.inclusion_injective hrangeLeKer)
  rw [hUcard] at hproduct
  have hcommDvd : Nat.card d.range ∣ 4 := by
    refine ⟨Nat.card d.ker, ?_⟩
    simpa [Nat.mul_comm] using hproduct
  have hcommCard : Nat.card d.range = 2 := by
    have hcommLeFour : Nat.card d.range ≤ 4 :=
      Nat.le_of_dvd (by norm_num) hcommDvd
    interval_cases hc : Nat.card d.range <;> omega
  constructor
  · rw [hcommCard] at hproduct
    rw [← hker]
    omega
  · simpa [hker, hrange] using hrangeLeKer

/-- A subgroup normalizing the actor preserves its action-commutator
module. -/
public theorem commutatorAction_isInvariant_of_normalizing_actor
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (B A : Subgroup G) (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    IsInvariant B V (commutatorAction A V) := by
  exact _root_.commutatorAction_isInvariant_of_normalizing_actor B A hBA

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
