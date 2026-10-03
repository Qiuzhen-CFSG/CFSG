module

public import Theory.Comparator.Defs
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.Commutator.ActionTriviality
public import Theory.Representation.ElementaryAbelianAction

/-!
# Inverted odd-order elements on elementary abelian two-groups

This module proves the representation-theoretic size split and containment
used in Stellmacher's proof of Lemma (1.3). If an involution `x` inverts a
nontrivial odd-order element `a` acting faithfully on an elementary abelian
two-group `V`, and `|V| ≤ 4 |C_V(x)|`, then the action commutator `[V, a]`
has order four or sixteen.  In the order-sixteen case it also proves the
source's containment `[V,x] ≤ [V,a]`.

The proof puts `W = [V, ⟨a⟩]`. Coprime action gives
`V = C_V(a) × W`, so the difference map `w ↦ w⁻¹a(w)` is bijective on
`W`. The inversion relation implies that the kernel and range of
`w ↦ w⁻¹x(w)` on `W` coincide; hence `|W|` is the square of the range's
order. That range embeds in `[V,x]`, whose order is at most four by the
fixed-point bound. Faithfulness makes `W` nontrivial, and its elementary
abelian structure leaves square root two or four.  When the square root is
four, the embedding is onto `[V,x]`, giving the containment.

Source: `refs/latex/stellmacher-n-group.tex`, proof of Lemma (1.3), first
central-element split (journal p. 15; LaTeX lines 318--330).
-/
open scoped IsMulCommutative

universe u v

private theorem elementaryAbelian_subgroup
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

private theorem involution_card_eq_fixed_mul_commutator
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite V] [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x : G) (hx : IsInvolution x) :
    Nat.card V =
      Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) *
        Nat.card (commutatorAction (Subgroup.zpowers x) V) := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hcardR : Nat.card R = 2 := by
    simpa [R, Nat.card_zpowers] using hxorder
  let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
  let d : V →* V :=
    { toFun := fun w => w⁻¹ * (x • w)
      map_one' := by simp
      map_mul' := by
        intro w z
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hker : d.ker = FixedPoints.subgroup R V := by
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
          (Nat.card_eq_two_iff' (1 : R)).mp hcardR
        have hrxne : rx ≠ 1 := by
          intro h
          exact hx.1 (congrArg Subtype.val h)
        have hre : r = rx := (hzuniq r hr).trans (hzuniq rx hrxne).symm
        simpa [hre, rx] using hwx
    · intro hw
      rw [MonoidHom.mem_ker]
      have hwx := (FixedPoints.mem_subgroup (M := R) (a := w)).1 hw rx
      exact inv_mul_eq_one.mpr (by simpa [rx] using hwx.symm)
  have hrange : d.range = commutatorAction R V := by
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨w, rfl⟩
      change w⁻¹ * (x • w) ∈ commutatorAction R V
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨rx, w, rfl⟩
    · rw [commutatorAction_eq_closure]
      refine (Subgroup.closure_le (K := d.range)).2 ?_
      intro z hz
      rcases hz with ⟨r, w, rfl⟩
      by_cases hr : r = 1
      · subst r
        exact ⟨1, by simp [d]⟩
      · obtain ⟨z, _hzne, hzuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : R)).mp hcardR
        have hrxne : rx ≠ 1 := by
          intro h
          exact hx.1 (congrArg Subtype.val h)
        have hre : r = rx := (hzuniq r hr).trans (hzuniq rx hrxne).symm
        exact ⟨w, by simp [d, hre, rx]⟩
  calc
    Nat.card V = Nat.card d.ker * d.ker.index := d.ker.card_mul_index.symm
    _ = Nat.card d.ker * Nat.card d.range := by rw [Subgroup.index_ker]
    _ = Nat.card (FixedPoints.subgroup R V) *
        Nat.card (commutatorAction R V) := by rw [hker, hrange]

private theorem involution_commutator_card_le_four
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite V] [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x : G) (hx : IsInvolution x)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V)) :
    Nat.card (commutatorAction (Subgroup.zpowers x) V) ≤ 4 := by
  have hcard := involution_card_eq_fixed_mul_commutator (V := V) x hx
  rw [hcard, mul_comm 4] at hindex
  exact Nat.le_of_mul_le_mul_left hindex Nat.card_pos

private theorem invertedOddElement_size_and_cardSixteen_containment
    {G : Type u} {V : Type v} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (a x : G) (ha : a ≠ 1) (haodd : Nat.Coprime 2 (orderOf a))
    (hx : IsInvolution x) (hinv : x * a * x⁻¹ = a⁻¹)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    (Nat.card (commutatorAction (Subgroup.zpowers a) V) = 4 ∨
      Nat.card (commutatorAction (Subgroup.zpowers a) V) = 2 ^ 4) ∧
    (Nat.card (commutatorAction (Subgroup.zpowers a) V) = 2 ^ 4 →
      commutatorAction (Subgroup.zpowers x) V ≤
        commutatorAction (Subgroup.zpowers a) V) := by
  classical
  let A : Subgroup G := Subgroup.zpowers a
  let R : Subgroup G := Subgroup.zpowers x
  let W : Subgroup V := commutatorAction A V
  let aa : A := ⟨a, Subgroup.mem_zpowers a⟩
  let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
  have hxx : x * x = 1 := by simpa [pow_two] using hx.2
  have hcardR : Nat.card R = 2 := by
    simpa [R, Nat.card_zpowers] using hxorder
  obtain ⟨n, hcardV⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hcardA : Nat.card A = orderOf a := by simp [A, Nat.card_zpowers]
  have hcopAV : Nat.Coprime (Nat.card A) (Nat.card V) := by
    rw [hcardA, hcardV]
    exact haodd.symm.pow_right n
  have hcompl : IsCompl (FixedPoints.subgroup A V) W :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := A)
      (Group.isSolvable_of_comm fun y z =>
        (IsMulCommutative.is_comm (M := V)).comm y z)
      hcopAV (inferInstance : IsMulCommutative V)
  have hWne : W ≠ ⊥ := by
    intro hW
    have htriv : ActsTrivially (A := A) (G := V) :=
      actsTrivially_of_commutatorAction_eq_bot (G := V) (A := A) (by simpa [W] using hW)
    have haFix : a ∈ fixingSubgroup G (Set.univ : Set V) :=
      (mem_fixingSubgroup_iff (M := G) (s := (Set.univ : Set V))).2
        (fun w _ => by simpa [aa] using htriv aa w)
    rw [hfaith] at haFix
    exact ha (by simpa using haFix)
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
  let hWelem : IsElementaryAbelian 2 W := elementaryAbelian_subgroup W
  let : IsElementaryAbelian 2 W := hWelem
  let hAWinv : IsInvariant A V W := commutatorAction_isInvariant
  let : IsInvariant A V W := hAWinv
  let dx : W →* W :=
    { toFun := fun w => w⁻¹ * (rx • w)
      map_one' := by simp
      map_mul' := by
        intro w z
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  let da : W →* W :=
    { toFun := fun w => w⁻¹ * (aa • w)
      map_one' := by simp
      map_mul' := by
        intro w z
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hda_inj : Function.Injective da := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply eq_bot_iff.mpr
    intro w hw
    have hwfix : aa • w = w := by
      exact (eq_of_inv_mul_eq_one (MonoidHom.mem_ker.mp hw)).symm
    have hwfixedA : (w : V) ∈ FixedPoints.subgroup A V := by
      rw [FixedPoints.mem_subgroup]
      intro r
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp r.property
      have haaz : aa ^ z = r := by
        apply Subtype.ext
        simpa [aa] using hz
      have hwfix' : w ∈ MulAction.fixedBy W aa :=
        MulAction.mem_fixedBy.mpr hwfix
      have hwfixz := MulAction.mem_fixedBy_zpow hwfix' z
      rw [MulAction.mem_fixedBy] at hwfixz
      have : r • w = w := by simpa [haaz] using hwfixz
      exact congrArg Subtype.val this
    have hwinf : (w : V) ∈ FixedPoints.subgroup A V ⊓ W := ⟨hwfixedA, w.property⟩
    rw [hcompl.inf_eq_bot] at hwinf
    exact Subtype.ext (by simpa using hwinf)
  have hda_surj : Function.Surjective da := Finite.surjective_of_injective hda_inj
  let : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hWne
  let : Nontrivial V := Function.Injective.nontrivial W.subtype_injective
  have hdx_range_le_ker : dx.range ≤ dx.ker := by
    intro z hz
    rcases hz with ⟨w, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change
      ((w⁻¹ * (x • (w : V)))⁻¹ *
        (x • ((w : V)⁻¹ * (x • (w : V))))) = 1
    have hexp : Monoid.exponent V = 2 := IsElementaryAbelian.exponent_eq_prime
    have hinvself (y : V) : y⁻¹ = y :=
      inv_eq_self_of_exponent_two hexp y
    have hpow2 (y : V) : y * y = 1 := by
      have h := Monoid.pow_exponent_eq_one y
      rw [hexp] at h
      simpa [pow_two] using h
    simp only [mul_inv_rev, smul_mul', smul_inv', ← mul_smul, hxx, one_smul]
    simp_rw [hinvself]
    calc
      (x • (w : V)) * (w : V)⁻¹ * ((x • (w : V)) * (w : V)) =
          ((w : V)⁻¹ * (w : V)) * ((x • (w : V)) * (x • (w : V))) := by
            ac_rfl
      _ = 1 := by rw [inv_mul_cancel, hpow2, one_mul]
  have hax : a * x = x * a⁻¹ := by
    calc
      a * x = (x * x) * a * x := by rw [hxx, one_mul]
      _ = x * (x * a * x⁻¹) := by rw [hxinv]; group
      _ = x * a⁻¹ := by rw [hinv]
  have hrel (w : W) : aa • (rx • w) = rx • (aa⁻¹ • w) := by
    apply Subtype.ext
    change a • (x • (w : V)) = x • (a⁻¹ • (w : V))
    simpa [← mul_smul] using congrArg (fun g : G => g • (w : V)) hax
  have hda_rx (w : W) : da (rx • w) = rx • (aa⁻¹ • da w) := by
    change (rx • w)⁻¹ * (aa • (rx • w)) =
      rx • (aa⁻¹ • (w⁻¹ * (aa • w)))
    rw [hrel]
    simp only [smul_mul', smul_inv', inv_smul_smul]
    have hinvW (z : W) : z⁻¹ = z :=
      inv_eq_self_of_exponent_two IsElementaryAbelian.exponent_eq_prime z
    simp only [hinvW]
    ac_rfl
  have hdx_ker_le_range : dx.ker ≤ dx.range := by
    intro w hw
    have hwfix : rx • w = w :=
      (eq_of_inv_mul_eq_one (MonoidHom.mem_ker.mp hw)).symm
    obtain ⟨u, hu⟩ := hda_surj w
    refine ⟨u, ?_⟩
    apply hda_inj
    have hinvW (z : W) : z⁻¹ = z :=
      inv_eq_self_of_exponent_two IsElementaryAbelian.exponent_eq_prime z
    calc
      da (dx u) = (da u)⁻¹ * da (rx • u) := by
        change da (u⁻¹ * (rx • u)) = _
        rw [map_mul, map_inv]
      _ = w * (rx • (aa⁻¹ • w)) := by rw [hda_rx, hu, hinvW]
      _ = w * (aa • (rx • w)) := by rw [hrel]
      _ = w * (aa • w) := by rw [hwfix]
      _ = da w := by simp [da, hinvW]
  have hdx_ker_range : dx.ker = dx.range :=
    le_antisymm hdx_ker_le_range hdx_range_le_ker
  have hcardW : Nat.card W = Nat.card dx.range * Nat.card dx.range := by
    calc
      Nat.card W = Nat.card dx.ker * dx.ker.index := dx.ker.card_mul_index.symm
      _ = Nat.card dx.ker * Nat.card dx.range := by rw [Subgroup.index_ker]
      _ = Nat.card dx.range * Nat.card dx.range := by rw [hdx_ker_range]
  let Kx : Subgroup V := commutatorAction R V
  let inc : dx.range → Kx := fun z => ⟨((z : W) : V), by
    rcases z.property with ⟨w, hw⟩
    have hz : ((z : W) : V) = (w : V)⁻¹ * (x • (w : V)) := by
      calc
        ((z : W) : V) = ((dx w : W) : V) :=
          congrArg (fun y : W => (y : V)) hw.symm
        _ = (w : V)⁻¹ * (x • (w : V)) := rfl
    rw [hz]
    change (w : V)⁻¹ * (x • (w : V)) ∈ commutatorAction R V
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨rx, (w : V), rfl⟩⟩
  have hinc : Function.Injective inc := by
    intro y z hyz
    apply Subtype.ext
    apply Subtype.ext
    simpa [inc] using congrArg Subtype.val hyz
  have hrange_le_Kx : Nat.card dx.range ≤ Nat.card Kx :=
    Nat.card_le_card_of_injective inc hinc
  have hKx_le_four : Nat.card Kx ≤ 4 := by
    simpa [Kx, R] using involution_commutator_card_le_four (V := V) x hx hindex
  have hrange_le_four : Nat.card dx.range ≤ 4 := hrange_le_Kx.trans hKx_le_four
  have hrange_ne_one : Nat.card dx.range ≠ 1 := by
    intro hrange
    have hWcard : Nat.card W = 1 := by
      calc
        Nat.card W = Nat.card dx.range * Nat.card dx.range := hcardW
        _ = 1 := by rw [hrange]
    exact hWne ((Subgroup.card_eq_one (H := W)).mp hWcard)
  have hrange_even : 2 ∣ Nat.card dx.range := by
    have hP : IsPGroup 2 dx.range :=
      (IsElementaryAbelian.isPGroup 2 W).to_subgroup dx.range
    exact hP.card_eq_or_dvd.resolve_left hrange_ne_one
  have hrange_cases : Nat.card dx.range = 2 ∨ Nat.card dx.range = 4 := by
    rcases hrange_even with ⟨k, hk⟩
    have hrange_pos : 0 < Nat.card dx.range := Nat.card_pos
    omega
  have hsize : Nat.card W = 4 ∨ Nat.card W = 2 ^ 4 := by
    rcases hrange_cases with hrange | hrange
    · left
      rw [hcardW, hrange]
    · right
      rw [hcardW, hrange]
      norm_num
  change (Nat.card W = 4 ∨ Nat.card W = 2 ^ 4) ∧
    (Nat.card W = 2 ^ 4 → Kx ≤ W)
  refine ⟨hsize, ?_⟩
  intro hcardSixteen
  have hcardRange : Nat.card dx.range = 4 := by
    have hsquare : 2 ^ 4 = Nat.card dx.range * Nat.card dx.range :=
      hcardSixteen.symm.trans hcardW
    have hpos : 0 < Nat.card dx.range := Nat.card_pos
    norm_num at hsquare
    nlinarith
  have hcardKx : Nat.card Kx = 4 := by omega
  have hincSurj : Function.Surjective inc :=
    ((Nat.bijective_iff_injective_and_card inc).mpr
      ⟨hinc, by rw [hcardRange, hcardKx]⟩).2
  intro k hk
  obtain ⟨d, hd⟩ := hincSurj ⟨k, hk⟩
  have hval : ((inc d : Kx) : V) = k := congrArg Subtype.val hd
  have hdW : ((inc d : Kx) : V) ∈ W := d.1.property
  simpa [hval] using hdW

/-- An inverted nontrivial odd-order element has action-commutator order four or sixteen
under the index-at-most-four fixed-point bound. -/
public theorem invertedOddElement_commutatorAction_card_eq_four_or_sixteen
    {G : Type u} {V : Type v} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (a x : G) (ha : a ≠ 1) (haodd : Nat.Coprime 2 (orderOf a))
    (hx : IsInvolution x) (hinv : x * a * x⁻¹ = a⁻¹)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    Nat.card (commutatorAction (Subgroup.zpowers a) V) = 4 ∨
      Nat.card (commutatorAction (Subgroup.zpowers a) V) = 2 ^ 4 :=
  (invertedOddElement_size_and_cardSixteen_containment
    a x ha haodd hx hinv hindex hfaith).1

/-- In the card-sixteen case for an inverted odd element, the involution
commutator is contained in the odd element's commutator module. -/
public theorem invertedOddElement_cardSixteen_commutatorAction_le
    {G : Type u} {V : Type v} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (a x : G) (ha : a ≠ 1) (haodd : Nat.Coprime 2 (orderOf a))
    (hx : IsInvolution x) (hinv : x * a * x⁻¹ = a⁻¹)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers a) V) = 2 ^ 4) :
    commutatorAction (Subgroup.zpowers x) V ≤
      commutatorAction (Subgroup.zpowers a) V :=
  (invertedOddElement_size_and_cardSixteen_containment
    a x ha haodd hx hinv hindex hfaith).2 hcard
