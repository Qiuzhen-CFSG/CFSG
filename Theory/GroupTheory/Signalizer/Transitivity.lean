module
public import Theory.GroupTheory.Signalizer.Subgroup
public import Theory.GroupTheory.Signalizer.Conjugation
public import Theory.GroupAction.RankThreeCommonFixedNormalizer
public import Theory.GroupAction.InvariantCommonSylow
public import Theory.GroupTheory.Signalizer.PrimeProduct

/-!
# Transitivity of maximal prime signalizer subgroups

Let an elementary abelian 2-group A of order at least eight act on a finite
group G, and let θ be an odd solvable signalizer family for that action.
For every odd prime q, any two maximal q-subgroups satisfying the family
bounds are conjugate by an element of θ.common, the actual intersection
of all family values. No completeness or ambient solvability is assumed.

Choose a nonconjugate pair whose intersection D has maximal order. Each
member properly contains D. The rank-three fixed-normalizer theorem gives
an actor a whose fixed normalizer escapes D in both members. Within the
odd solvable invariant group N_G(D) ∩ θ(a), invariant Sylow conjugacy puts
these two normalizer pieces in one invariant q-subgroup E, after conjugating
the first by an A-fixed element c. Balance places c in every family value,
so c belongs to θ.common. Moreover c normalizes D and E normalizes D.

The normalized join D ⊔ E is a q-signalizer subgroup and lies in some
maximal one Q₃. Its intersections with the conjugated first member and
the second member both properly contain D. The maximal choice therefore
makes both pairs conjugate under θ.common, contradicting the original
nonconjugacy. Conjugation preserves the family bounds by the previously
proved common-subgroup conjugation lemma.

This is Kurzweil–Stellmacher, *The Theory of Finite Groups*, Lemma 11.1.8
(Transitivity Theorem), printed p.309, specialized to binary actors.
-/

open scoped Pointwise IsMulCommutative

namespace Theory.GroupTheory.TwoSignalizerFamily

variable {A G : Type*} [Group A] [Group G] [MulDistribMulAction A G]

private theorem map_conj_map (U : Subgroup G) (a b : G) :
    (U.map (MulAut.conj a : G →* G)).map (MulAut.conj b : G →* G) =
      U.map (MulAut.conj (b * a) : G →* G) := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  change b * (a * x * a⁻¹) * b⁻¹ = (b * a) * x * (b * a)⁻¹
  group

private theorem map_conj_one (U : Subgroup G) : U.map (MulAut.conj (1 : G) : G →* G) = U := by
  have h : (MulAut.conj (1 : G) : G →* G) = MonoidHom.id G := by
    ext x
    change 1 * x * (1 : G)⁻¹ = x
    simp
  rw [h, Subgroup.map_id]

private def CommonConjugate (θ : TwoSignalizerFamily A G) (U V : Subgroup G) : Prop :=
  ∃ c : G, c ∈ θ.common ∧ V = U.map (MulAut.conj c : G →* G)

private theorem CommonConjugate.refl (θ : TwoSignalizerFamily A G) (U : Subgroup G) :
    CommonConjugate θ U U := by
  refine ⟨1, θ.common.one_mem, ?_⟩
  exact (map_conj_one U).symm

private theorem CommonConjugate.symm {θ : TwoSignalizerFamily A G} {U V : Subgroup G}
    (h : CommonConjugate θ U V) : CommonConjugate θ V U := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c⁻¹, θ.common.inv_mem hc, by rw [map_conj_map, inv_mul_cancel, map_conj_one]⟩

private theorem CommonConjugate.trans {θ : TwoSignalizerFamily A G} {U V W : Subgroup G}
    (h : CommonConjugate θ U V) (k : CommonConjugate θ V W) : CommonConjugate θ U W := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := k
  exact ⟨d * c, θ.common.mul_mem hd hc, map_conj_map U c d⟩

private theorem maximal_map_conj {θ : TwoSignalizerFamily A G} {q : ℕ}
    {Q : Subgroup G}
    (hQ : Maximal (fun U => θ.IsSignalizerSubgroup U ∧ IsPGroup q U) Q)
    {c : G} (hc : c ∈ θ.common) :
    Maximal (fun U => θ.IsSignalizerSubgroup U ∧ IsPGroup q U)
      (Q.map (MulAut.conj c : G →* G)) := by
  refine ⟨⟨hQ.1.1.map_conj_of_mem_common hc, hQ.1.2.map _⟩, ?_⟩
  intro U hU hQU
  have hU' : θ.IsSignalizerSubgroup (U.map (MulAut.conj c⁻¹ : G →* G)) ∧
      IsPGroup q (U.map (MulAut.conj c⁻¹ : G →* G)) :=
    ⟨hU.1.map_conj_of_mem_common (θ.common.inv_mem hc), hU.2.map _⟩
  have hQle : Q ≤ U.map (MulAut.conj c⁻¹ : G →* G) := by
    have h := Subgroup.map_mono hQU (f := (MulAut.conj c⁻¹ : G →* G))
    simpa only [map_conj_map, inv_mul_cancel, map_conj_one] using h
  have hle := Subgroup.map_mono (hQ.2 hU' hQle) (f := (MulAut.conj c : G →* G))
  simpa only [map_conj_map, mul_inv_cancel, map_conj_one] using hle

private theorem core_transitivity [Finite G]
    (θ : TwoSignalizerFamily A G) {q : ℕ}
    (hprod : ∀ D E : Subgroup G, θ.IsSignalizerSubgroup D → θ.IsSignalizerSubgroup E →
      IsPGroup q D → IsPGroup q E → E ≤ Subgroup.normalizer (D : Set G) →
      θ.IsSignalizerSubgroup (D ⊔ E) ∧ IsPGroup q (D ⊔ E : Subgroup G))
    (henlarge : ∀ Q₁ Q₂ : Subgroup G,
      Maximal (fun U => θ.IsSignalizerSubgroup U ∧ IsPGroup q U) Q₁ →
      Maximal (fun U => θ.IsSignalizerSubgroup U ∧ IsPGroup q U) Q₂ →
      Q₁ ⊓ Q₂ < Q₁ → Q₁ ⊓ Q₂ < Q₂ →
      ∃ c : G, c ∈ θ.common ∧ c ∈ Subgroup.normalizer (↑(Q₁ ⊓ Q₂) : Set G) ∧
      ∃ E : Subgroup G, θ.IsSignalizerSubgroup E ∧ IsPGroup q E ∧
        E ≤ Subgroup.normalizer (↑(Q₁ ⊓ Q₂) : Set G) ∧
        ¬ Q₁.map (MulAut.conj c : G →* G) ⊓ E ≤ Q₁ ⊓ Q₂ ∧
        ¬ Q₂ ⊓ E ≤ Q₁ ⊓ Q₂)
    (Q₁ Q₂ : Subgroup G)
    (hQ₁ : Maximal (fun U => θ.IsSignalizerSubgroup U ∧ IsPGroup q U) Q₁)
    (hQ₂ : Maximal (fun U => θ.IsSignalizerSubgroup U ∧ IsPGroup q U) Q₂) :
    CommonConjugate θ Q₁ Q₂ := by
  classical
  let P : Subgroup G → Prop := fun U => θ.IsSignalizerSubgroup U ∧ IsPGroup q U
  let bad : Set (Subgroup G × Subgroup G) :=
    {p | Maximal P p.1 ∧ Maximal P p.2 ∧ ¬ CommonConjugate θ p.1 p.2}
  by_contra hbad
  obtain ⟨⟨R₁, R₂⟩, ⟨hR₁, hR₂, hRbad⟩, hmax⟩ :=
    bad.exists_max_image (fun p => Nat.card (p.1 ⊓ p.2 : Subgroup G)) bad.toFinite
      ⟨(Q₁, Q₂), hQ₁, hQ₂, hbad⟩
  have hne : R₁ ≠ R₂ := by
    rintro rfl
    exact hRbad (CommonConjugate.refl θ R₁)
  have hproper₁ : R₁ ⊓ R₂ < R₁ := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hle : R₁ ≤ R₂ := heq ▸ inf_le_right
    exact hne (le_antisymm hle (hR₁.2 hR₂.1 hle))
  have hproper₂ : R₁ ⊓ R₂ < R₂ := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    have hle : R₂ ≤ R₁ := heq ▸ inf_le_left
    exact hne (le_antisymm (hR₂.2 hR₁.1 hle) hle)
  let D := R₁ ⊓ R₂
  let _ : IsInvariant A G R₁ := hR₁.1.1.2.2.1
  let _ : IsInvariant A G R₂ := hR₂.1.1.2.2.1
  have hDI : IsInvariant A G D := isInvariant_inf R₁ R₂
  have hD : θ.IsSignalizerSubgroup D := hR₁.1.1.mono inf_le_left hDI
  have hDp : IsPGroup q D := hR₁.1.2.to_le inf_le_left
  obtain ⟨c, hc, hcN, E, hE, hEp, hEN, hescape₁, hescape₂⟩ :=
    henlarge R₁ R₂ hR₁ hR₂ hproper₁ hproper₂
  obtain ⟨R₃, hDR₃, hR₃⟩ := Finite.exists_le_maximal (p := P)
    (hprod D E hD hE hDp hEp hEN)
  have hDle : D ≤ R₃ := le_sup_left.trans hDR₃
  have hEle : E ≤ R₃ := le_sup_right.trans hDR₃
  have hDconj : D.map (MulAut.conj c : G →* G) = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hcN
  have hDconjle : D ≤ R₁.map (MulAut.conj c : G →* G) := by
    rw [← hDconj]
    exact Subgroup.map_mono inf_le_left
  have hlt₁ : D < R₁.map (MulAut.conj c : G →* G) ⊓ R₃ := by
    refine lt_of_le_of_ne (le_inf hDconjle hDle) ?_
    intro heq
    apply hescape₁
    exact (inf_le_inf_left _ hEle).trans heq.ge
  have hlt₂ : D < R₂ ⊓ R₃ := by
    refine lt_of_le_of_ne (le_inf inf_le_right hDle) ?_
    intro heq
    exact hescape₂ ((inf_le_inf_left _ hEle).trans heq.ge)
  have bigger (U V : Subgroup G) (hU : Maximal P U) (hV : Maximal P V)
      (hlt : D < U ⊓ V) : CommonConjugate θ U V := by
    by_contra hn
    have hle := hmax (U, V) ⟨hU, hV, hn⟩
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le hle)
  have hconj₁ := bigger _ R₃ (maximal_map_conj hR₁ hc) hR₃ hlt₁
  have hconj₂ := bigger R₂ R₃ hR₂ hR₃ hlt₂
  exact hRbad ((CommonConjugate.trans
    (show CommonConjugate θ R₁ (R₁.map (MulAut.conj c : G →* G)) from ⟨c, hc, rfl⟩)
    hconj₁).trans hconj₂.symm)

private theorem exists_enlarging_common_overgroup [Finite A] [Finite G]
    [IsElementaryAbelian 2 A] (θ : TwoSignalizerFamily A G)
    {q : ℕ} [Fact q.Prime] (hA : 8 ≤ Nat.card A) (hq : q ≠ 2)
    (Q₁ Q₂ : Subgroup G) (hQ₁ : θ.IsSignalizerSubgroup Q₁)
    (hQ₂ : θ.IsSignalizerSubgroup Q₂) (hp₁ : IsPGroup q Q₁) (hp₂ : IsPGroup q Q₂)
    (hproper₁ : Q₁ ⊓ Q₂ < Q₁) (hproper₂ : Q₁ ⊓ Q₂ < Q₂) :
    ∃ c : G, c ∈ θ.common ∧ c ∈ Subgroup.normalizer (↑(Q₁ ⊓ Q₂) : Set G) ∧
      ∃ E : Subgroup G, θ.IsSignalizerSubgroup E ∧ IsPGroup q E ∧
        E ≤ Subgroup.normalizer (↑(Q₁ ⊓ Q₂) : Set G) ∧
        ¬ Q₁.map (MulAut.conj c : G →* G) ⊓ E ≤ Q₁ ⊓ Q₂ ∧
        ¬ Q₂ ⊓ E ≤ Q₁ ⊓ Q₂ := by
  let _ : IsInvariant A G Q₁ := hQ₁.2.2.1
  let _ : IsInvariant A G Q₂ := hQ₂.2.2.1
  let D := Q₁ ⊓ Q₂
  let _ : IsInvariant A G D := isInvariant_inf Q₁ Q₂
  let _ : IsInvariant A G (Subgroup.normalizer (D : Set G)) := isInvariant_normalizer D
  obtain ⟨a, ha, ha₁, ha₂⟩ :=
    exists_nontrivial_common_fixed_normalizer hA hq Q₁ Q₂ hp₁ hp₂ hproper₁ hproper₂
  let a' : {a : A // a ≠ 1} := ⟨a, ha⟩
  let _ : IsInvariant A G (θ.subgroup a') := θ.invariant a'
  let N := Subgroup.normalizer (D : Set G) ⊓ θ.subgroup a'
  let _ : IsInvariant A G N := isInvariant_inf _ _
  have hNodd : Odd (Nat.card N) := (θ.odd a').of_dvd_nat
    (Subgroup.card_dvd_of_le (show N ≤ θ.subgroup a' from inf_le_right))
  have hNsolv : Group.IsSolvable N := by
    let _ := θ.solvable a'
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (show N ≤ θ.subgroup a' from inf_le_right))
  have hsubp (Q : Subgroup G) (hQ : IsPGroup q Q) : IsPGroup q (Q.subgroupOf N) := by
    let f : Q.subgroupOf N →* Q :=
      { toFun := fun x => ⟨x.val.val, x.property⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    exact hQ.of_injective f (fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : Q => (z : G)) h)))
  obtain ⟨c, hcfix, E₀, hE₀p, hE₀I, h₁E, h₂E⟩ :=
    exists_fixedPoint_conj_le_common_invariant_pSubgroup
      (IsElementaryAbelian.isPGroup 2 A) hNodd hNsolv
      (Q₁.subgroupOf N) (Q₂.subgroupOf N) (hsubp Q₁ hp₁) (hsubp Q₂ hp₂)
      (isInvariant_subgroupOf Q₁ N) (isInvariant_subgroupOf Q₂ N)
  let _ : IsInvariant A N E₀ := hE₀I
  let E := E₀.map N.subtype
  have hEI : IsInvariant A G E := isInvariant_map_subtype N E₀
  have hEN : E ≤ N := Subgroup.map_subtype_le E₀
  have hE : θ.IsSignalizerSubgroup E :=
    (θ.value_isSignalizerSubgroup a').mono (hEN.trans inf_le_right) hEI
  have hccommon : (c : G) ∈ θ.common := by
    apply Subgroup.mem_iInf.mpr
    intro b
    apply θ.balance a' b
    refine ⟨c.property.2, ?_⟩
    intro z
    exact congrArg Subtype.val (hcfix z.val)
  have hcD : (MulAut.conj (c : G) : G →* G) '' (D : Set G) = D := by
    exact congrArg (fun H : Subgroup G => (H : Set G))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp c.property.1)
  refine ⟨c, hccommon, c.property.1, E, hE, hE₀p.map N.subtype,
    hEN.trans inf_le_left, ?_, ?_⟩
  · intro hle
    apply ha₁
    intro x hx
    have hxN : x ∈ N := ⟨hx.1.2, hQ₁.2.2.2 a' ⟨hx.1.1, hx.2⟩⟩
    let xN : N := ⟨x, hxN⟩
    have hcxE : (MulAut.conj (c : G) : G →* G) x ∈ E := by
      refine ⟨(MulAut.conj c : N →* N) xN, h₁E ?_, rfl⟩
      exact ⟨xN, hx.1.1, rfl⟩
    have hcxD : (MulAut.conj (c : G) : G →* G) x ∈ D :=
      hle ⟨⟨x, hx.1.1, rfl⟩, hcxE⟩
    change (MulAut.conj (c : G) : G →* G) x ∈ (D : Set G) at hcxD
    rw [← hcD] at hcxD
    obtain ⟨y, hy, heq⟩ := hcxD
    have hyx : y = x := (MulAut.conj (c : G)).injective heq
    exact hyx ▸ hy
  · intro hle
    apply ha₂
    intro x hx
    have hxN : x ∈ N := ⟨hx.1.2, hQ₂.2.2.2 a' ⟨hx.1.1, hx.2⟩⟩
    have hxE : x ∈ E := ⟨⟨x, hxN⟩, h₂E hx.1.1, rfl⟩
    exact hle ⟨hx.1.1, hxE⟩

/-- Maximal q-signalizer subgroups are conjugate under the common subgroup. -/
public theorem maximal_pSubgroups_conjugate [Finite A] [Finite G]
    [IsElementaryAbelian 2 A] (θ : TwoSignalizerFamily A G)
    {q : ℕ} [Fact q.Prime] (hA : 8 ≤ Nat.card A) (hq : q ≠ 2)
    (Q₁ Q₂ : Subgroup G)
    (hQ₁ : Maximal (fun U : Subgroup G => θ.IsSignalizerSubgroup U ∧ IsPGroup q U) Q₁)
    (hQ₂ : Maximal (fun U : Subgroup G => θ.IsSignalizerSubgroup U ∧ IsPGroup q U) Q₂) :
    ∃ c : G, c ∈ θ.common ∧ Q₂ = Q₁.map (MulAut.conj c : G →* G) := by
  apply core_transitivity θ
    (fun D E hD hE hDp hEp hED => hD.sup_of_normalizes_pGroup hE hq hDp hEp hED)
    (fun R₁ R₂ hR₁ hR₂ hproper₁ hproper₂ =>
      exists_enlarging_common_overgroup θ hA hq R₁ R₂ hR₁.1.1 hR₂.1.1
        hR₁.1.2 hR₂.1.2 hproper₁ hproper₂) Q₁ Q₂ hQ₁ hQ₂

end Theory.GroupTheory.TwoSignalizerFamily
