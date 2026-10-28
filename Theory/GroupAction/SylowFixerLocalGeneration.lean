module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Order.Atoms.Finite

/-!
# Pointwise fixers from generating local normalizers

Suppose subgroups Qᵢ of a finite p-subgroup S have C_G(Qᵢ) ≤ Qᵢ, and their
normalizers generate G. Then the full pointwise automorphism fixer of S is
a p-group. For g ∈ N_G(Qᵢ), an automorphism a fixing S has displacement
`g⁻¹ * a(g)` in C_G(Qᵢ), hence in S. Since a fixes that displacement, a power
annihilating S fixes g. The same power fixes every generating normalizer.
No hypothesis on the order or classification of the automorphism is used.

This is the elementary local-normalizer argument used for the Sylow fixer
step of Aschbacher–Smith B.1.13, printed pp.73–74 of `refs/quasithin.pdf`.
The second criterion obtains these normalizers from two proper overgroups of
one Sylow subgroup that generate a finite simple group, assuming characteristic
p for its proper Sylow overgroups. Maximal overgroups normalize their nontrivial
p-cores, so simplicity and maximality make these cores self-centralizing in G.
The concrete application is in the split orthogonal branch of Chapter B.
-/

public section
open Subgroup
namespace Theory.GroupAction.SylowFixerLocalGeneration
variable {G : Type*} [Group G]

private theorem displacement_centralizes (Q : Subgroup G) (a : MulAut G)
    (ha : ∀ q ∈ Q, a q = q) {g : G} (hg : g ∈ normalizer (Q : Set G)) :
    g⁻¹ * a g ∈ centralizer (Q : Set G) := by
  intro q hq
  have he : a g * q * (a g)⁻¹ = g * q * g⁻¹ := by
    simpa only [map_mul, map_inv, ha q hq] using
      ha (g * q * g⁻¹) ((mem_normalizer_iff.mp hg q).mp hq)
  calc
    q * (g⁻¹ * a g) = g⁻¹ * (g * q * g⁻¹) * a g := by group
    _ = g⁻¹ * (a g * q * (a g)⁻¹) * a g := by rw [he]
    _ = (g⁻¹ * a g) * q := by group

private theorem pow_apply_of_fixed_displacement (a : MulAut G) (g : G)
    (ha : a (g⁻¹ * a g) = g⁻¹ * a g) (n : ℕ) :
    (a ^ n) g = g * (g⁻¹ * a g) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change a ((a ^ n) g) = _
    rw [ih, map_mul, map_pow, ha]
    simp only [pow_succ', ← mul_assoc, mul_inv_cancel, one_mul]

/-- Self-centralizing subgroups of a finite p-subgroup whose normalizers
 generate the ambient group bound the entire pointwise automorphism fixer. -/
theorem isPGroup_fixingSubgroup_of_normalizer_generation
    {p : ℕ} (S : Subgroup G) [Finite S] (hS : IsPGroup p S)
    {I : Type*} (Q : I → Subgroup G) (hQS : ∀ i, Q i ≤ S)
    (hC : ∀ i, centralizer (Q i : Set G) ≤ Q i)
    (hgen : (⨆ i, normalizer (Q i : Set G)) = ⊤) :
    IsPGroup p (fixingSubgroup (MulAut G) (S : Set G)) := by
  obtain ⟨k, hk⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hS
  intro a
  refine ⟨k, ?_⟩
  have ha : ∀ x ∈ S, a.val x = x := (mem_fixingSubgroup_iff _).mp a.property
  have hn : (⨆ i, normalizer (Q i : Set G)) ≤
      (a.val ^ (p ^ k)).toMonoidHom.eqLocus (MonoidHom.id G) := by
    refine iSup_le fun i g hg => ?_
    have hd : g⁻¹ * a.val g ∈ S := hQS i (hC i
      (displacement_centralizes (Q i) a.val (fun q hq => ha q (hQS i hq)) hg))
    change (a.val ^ (p ^ k)) g = g
    rw [pow_apply_of_fixed_displacement a.val g (ha _ hd)]
    have he : (g⁻¹ * a.val g) ^ (p ^ k) = 1 := congrArg Subtype.val (hk ⟨_, hd⟩)
    rw [he, mul_one]
  rw [hgen] at hn
  apply Subtype.ext
  apply MulEquiv.ext
  intro g
  exact hn (mem_top g)

section Simple
variable [Finite G] [IsSimpleGroup G] {p : ℕ}

omit [Finite G] in
private theorem coatom_pCore_normalizer (P : Subgroup G)
    (hP : IsCoatom P) (hne : P ≠ ⊥)
    (hchar : centralizer (pCore p P : Set P) ≤ pCore p P) :
    normalizer (P.pCoreIn p : Set G) = P ∧
      centralizer (P.pCoreIn p : Set G) ≤ P.pCoreIn p := by
  have hPN : P ≤ normalizer (P.pCoreIn p : Set G) := by
    have h := (pCore p P).le_normalizer_map P.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h
  have hQne : P.pCoreIn p ≠ ⊥ := by
    intro hbot
    have hc : pCore p P = ⊥ := (map_eq_bot_iff_of_injective (pCore p P) P.subtype_injective).mp hbot
    have hall : ∀ x : P, x = 1 := by
      intro x
      apply mem_bot.mp
      rw [← hc]
      apply hchar
      intro y hy
      have hy1 : y = 1 := by
        change y ∈ pCore p P at hy
        rw [hc, mem_bot] at hy
        exact hy
      simp only [hy1, one_mul, mul_one]
    apply hne
    apply eq_bot_iff.mpr
    intro x hx
    exact congrArg Subtype.val (hall ⟨x, hx⟩)
  have hnorm : normalizer (P.pCoreIn p : Set G) = P := by
    rcases hP.le_iff.mp hPN with ht | he
    · have hn := normalizer_eq_top_iff.mp ht
      rcases hn.eq_bot_or_eq_top with hb | htop
      · exact (hQne hb).elim
      · exact (hP.ne_top (top_le_iff.mp (htop ▸ P.pCoreIn_le p))).elim
    · exact he
  refine ⟨hnorm, ?_⟩
  intro x hx
  have hxP : x ∈ P := hnorm ▸ (Subgroup.centralizer_le_normalizer _ hx)
  have hc : (⟨x, hxP⟩ : P) ∈ centralizer (pCore p P : Set P) := by
    intro y hy
    exact Subtype.ext (hx y (mem_map_of_mem P.subtype hy))
  exact mem_map_of_mem P.subtype (hchar hc)
/-- In a finite simple group, characteristic-p proper Sylow overgroups and
 two proper overgroups generating G force the full Sylow fixer to be a p-group. -/
theorem isPGroup_fixingSubgroup_of_generating_overgroups (S : Sylow p G)
    (hchar : ∀ P : Subgroup G, (S : Subgroup G) ≤ P → P ≠ ⊤ →
      centralizer (pCore p P : Set P) ≤ pCore p P)
    (hpair : ∃ P R : Subgroup G,
      (S : Subgroup G) ≤ P ∧ (S : Subgroup G) ≤ R ∧
      P ≠ ⊤ ∧ R ≠ ⊤ ∧ P ⊔ R = ⊤) :
    IsPGroup p (fixingSubgroup (MulAut G) (S : Set G)) := by
  obtain ⟨P₀, R₀, hSP₀, hSR₀, hP₀, hR₀, hgen₀⟩ := hpair
  obtain ⟨P, hP, hP₀P⟩ := (eq_top_or_exists_le_coatom P₀).resolve_left hP₀
  obtain ⟨R, hR, hR₀R⟩ := (eq_top_or_exists_le_coatom R₀).resolve_left hR₀
  have hSP := hSP₀.trans hP₀P
  have hSR := hSR₀.trans hR₀R
  have hgen : P ⊔ R = ⊤ := top_unique (hgen₀ ▸ sup_le_sup hP₀P hR₀R)
  have hPne : P ≠ ⊥ := by
    intro h
    exact hR.ne_top (by simpa only [h, bot_sup_eq] using hgen)
  have hRne : R ≠ ⊥ := by
    intro h
    exact hP.ne_top (by simpa only [h, sup_bot_eq] using hgen)
  obtain ⟨hPN, hPC⟩ := coatom_pCore_normalizer P hP hPne
    (hchar P hSP hP.ne_top)
  obtain ⟨hRN, hRC⟩ := coatom_pCore_normalizer R hR hRne
    (hchar R hSR hR.ne_top)
  have hPS : P.pCoreIn p ≤ (S : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hSP] using
      pCoreIn_le_sylow P (S.subtype hSP)
  have hRS : R.pCoreIn p ≤ (S : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hSR] using
      pCoreIn_le_sylow R (S.subtype hSR)
  let Q : Bool → Subgroup G := fun b => if b then P.pCoreIn p else R.pCoreIn p
  apply Theory.GroupAction.SylowFixerLocalGeneration.isPGroup_fixingSubgroup_of_normalizer_generation
    (S : Subgroup G) S.isPGroup' Q
  · intro b
    cases b
    · exact hRS
    · exact hPS
  · intro b
    cases b
    · exact hRC
    · exact hPC
  · simpa only [Q, Bool.false_eq_true, ↓reduceIte, iSup_bool_eq, hPN, hRN] using hgen

end Simple

end Theory.GroupAction.SylowFixerLocalGeneration
