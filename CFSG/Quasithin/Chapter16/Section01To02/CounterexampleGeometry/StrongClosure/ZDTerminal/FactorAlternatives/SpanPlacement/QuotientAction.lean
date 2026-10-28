module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.Reduction
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# The genuine quotient action for terminal factor placement

Ambient conjugation on the normal involution span descends through its
characteristic odd core. Its restriction to the span has exactly that core
as kernel, because the Bender quotient is centerless. Each original factor
acts faithfully: any nontrivial two-group kernel has an involution, already
in the span, contradicting oddness of the restricted kernel.

These facts concern the actual quotient and its conjugation homomorphism.
They assert neither faithfulness of the entire ambient action nor oddness
of its kernel. Whole-factor placement remains a separate model calculation.

Source: Aschbacher (1975), Lemma 3.4, pp.94–96, terminal appeal to Theorem
3.3; GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Conjugation on the actual odd-core quotient of the terminal span. -/
def terminalQuotientAction
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal) :
    G →* MulAut ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) :=
  letI := hL
  normalQuotientAction _ _

omit [Finite G] in
/-- On elements of the span, the action is inner conjugation by their quotient image. -/
theorem terminalQuotientAction_inner
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (l : closure (terminalInvolutions A₁ A₂)) :
    terminalQuotientAction hL (l : G) =
      MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) l) := by
  let := hL
  exact normalQuotientAction_inner _ _ l

/-- The exact simple Bender quotient has trivial center. -/
theorem terminal_quotient_center_eq_bot (h : TwoRankAtLeastTwo A₁)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    center ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) = ⊥ := by
  have hQ := (terminal_structure_perfect_bender h hs).2
  rcases hQ.isSimple.eq_bot_or_eq_top_of_normal (center _) inferInstance with hc | hc
  · exact hc
  · exact False.elim (hQ.not_commutative (fun x y =>
      mem_center_iff.mp (hc ▸ mem_top y) x))

/-- Restricting the ambient action to the span leaves exactly its odd core as kernel. -/
theorem terminalQuotientAction_restrict_ker
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (h : TwoRankAtLeastTwo A₁)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    ((terminalQuotientAction hL).comp (closure (terminalInvolutions A₁ A₂)).subtype).ker =
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂)) := by
  let L := closure (terminalInvolutions A₁ A₂)
  let O := pPrimeCore 2 L
  let q := QuotientGroup.mk' O
  ext l
  change terminalQuotientAction hL (l : G) = 1 ↔ l ∈ O
  rw [terminalQuotientAction_inner]
  have he : MulAut.conj (q l) = 1 ↔ q l ∈ center (L ⧸ O) := by
    constructor
    · intro hh
      apply mem_center_iff.mpr
      intro x
      have hx := DFunLike.congr_fun hh x
      change q l * x * (q l)⁻¹ = x at hx
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm
    · intro hh
      ext x
      change q l * x * (q l)⁻¹ = x
      rw [← mem_center_iff.mp hh x, mul_inv_cancel_right]
  rw [he, terminal_quotient_center_eq_bot h hs, mem_bot]
  exact QuotientGroup.eq_one_iff l

private theorem injective_of_twoGroup_of_no_involution_in_kernel
    {A Q : Type*} [Group A] [Finite A] [Group Q]
    (hA : IsPGroup 2 A) (φ : A →* Q)
    (hi : ∀ a : A, IsInvolution a → φ a ≠ 1) : Function.Injective φ := by
  apply φ.ker_eq_bot_iff.mp
  by_contra hk
  let K := φ.ker
  have hKt : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hk
  have hKp : IsPGroup 2 K := hA.of_injective K.subtype K.subtype_injective
  obtain ⟨x, hx⟩ := exists_ne (1 : K)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := K) 2
    ((hKp.dvd_orderOf hx).trans (orderOf_dvd_natCard x))
  have hz' : orderOf (z : A) = 2 := by simpa using hz
  exact hi z ⟨(orderOf_eq_prime_iff.mp hz').2, (orderOf_eq_prime_iff.mp hz').1⟩ z.property

/-- Any two-subgroup whose involutions are in the span acts faithfully on its quotient. -/
theorem terminalQuotientAction_injective_on_twoSubgroup
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (h : TwoRankAtLeastTwo A₁)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (A : Subgroup G) (hA : IsPGroup 2 A)
    (hi : ∀ a ∈ A, IsInvolution a → a ∈ closure (terminalInvolutions A₁ A₂)) :
    Function.Injective ((terminalQuotientAction hL).comp A.subtype) := by
  apply injective_of_twoGroup_of_no_involution_in_kernel hA
  intro a ha hker
  have haG : IsInvolution (a : G) :=
    ⟨fun he => ha.ne_one (Subtype.ext he), congrArg Subtype.val ha.sq_eq_one⟩
  let L := closure (terminalInvolutions A₁ A₂)
  let aL : L := ⟨a, hi a a.property haG⟩
  have haO : aL ∈ pPrimeCore 2 L := by
    rw [← terminalQuotientAction_restrict_ker hL h hs]
    exact hker
  have hao : Odd (Nat.card (pPrimeCore 2 L)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  let aO : pPrimeCore 2 L := ⟨aL, haO⟩
  have haOi : IsInvolution aO :=
    ⟨fun he => haG.ne_one (congrArg (fun x : pPrimeCore 2 L => ((x : L) : G)) he),
      Subtype.ext (Subtype.ext haG.sq_eq_one)⟩
  have hd := orderOf_dvd_natCard aO
  rw [orderOf_eq_prime haOi.sq_eq_one haOi.ne_one] at hd
  exact hao.not_two_dvd_nat hd

/-- Both factor restrictions are injective; this says nothing about the remaining ambient kernel. -/
theorem terminalQuotientAction_factors_injective
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (h : Hypotheses S A₁ A₂)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    Function.Injective ((terminalQuotientAction hL).comp A₁.subtype) ∧
      Function.Injective ((terminalQuotientAction hL).comp A₂.subtype) := by
  constructor
  · exact terminalQuotientAction_injective_on_twoSubgroup hL h.left_rank hs A₁
      (S.isPGroup'.to_le h.left_le)
      (fun _ ha hai => subset_closure (mem_terminalInvolutions (Or.inl ha) hai))
  · exact terminalQuotientAction_injective_on_twoSubgroup hL h.left_rank hs A₂
      (S.isPGroup'.to_le h.right_le)
      (fun _ ha hai => subset_closure (mem_terminalInvolutions (Or.inr ha) hai))

omit [Finite G] in
/-- The image of the span is exactly the inner automorphism group of its quotient. -/
theorem terminalQuotientAction_span_image
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal) :
    (closure (terminalInvolutions A₁ A₂)).map (terminalQuotientAction hL) =
      (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk' _ ⟨x, hx⟩, (terminalQuotientAction_inner hL ⟨x, hx⟩).symm⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨l, l.property, terminalQuotientAction_inner hL l⟩

/-- Involutions in the image of either factor are inner; injectivity is
needed to lift an involution in the image to an actual factor involution. -/
theorem terminalQuotientAction_factor_image_involutions_inner
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (h : Hypotheses S A₁ A₂)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    ∀ a, a ∈ ((A₁.map (terminalQuotientAction hL) : Set _) ∪
      A₂.map (terminalQuotientAction hL)) → IsInvolution a →
      a ∈ (closure (terminalInvolutions A₁ A₂)).map (terminalQuotientAction hL) := by
  let ρ := terminalQuotientAction hL
  have hgen (A : Subgroup G) (hinj : Function.Injective (ρ.comp A.subtype))
      (hAL : ∀ x ∈ A, IsInvolution x → x ∈ closure (terminalInvolutions A₁ A₂))
      (a : _) (ha : a ∈ A.map ρ) (hai : IsInvolution a) :
      a ∈ (closure (terminalInvolutions A₁ A₂)).map ρ := by
    obtain ⟨x, hx, rfl⟩ := ha
    let xA : A := ⟨x, hx⟩
    have hx2 : xA ^ 2 = 1 := by
      apply hinj
      rw [map_pow, map_one]
      change ρ x ^ 2 = 1
      exact hai.sq_eq_one
    have hxi : IsInvolution x :=
      ⟨fun he => hai.ne_one (he ▸ ρ.map_one), congrArg Subtype.val hx2⟩
    exact mem_map_of_mem ρ (hAL x hx hxi)
  intro a ha hai
  rcases ha with ha | ha
  · exact hgen A₁ (terminalQuotientAction_factors_injective hL h hs).1
      (fun _ hx hxi => subset_closure (mem_terminalInvolutions (Or.inl hx) hxi)) a ha hai
  · exact hgen A₂ (terminalQuotientAction_factors_injective hL h hs).2
      (fun _ hx hxi => subset_closure (mem_terminalInvolutions (Or.inr hx) hxi)) a ha hai

omit [Finite G] in
/-- Commutation of the factors survives in the actual quotient action. -/
theorem terminalQuotientAction_factor_images_commute
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (h : Hypotheses S A₁ A₂) :
    ⁅A₁.map (terminalQuotientAction hL), A₂.map (terminalQuotientAction hL)⁆ = ⊥ := by
  rw [← map_commutator, h.commute, Subgroup.map_bot]

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
