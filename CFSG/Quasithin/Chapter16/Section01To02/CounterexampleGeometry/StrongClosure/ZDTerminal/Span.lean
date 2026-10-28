module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Involutions
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.CentralizerChoice.Seed

/-!
# Strong embedding in the involution span of Asc75 Lemma 3.4

The elementary four in the distinguished involution set kills the central
factor in ZD: modulo the derived group, all three of its nonidentity elements
would have the same image, and their multiplication forces that image to be
one. Disjointness of the two quotient factors and oddness of the kernel then
force the structural square-one element itself to be one. The span is perfect
and its odd-core quotient is an actual simple Bender group.

The existing Borel action argument supplies a nonidentity central involution
modulo the odd core whenever strong embedding fails. The simple Bender
quotient is centerless, contradicting oddness of that core. Finally involution
fusion in the strongly embedded pair puts the span in the normal closure of
the first factor. This last containment does not assert strong embedding in
the larger normal closure; the nested-case deduction remains separate.

Source: Aschbacher (1975), Lemma 3.4, final paragraph, printed p.96;
GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII

private theorem four_constant {E Q : Type*} [Group E] [Group Q]
    (hE : Nat.card E = 4) (φ : E →* Q) (u : Q)
    (hu : ∀ x : E, x ≠ 1 → φ x = u) : u = 1 := by
  classical
  have : Finite E := Nat.finite_of_card_ne_zero (hE ▸ by decide)
  let : Fintype E := Fintype.ofFinite E
  have hc : 2 < Fintype.card E := by rw [← Nat.card_eq_fintype_card, hE]; omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
  let x := a⁻¹ * b
  let y := a⁻¹ * c
  have hx : x ≠ 1 := fun he => hab (inv_mul_eq_one.mp he)
  have hy : y ≠ 1 := fun he => hac (inv_mul_eq_one.mp he)
  have hxy : x ≠ y := by simpa [x, y] using hbc
  have hz : x⁻¹ * y ≠ 1 := fun he => hxy (inv_mul_eq_one.mp he)
  calc
    u = φ (x⁻¹ * y) := (hu _ hz).symm
    _ = (φ x)⁻¹ * φ y := by rw [map_mul, map_inv]
    _ = 1 := by rw [hu x hx, hu y hy, inv_mul_cancel]


private theorem eq_one_of_sq_eq_one_of_mem_oddCore {L : Type*} [Group L] [Finite L]
    {u : L} (hu : u ^ 2 = 1) (hmem : u ∈ pPrimeCore 2 L) : u = 1 := by
  by_contra hne
  have hi : IsInvolution (⟨u, hmem⟩ : pPrimeCore 2 L) :=
    BenderSuzuki.IsInvolution.subtype ⟨hne, hu⟩ hmem
  have ho : Odd (Nat.card (pPrimeCore 2 L)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hd := _root_.orderOf_dvd_natCard (⟨u, hmem⟩ : pPrimeCore 2 L)
  rw [orderOf_eq_prime hi.sq_eq_one hi.ne_one] at hd
  exact ho.not_two_dvd_nat hd

universe u
variable {G : Type u} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

private theorem central_factor_eq_one (h : TwoRankAtLeastTwo A₁)
    (u : closure (terminalInvolutions A₁ A₂)) (hu : u ^ 2 = 1)
    (hdis : Disjoint (commutator ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))))
      (zpowers (QuotientGroup.mk' (pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) u)))
    (hcoset : ∀ z : closure (terminalInvolutions A₁ A₂), (z : G) ∈ terminalInvolutions A₁ A₂ →
      (QuotientGroup.mk' (pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) u)⁻¹ *
        QuotientGroup.mk' (pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) z ∈
          commutator ((closure (terminalInvolutions A₁ A₂)) ⧸
            pPrimeCore 2 (closure (terminalInvolutions A₁ A₂)))) : u = 1 := by
  let L := closure (terminalInvolutions A₁ A₂)
  let O := pPrimeCore 2 L
  let Q := L ⧸ O
  let q := QuotientGroup.mk' O
  let X := commutator Q
  let π : L →* Q ⧸ X := (QuotientGroup.mk' X).comp q
  obtain ⟨E, hE, _, hEZ⟩ := terminalInvolutions_four (A₂ := A₂) h
  have he : π u = 1 := by
    apply four_constant hE (π.comp E.subtype) (π u)
    intro x hx
    exact (QuotientGroup.eq.mpr (hcoset x (hEZ x hx))).symm
  have huX : q u ∈ X := (QuotientGroup.eq_one_iff _).mp he
  have huq : q u = 1 := by
    have hmem : q u ∈ X ⊓ zpowers (q u) := ⟨huX, mem_zpowers _⟩
    rw [hdis.eq_bot, mem_bot] at hmem
    exact hmem
  exact eq_one_of_sq_eq_one_of_mem_oddCore hu ((QuotientGroup.eq_one_iff _).mp huq)

/-- The four-group in the distinguished set removes ZD’s central factor. -/
theorem terminal_structure_perfect_bender (h : TwoRankAtLeastTwo A₁)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    commutator (closure (terminalInvolutions A₁ A₂)) = ⊤ ∧
      BenderSuzuki.IsSimpleBenderGroup ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) := by
  let L := closure (terminalInvolutions A₁ A₂)
  let O := pPrimeCore 2 L
  let Q := L ⧸ O
  let q := QuotientGroup.mk' O
  let X := commutator Q
  obtain ⟨u, _, hu2, hgenL, hgenQ, hdis, _, hmodel, _, _, hcoset⟩ := hs
  have hu1 : u = 1 := central_factor_eq_one h u hu2 hdis (fun z hz => (hcoset z hz).1)
  have hL : commutator L = ⊤ := by simpa [hu1] using hgenL
  have hX : X = ⊤ := by simpa [q, hu1] using hgenQ
  let e : X ≃* Q := MulEquiv.ofBijective X.subtype
    ⟨Subtype.val_injective, fun y => ⟨⟨y, hX ▸ mem_top y⟩, rfl⟩⟩
  exact ⟨hL, hmodel.map_mulEquiv e⟩

/-- The Borel action and odd-core lifting give strong embedding inside the
actual involution span. -/
theorem terminal_stronglyEmbedded_in_span
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    BenderSuzuki.IsStronglyEmbedded
      ((intersectionGenerated A₁ A₂).subgroupOf (closure (terminalInvolutions A₁ A₂))) := by
  by_contra hn
  obtain ⟨u, hu, _, hc, _⟩ := BenderSuzuki.ZD.local_structure_central_involution_seed
    (terminalInvolutions_productDisconnected h f hp) hs hn
  let L := closure (terminalInvolutions A₁ A₂)
  let O := pPrimeCore 2 L
  let Q := L ⧸ O
  let q := QuotientGroup.mk' O
  have hQ : BenderSuzuki.IsSimpleBenderGroup Q := (terminal_structure_perfect_bender h.left_rank hs).2
  have hcenter : center Q = ⊥ := by
    rcases hQ.isSimple.eq_bot_or_eq_top_of_normal (center Q) inferInstance with he | he
    · exact he
    · apply False.elim
      apply hQ.not_commutative
      intro x y
      exact mem_center_iff.mp (he ▸ mem_top y) x
  have hqu : q u = 1 := by
    change q u ∈ center Q at hc
    rwa [hcenter, mem_bot] at hc
  exact hu.ne_one (eq_one_of_sq_eq_one_of_mem_oddCore hu.sq_eq_one
    ((QuotientGroup.eq_one_iff _).mp hqu))


/-- Involution fusion puts the whole span inside the normal closure of A₁. -/
theorem terminal_span_le_normalClosure_left
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂)) :
    closure (terminalInvolutions A₁ A₂) ≤ normalClosure (A₁ : Set G) := by
  let L := closure (terminalInvolutions A₁ A₂)
  let N := normalClosure (A₁ : Set G)
  have hSE := terminal_stronglyEmbedded_in_span h f hp hs
  obtain ⟨a, ha, haZ, hai⟩ := terminalInvolutions_left_seed (A₂ := A₂) h.left_rank
  let aL : L := ⟨a, Subgroup.subset_closure haZ⟩
  apply (Subgroup.closure_le N).mpr
  intro z hz
  let zL : L := ⟨z, Subgroup.subset_closure hz⟩
  obtain ⟨g, hg⟩ := hSE.involutions_conjugate
    (BenderSuzuki.IsInvolution.subtype hai aL.property)
    (BenderSuzuki.IsInvolution.subtype (terminalInvolutions_involutions hz) zL.property)
  have he : (g : G)⁻¹ * a * (g : G) = z := congrArg Subtype.val hg
  rw [← he]
  change (g : G)⁻¹ * a * (g : G) ∈ normalClosure (A₁ : Set G)
  simpa only [inv_inv] using
    (normalClosure_normal (s := (A₁ : Set G))).conj_mem a (subset_normalClosure ha) (g : G)⁻¹

/-- The reduction retains the exact normal subgroup in which
ZD has proved strong embedding. This is not the source alternative (2). -/
theorem terminal_normal_span_of_theoremZD
    (zd : TheoremZD.{u}) (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤) :
    let L := closure (terminalInvolutions A₁ A₂)
    L.Normal ∧ commutator L = ⊤ ∧
      BenderSuzuki.IsSimpleBenderGroup (L ⧸ pPrimeCore 2 L) ∧
      BenderSuzuki.IsStronglyEmbedded ((intersectionGenerated A₁ A₂).subgroupOf L) ∧
      L ≤ normalClosure (A₁ : Set G) := by
  have hs := terminal_structure_of_theoremZD zd h f hp
  have hpb := terminal_structure_perfect_bender h.left_rank hs
  exact ⟨(terminalInvolutions_productDisconnected h f hp).closure_normal,
    hpb.1, hpb.2, terminal_stronglyEmbedded_in_span h f hp hs,
    terminal_span_le_normalClosure_left h f hp hs⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
