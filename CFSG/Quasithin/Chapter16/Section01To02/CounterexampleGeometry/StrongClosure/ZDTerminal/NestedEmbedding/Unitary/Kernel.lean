module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.QuotientAction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Unitary.Kernel.Setup
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Unitary.Kernel.SylowLift
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Unitary.Kernel.UnitaryTorus

/-!
# Fusion and the kernel inside the nested normal closure

A lifted Sylow normalizer element with no nonidentity fixed points on the
quotient Sylow image forces the larger strongly closed factor into the span.
Innerness first puts its image in the image of the span's Sylow intersection.
Centralization of the Sylow part of the ambient kernel then ensures that
conjugation by the lifted element returns the factor to the ambient Sylow.
Strong closure and factor faithfulness give an action without nonidentity
fixed points. Its commutator map is bijective on the finite factor, and all
these commutators belong to the normal span.

The normal closure of A₁ consequently lies in the span in either nesting
orientation. Its action kernel embeds in the odd core of the span, so has
odd order. In the unitary case, the actual model isomorphism transports the
fixed-field torus calculation to the span quotient. Coprime centralizer and
normalizer lifting supply the required ambient element, completing the
kernel theorem. Factor innerness remains an explicit hypothesis for the
parent assembly to discharge.

Source: Aschbacher (1975), Lemma 3.4, printed pp.94–96, terminal application
of Theorem 3.3; Huppert II.10.12 for the required unitary torus geometry.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75


private theorem image_le_span_sylow
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (T : Sylow 2 (closure (terminalInvolutions A₁ A₂)))
    (hT : (T : Subgroup (closure (terminalInvolutions A₁ A₂))) =
      (S : Subgroup G).subgroupOf (closure (terminalInvolutions A₁ A₂)))
    (A : Subgroup G) (hA : A ≤ S)
    (hi : A.map (terminalQuotientAction hL) ≤
      (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range) :
    A.map (terminalQuotientAction hL) ≤
      ((T : Subgroup (closure (terminalInvolutions A₁ A₂))).map
        (closure (terminalInvolutions A₁ A₂)).subtype).map (terminalQuotientAction hL) := by
  let L := closure (terminalInvolutions A₁ A₂)
  let Q := L ⧸ pPrimeCore 2 L
  let ρ := terminalQuotientAction hL
  let c : Q →* MulAut Q := MulAut.conj
  let I := c.range
  let φ : L →* I := c.rangeRestrict.comp (QuotientGroup.mk' (pPrimeCore 2 L))
  have hφ : Function.Surjective φ := c.rangeRestrict_surjective.comp
    (QuotientGroup.mk'_surjective _)
  let P := T.mapSurjective hφ
  let B := ((S : Subgroup G).map ρ).subgroupOf I
  have hB : IsPGroup 2 B := (S.isPGroup'.map ρ).comap_of_injective
    I.subtype I.subtype_injective
  have he (t : L) : (φ t : MulAut Q) = ρ (t : G) :=
    (terminalQuotientAction_inner hL t).symm
  have hPB : (P : Subgroup I) ≤ B := by
    rintro x ⟨t, ht, rfl⟩
    change (φ t : MulAut Q) ∈ (S : Subgroup G).map ρ
    rw [he]
    apply mem_map_of_mem
    rw [hT] at ht
    exact ht
  have hBP : B = (P : Subgroup I) := P.is_maximal' hB hPB
  intro x hx
  have hxB : (⟨x, hi hx⟩ : I) ∈ B := map_mono hA hx
  rw [hBP] at hxB
  obtain ⟨t, ht, htval⟩ := hxB
  refine ⟨t, mem_map_of_mem L.subtype ht, ?_⟩
  exact (he t).symm.trans (congrArg Subtype.val htval)

private theorem closed_le_normal_of_fixedPointFree
    {G H : Type*} [Group G] [Finite G] [Group H]
    (L A S T : Subgroup G) [L.Normal] (ρ : G →* H)
    (hAS : A ≤ S) (hTS : T ≤ S)
    (hc : IsStronglyClosedSet (A : Set G) S ⊤)
    (hi : Function.Injective (ρ.comp A.subtype))
    (hAT : A.map ρ ≤ T.map ρ)
    (g : G) (hgL : g ∈ L) (hgT : g ∈ normalizer (T : Set G))
    (hgK : g ∈ centralizer (S ⊓ ρ.ker : Set G))
    (hf : ∀ t ∈ T, Commute (ρ g) (ρ t) → ρ t = 1) : A ≤ L := by
  have hconj (a : G) (ha : a ∈ A) : g⁻¹ * a * g ∈ A := by
    obtain ⟨t, ht, he⟩ := hAT (mem_map_of_mem ρ ha)
    let k := t⁻¹ * a
    have hkS : k ∈ S := S.mul_mem (S.inv_mem (hTS ht)) (hAS ha)
    have hkK : k ∈ ρ.ker := by
      change ρ (t⁻¹ * a) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hkg : Commute k g := (mem_centralizer_iff.mp hgK k ⟨hkS, hkK⟩)
    have htconj : g⁻¹ * t * g ∈ T := by
      exact (mem_normalizer_iff''.mp hgT t).mp ht
    have heq : g⁻¹ * a * g = (g⁻¹ * t * g) * k := by
      calc
        g⁻¹ * a * g = g⁻¹ * (t * k) * g := by dsimp [k]; group
        _ = (g⁻¹ * t * g) * k := by simp only [mul_assoc]; rw [hkg.eq]
    exact hc.2 a ha g (mem_top g) (heq ▸ S.mul_mem (hTS htconj) hkS)
  let α : A →* A :=
    { toFun := fun a => ⟨g⁻¹ * a * g, hconj a a.property⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [coe_mul]; group) }
  have hfix (a : A) (ha : α a = a) : a = 1 := by
    have he : g⁻¹ * (a : G) * g = a := congrArg Subtype.val ha
    have he' : Commute (ρ g) (ρ (a : G)) := by
      have hm := congrArg ρ he
      simp only [map_mul, map_inv] at hm
      exact (inv_mul_eq_iff_eq_mul.mp (by simpa only [mul_assoc] using hm)).symm
    obtain ⟨t, ht, htρ⟩ := hAT (mem_map_of_mem ρ a.property)
    have haρ : ρ (a : G) = 1 := htρ ▸ hf t ht (htρ ▸ he')
    apply hi
    exact haρ.trans (map_one _).symm
  let δ : A → A := fun a => a⁻¹ * α a
  have hδ : Function.Injective δ := by
    intro a b hab
    have hab' : α (a * b⁻¹) = a * b⁻¹ := by
      have he : a⁻¹ * α a = b⁻¹ * α b := hab
      rw [map_mul, map_inv]
      calc
        α a * (α b)⁻¹ = a * (a⁻¹ * α a) * (α b)⁻¹ := by group
        _ = a * (b⁻¹ * α b) * (α b)⁻¹ := by rw [he]
        _ = a * b⁻¹ := by group
    exact mul_inv_eq_one.mp (hfix _ hab')
  intro a ha
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective hδ (⟨a, ha⟩ : A)
  have he : (b : G)⁻¹ * (g⁻¹ * (b : G) * g) = a := congrArg Subtype.val hb
  rw [← he]
  have hm : (b : G)⁻¹ * g⁻¹ * (b : G) ∈ L := by
    simpa only [inv_inv] using
      (inferInstance : L.Normal).conj_mem g⁻¹ (L.inv_mem hgL) (b : G)⁻¹
  simpa only [mul_assoc] using L.mul_mem hm hgL

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- A Sylow normalizer element, lifted to the span and centralizing the Sylow
part of the ambient action kernel, forces both nested factors into the span.
The fixed-point condition is on the actual quotient action. -/
theorem terminal_nested_factors_le_span_of_sylow_lift
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (hinner : A₁.map (terminalQuotientAction hL) ≤
      (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range ∧
      A₂.map (terminalQuotientAction hL) ≤
      (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range)
    (hlift : TerminalSylowNormalizerLift S hL) :
    A₁ ≤ closure (terminalInvolutions A₁ A₂) ∧
      A₂ ≤ closure (terminalInvolutions A₁ A₂) := by
  let := hL
  obtain ⟨T, hT, g, hgL, hgT, hgK, hgfree⟩ := hlift
  let L := closure (terminalInvolutions A₁ A₂)
  let U := (T : Subgroup L).map L.subtype
  have hUS : U ≤ S := by
    rintro x ⟨t, ht, rfl⟩
    rw [hT] at ht
    exact ht
  have hi := terminalQuotientAction_factors_injective hL h hs
  rcases hn with h12 | h21
  · have hc : IsStronglyClosedSet (A₂ : Set G) (S : Subgroup G) ⊤ := by
      refine ⟨h.right_le, ?_⟩
      intro a ha k hk hak
      exact (f.closed.2 a (Or.inr ha) k hk hak).elim (fun hx => h12 hx) id
    have hA₂ : A₂ ≤ L := closed_le_normal_of_fixedPointFree L A₂ S U
      (terminalQuotientAction hL) h.right_le hUS hc hi.2
      (image_le_span_sylow hL T hT A₂ h.right_le hinner.2)
      g hgL hgT hgK hgfree
    exact ⟨h12.trans hA₂, hA₂⟩
  · have hc : IsStronglyClosedSet (A₁ : Set G) (S : Subgroup G) ⊤ := by
      refine ⟨h.left_le, ?_⟩
      intro a ha k hk hak
      exact (f.closed.2 a (Or.inl ha) k hk hak).elim id (fun hx => h21 hx)
    have hA₁ : A₁ ≤ L := closed_le_normal_of_fixedPointFree L A₁ S U
      (terminalQuotientAction hL) h.left_le hUS hc hi.1
      (image_le_span_sylow hL T hT A₁ h.left_le hinner.1)
      g hgL hgT hgK hgfree
    exact ⟨hA₁, h21.trans hA₁⟩

/-- The kernel in the genuine normal closure has odd order once the Sylow
normalizer lift has been constructed. The normal closure remains that of A₁
in both nesting orientations. This is a conditional reduction. -/
theorem terminal_nested_normalClosure_kernel_odd_of_sylow_lift
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (hinner : A₁.map (terminalQuotientAction hL) ≤
      (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range ∧
      A₂.map (terminalQuotientAction hL) ≤
      (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range)
    (hlift : TerminalSylowNormalizerLift S hL) :
    Odd (Nat.card (normalClosure (A₁ : Set G) ⊓
      (terminalQuotientAction hL).ker : Subgroup G)) := by
  let := hL
  let L := closure (terminalInvolutions A₁ A₂)
  let O := pPrimeCore 2 L
  have hN : normalClosure (A₁ : Set G) ≤ L := normalClosure_le_normal
    (terminal_nested_factors_le_span_of_sylow_lift h f hn hs hL hinner hlift).1
  have hK : normalClosure (A₁ : Set G) ⊓ (terminalQuotientAction hL).ker ≤
      O.map L.subtype := by
    intro x hx
    refine ⟨⟨x, hN hx.1⟩, ?_, rfl⟩
    change (⟨x, hN hx.1⟩ : L) ∈ pPrimeCore 2 L
    exact (terminalQuotientAction_restrict_ker hL h.left_rank hs).le hx.2
  have ho : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact ho.of_dvd_nat ((card_dvd_of_le hK).trans (O.card_map_dvd L.subtype))

/-- For the actual unitary quotient, the action kernel inside the normal
closure of A₁ has odd order in either nesting orientation. The model torus
and its ambient lift are constructed; innerness of both factor images
remains the explicit hypothesis to be discharged by the parent theorem. -/
theorem terminal_nested_unitary_normalClosure_kernel_odd
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    (n : ℕ) (hn₂ : 2 ≤ n)
    {E : Type*} [Field E] [Finite E] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2^n)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃*
        BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hinner : let hL := (terminalInvolutions_productDisconnected h f hp).closure_normal
      A₁.map (terminalQuotientAction hL) ≤
        (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
          pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range ∧
      A₂.map (terminalQuotientAction hL) ≤
        (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
          pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range) :
    let hL := (terminalInvolutions_productDisconnected h f hp).closure_normal
    Odd (Nat.card (normalClosure (A₁ : Set G) ⊓
      (terminalQuotientAction hL).ker : Subgroup G)) := by
  let hL := (terminalInvolutions_productDisconnected h f hp).closure_normal
  apply terminal_nested_normalClosure_kernel_odd_of_sylow_lift h f hn hs hL hinner
  apply terminal_sylowNormalizerLift_of_fixedPointFree_normalizers S hL h.left_rank hs
  intro P
  obtain ⟨d, hd, hfree⟩ := unitary_exists_fixedPointFree_sylow_normalizer
    n hn₂ J hJ hcard hfixed (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  change d ∈ normalizer ((P : Subgroup _).map e.toMonoidHom : Set _) at hd
  rw [← Subgroup.map_equiv_normalizer_eq] at hd
  obtain ⟨d₀, hd₀, rfl⟩ := hd
  refine ⟨d₀, hd₀, ?_⟩
  intro x hx hc
  apply e.injective
  rw [map_one]
  exact hfree (e x) (mem_map_of_mem e.toMonoidHom hx) (hc.map e.toMonoidHom)


end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
