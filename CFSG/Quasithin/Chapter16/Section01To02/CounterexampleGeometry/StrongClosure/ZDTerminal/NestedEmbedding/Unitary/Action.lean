module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Transfer
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.QuotientAction
public import Theory.GroupTheory.SetStrongClosureImage

/-!
# Transport for the nested unitary quotient action

The faithful restrictions of the terminal quotient action place the original
factors in its actual image in Aut(PSU₃). Surjective-image strong closure and
transport of elementary four-groups preserve every input to the intrinsic
nested-pair problem. The normal span supplies the entire inner automorphism
group in that image. Transporting the resulting innerness back gives both
original factor actions, without any assertion about the ambient action kernel.

`UnitaryNestedPairInnerness` specifies the remaining model calculation. Its
binary specialization must retain the matrix-field cardinality q², the stored
Hermitian fixed-field cardinality q, and the standard Gram matrix. This file
proves only the transport from that explicit input.

Source: Aschbacher (1975), Lemma 3.4, printed pp.94–96, and
GLS, Volume 4, Chapter 2, Theorem ZD(a)–(e).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII
open BenderSuzuki.MatrixGroups

/-- The intrinsic nested-pair calculation needed for the unitary branch.
This is a specification, not an assertion that the model satisfies it.
Every element of both factors must be inner, including elements of order four
or higher. The smaller-factor conclusion of pair rigidity is insufficient. -/
def UnitaryNestedPairInnerness {E : Type*} [Field E] (J : HermitianForm 3 E) : Prop :=
  ∀ (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))),
    (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K →
    ∀ (T : Sylow 2 K) (B₁ B₂ : Subgroup K),
      B₁ ≤ (T : Subgroup K) → B₂ ≤ (T : Subgroup K) →
      ⁅B₁, B₂⁆ = ⊥ → TwoRankAtLeastTwo B₁ → TwoRankAtLeastTwo B₂ →
      IsStronglyClosedSet ((B₁ : Set K) ∪ B₂) (T : Subgroup K) ⊤ →
      (∀ b : K, b ∈ (B₁ : Set K) ∪ B₂ → IsInvolution b →
        (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ∈
          (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range) →
      (B₁ ≤ B₂ ∨ B₂ ≤ B₁) →
      B₁.map K.subtype ≤ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ∧
      B₂.map K.subtype ≤ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- Transport the nested-pair calculation through the actual quotient action.
The codomain is the action image, which contains all inner automorphisms.
No ambient injectivity or odd-kernel premise is used. -/
theorem terminal_nested_unitary_actions_inner_of_model
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hcalc : UnitaryNestedPairInnerness J) :
    let hL := (terminalInvolutions_productDisconnected h f hp).closure_normal
    A₁.map (terminalQuotientAction hL) ≤
      (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range ∧
    A₂.map (terminalQuotientAction hL) ≤
      (MulAut.conj : ((closure (terminalInvolutions A₁ A₂)) ⧸
        pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) →* _).range := by
  let L := closure (terminalInvolutions A₁ A₂)
  have hL : L.Normal := (terminalInvolutions_productDisconnected h f hp).closure_normal
  let ρ := terminalQuotientAction hL
  let φ := (MulAut.congr e).toMonoidHom.comp ρ
  let ψ := φ.rangeRestrict
  let K := φ.range
  let T : Sylow 2 K := S.mapSurjective φ.rangeRestrict_surjective
  let B₁ := A₁.map ψ
  let B₂ := A₂.map ψ
  have hinj (A : Subgroup G) (hA : Function.Injective (ρ.comp A.subtype)) :
      Function.Injective (ψ.comp A.subtype) := by
    intro x y hxy
    apply hA
    apply (MulAut.congr e).injective
    exact congrArg Subtype.val hxy
  have hi₁ := hinj A₁ (terminalQuotientAction_factors_injective hL h hs).1
  have hi₂ := hinj A₂ (terminalQuotientAction_factors_injective hL h hs).2
  have hinner : (MulAut.conj : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L) (e.symm x)
    refine ⟨l, ?_⟩
    change MulAut.congr e (terminalQuotientAction hL (l : G)) = MulAut.conj x
    rw [terminalQuotientAction_inner, hl]
    ext y
    simp [MulAut.congr, MulAut.conj_apply]
  have hrank (A : Subgroup G) (hA : TwoRankAtLeastTwo A)
      (hi : Function.Injective (ψ.comp A.subtype)) : TwoRankAtLeastTwo (A.map ψ) := by
    apply hA.map_of_injective (ψ.subgroupMap A)
    intro x y hxy
    apply hi
    exact congrArg Subtype.val hxy
  have hclosed : IsStronglyClosedSet ((B₁ : Set K) ∪ B₂) (T : Subgroup K) ⊤ := by
    have hh := f.closed.image S ψ φ.rangeRestrict_surjective
    simpa only [B₁, B₂, T, Set.image_union, coe_map, Sylow.coe_mapSurjective] using hh
  have hi : ∀ b : K, b ∈ (B₁ : Set K) ∪ B₂ → IsInvolution b →
      (b : MulAut (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) ∈
        (MulAut.conj : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
    have hgen (A : Subgroup G) (hin : Function.Injective (ψ.comp A.subtype))
        (hAL : ∀ a ∈ A, IsInvolution a → a ∈ L)
        (b : K) (hb : b ∈ A.map ψ) (hbi : IsInvolution b) :
        (b : MulAut (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) ∈
          (MulAut.conj : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
      obtain ⟨a, ha, rfl⟩ := hb
      have ha2 : (⟨a, ha⟩ : A) ^ 2 = 1 := by
        apply hin
        rw [map_pow, map_one]
        exact hbi.sq_eq_one
      have hai : IsInvolution a := ⟨fun he => hbi.ne_one (he ▸ ψ.map_one),
        congrArg Subtype.val ha2⟩
      let aL : L := ⟨a, hAL a ha hai⟩
      refine ⟨e (QuotientGroup.mk' _ aL), ?_⟩
      change MulAut.conj _ = MulAut.congr e (ρ a)
      rw [show ρ a = MulAut.conj (QuotientGroup.mk' _ aL) from terminalQuotientAction_inner hL aL]
      ext y
      simp [MulAut.congr, MulAut.conj_apply]
    intro b hb hbi
    rcases hb with hb | hb
    · exact hgen A₁ hi₁
        (fun _ ha hai => subset_closure (mem_terminalInvolutions (Or.inl ha) hai)) b hb hbi
    · exact hgen A₂ hi₂
        (fun _ ha hai => subset_closure (mem_terminalInvolutions (Or.inr ha) hai)) b hb hbi
  have hc : ⁅B₁, B₂⁆ = ⊥ := by
    change ⁅A₁.map ψ, A₂.map ψ⁆ = ⊥
    rw [← map_commutator, h.commute, Subgroup.map_bot]
  have hn' : B₁ ≤ B₂ ∨ B₂ ≤ B₁ := hn.imp (map_mono (f := ψ)) (map_mono (f := ψ))
  have hout := hcalc K hinner T B₁ B₂ (map_mono h.left_le) (map_mono h.right_le)
    hc (hrank A₁ h.left_rank hi₁) (hrank A₂ h.right_rank hi₂) hclosed hi hn'
  have descend (A : Subgroup G)
      (hA : (A.map ψ).map K.subtype ≤
        (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range) :
      A.map ρ ≤ (MulAut.conj : (L ⧸ pPrimeCore 2 L) →* _).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := hA (mem_map_of_mem K.subtype (mem_map_of_mem ψ ha))
    refine ⟨e.symm x, ?_⟩
    apply (MulAut.congr e).injective
    have he : MulAut.congr e (MulAut.conj (e.symm x)) = MulAut.conj x := by
      ext y
      simp [MulAut.congr, MulAut.conj_apply]
    rw [he]
    exact hx
  exact ⟨descend A₁ hout.1, descend A₂ hout.2⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
