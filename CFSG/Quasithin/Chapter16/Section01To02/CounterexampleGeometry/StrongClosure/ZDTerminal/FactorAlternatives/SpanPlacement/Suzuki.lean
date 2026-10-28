module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.QuotientAction
public import Theory.GroupAction.SylowPointwiseInner
public import Theory.GroupTheory.AutomorphismTowerSimple
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.Suzuki.Geometry
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# Terminal factor placement for a Suzuki quotient

Oddness of the Suzuki outer index makes the fixed Sylow subgroup act by
inner automorphisms on the actual odd-core quotient of the involution span.
The preimage of the inner automorphism group therefore contains that Sylow
subgroup and surjects onto the concrete Suzuki group. Strong closure descends
through this surjection without any assumption on its ambient kernel.

Suzuki rigidity nests the factor images, and the split-torus calculation
makes the smaller image have exponent at most two. Injectivity on each
factor reflects the square-one condition, placing both representatives in
the involution span. Injectivity on the Sylow intersection with that span
then identifies them. Thus the original factors nest, contradicting the
given incomparability and proving the requested placement.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed pp.94–96; GLS IV, Chapter 2, Theorem ZD(a)–(e).
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

private theorem suzuki_pair_lift {G X : Type*} [Group G] [Finite G] [Group X]
    (S : Sylow 2 G) (A B : Subgroup G) (hAS : A ≤ S) (hBS : B ≤ S)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    (hcomm : ⁅A, B⁆ = ⊥) (hAr : TwoRankAtLeastTwo A) (hBr : TwoRankAtLeastTwo B)
    (q : G →* X) (hq : Function.Surjective q)
    (hiA : Function.Injective (q.comp A.subtype))
    (hiB : Function.Injective (q.comp B.subtype))
    (hiI : ∀ a ∈ A, ∀ b ∈ B, a ^ 2 = 1 → b ^ 2 = 1 → q a = q b → a = b)
    (hmodel : ∀ (P : Sylow 2 X) (C D : Subgroup X), C ≤ P → D ≤ P →
      ⁅C, D⁆ = ⊥ → TwoRankAtLeastTwo C → TwoRankAtLeastTwo D →
      IsStronglyClosedSet ((C : Set X) ∪ D) (P : Subgroup X) ⊤ →
      (C ≤ D ∧ ∀ x ∈ C, x ^ 2 = 1) ∨ (D ≤ C ∧ ∀ x ∈ D, x ^ 2 = 1)) :
    A ≤ B ∨ B ≤ A := by
  have hmaprank (C : Subgroup G) (hi : Function.Injective (q.comp C.subtype))
      (hr : TwoRankAtLeastTwo C) : TwoRankAtLeastTwo (C.map q) := by
    apply hr.map_of_injective (q.subgroupMap C)
    intro x y he
    exact hi (congrArg Subtype.val he)
  have hclosed : IsStronglyClosedSet ((A.map q : Set X) ∪ B.map q)
      (S.mapSurjective hq : Subgroup X) ⊤ := by
    simpa only [Sylow.coe_mapSurjective, Set.image_union, Subgroup.coe_map] using
      InternalRigidity.stronglyClosed_image S _ hc q hq
  have hmc : ⁅A.map q, B.map q⁆ = ⊥ := by
    rw [← map_commutator, hcomm, Subgroup.map_bot]
  have hsq (C : Subgroup G) (hi : Function.Injective (q.comp C.subtype))
      {c : G} (hc : c ∈ C) (hh : q c ^ 2 = 1) : c ^ 2 = 1 := by
    have he : (⟨c, hc⟩ : C) ^ 2 = 1 := by
      apply hi
      simpa only [map_pow, map_one, MonoidHom.comp_apply, Subgroup.coe_subtype] using hh
    exact congrArg Subtype.val he
  rcases hmodel (S.mapSurjective hq) (A.map q) (B.map q)
      (map_mono hAS) (map_mono hBS) hmc (hmaprank A hiA hAr)
      (hmaprank B hiB hBr) hclosed with ⟨hle, hs⟩ | ⟨hle, hs⟩
  · left
    intro a ha
    have ha2 := hs _ (mem_map_of_mem q ha)
    obtain ⟨b, hb, he⟩ := hle (mem_map_of_mem q ha)
    have hb2 : q b ^ 2 = 1 := he ▸ ha2
    exact (hiI a ha b hb (hsq A hiA ha ha2) (hsq B hiB hb hb2) he.symm) ▸ hb
  · right
    intro b hb
    have hb2 := hs _ (mem_map_of_mem q hb)
    obtain ⟨a, ha, he⟩ := hle (mem_map_of_mem q hb)
    have ha2 : q a ^ 2 = 1 := he ▸ hb2
    exact (hiI a ha b hb (hsq A hiA ha ha2) (hsq B hiB hb hb2) he) ▸ ha

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
/-- Every element of the fixed Sylow group acts inner on a Suzuki quotient. -/
private theorem terminalQuotientAction_suzuki_sylow_inner
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (m : ℕ) (hm : 1 ≤ m)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* SuzukiMatrixGroup m)
    {s : G} (hs : s ∈ (S : Subgroup G)) :
    ∃ x : SuzukiMatrixGroup m,
      MulAut.congr e (terminalQuotientAction hL s) = MulAut.conj x := by
  obtain ⟨k, hk⟩ := S.isPGroup' (⟨s, hs⟩ : S)
  apply MulAut.inner_of_two_pow_eq_one_of_odd_index (suzuki_odd_outer_index m hm)
  rw [← map_pow, ← map_pow]
  have hs' : s ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  rw [hs', map_one, map_one]

private theorem suzuki_centerless (m : ℕ) (hm : 1 ≤ m) :
    center (SuzukiMatrixGroup m) = ⊥ := by
  have hmodel : BenderSuzuki.IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m, hm, ⟨MulEquiv.refl _⟩⟩
  rcases hmodel.isSimple.eq_bot_or_eq_top_of_normal (center _) inferInstance with h | h
  · exact h
  · exact False.elim (hmodel.not_commutative (fun x y =>
      mem_center_iff.mp (h ▸ mem_top y) x))

/-- With a Suzuki quotient, the terminal fusion assumptions force nesting,
contradicting incomparability. In particular both factors lie in the span. -/
theorem terminal_factors_le_span_suzuki
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (m : ℕ) (hm : 1 ≤ m)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* SuzukiMatrixGroup m) :
    A₁ ≤ closure (terminalInvolutions A₁ A₂) ∧
      A₂ ≤ closure (terminalInvolutions A₁ A₂) := by
  have hmodel := suzuki_factors_nested_elementary m hm
  let L := closure (terminalInvolutions A₁ A₂)
  have hL : L.Normal := (terminalInvolutions_productDisconnected h f hp).closure_normal
  let ρ := terminalQuotientAction hL
  let ψ := (MulAut.congr e).toMonoidHom.comp ρ
  let I := (MulAut.conj : SuzukiMatrixGroup m →* _).range
  let N := I.comap ψ
  have hSN : (S : Subgroup G) ≤ N := by
    intro s hs
    obtain ⟨x, hx⟩ := terminalQuotientAction_suzuki_sylow_inner hL m hm e hs
    exact ⟨x, hx.symm⟩
  let j : SuzukiMatrixGroup m ≃* I :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot (suzuki_centerless m hm))
  let ψN : N →* I := (ψ.comp N.subtype).codRestrict I (fun n => n.property)
  let q : N →* SuzukiMatrixGroup m := j.symm.toMonoidHom.comp ψN
  have hq (n : N) : MulAut.conj (q n) = ψ (n : G) := by
    exact congrArg Subtype.val (j.apply_symm_apply (ψN n))
  have hqsurj : Function.Surjective q := by
    intro x
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L) (e.symm x)
    have hlψ : ψ (l : G) = MulAut.conj x := by
      dsimp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ρ]
      rw [terminalQuotientAction_inner, MulAut.congr_conj, hl, e.apply_symm_apply]
    let n : N := ⟨l, ⟨x, hlψ.symm⟩⟩
    refine ⟨n, MulAut.conj_injective_of_center_eq_bot (suzuki_centerless m hm) ?_⟩
    exact (hq n).trans hlψ
  let B := A₁.subgroupOf N
  let C := A₂.subgroupOf N
  let P := S.subtype hSN
  have hBP : B ≤ P := fun _ hx => h.left_le hx
  have hCP : C ≤ P := fun _ hx => h.right_le hx
  have hi := terminalQuotientAction_factors_injective hL h hs
  have hqeq {a b : N} (he : q a = q b) : ρ (a : G) = ρ (b : G) := by
    apply (MulAut.congr e).injective
    exact (hq a).symm.trans ((congrArg MulAut.conj he).trans (hq b))
  have hinj (A : Subgroup G) (hi : Function.Injective (ρ.comp A.subtype)) :
      Function.Injective (q.comp (A.subgroupOf N).subtype) := by
    intro a b he
    have hab : (⟨(a : N), a.property⟩ : A) = ⟨(b : N), b.property⟩ := hi (hqeq he)
    exact Subtype.ext (Subtype.ext (congrArg (fun x : A => (x : G)) hab))
  have hclosed : IsStronglyClosedSet ((B : Set N) ∪ C) (P : Subgroup N) ⊤ := by
    refine ⟨?_, ?_⟩
    · intro x hx
      change x ∈ (P : Subgroup N)
      exact hx.elim (fun hx => hBP hx) (fun hx => hCP hx)
    · intro x hx g _ hxg
      exact f.closed.2 (x : G) hx (g : G) (mem_top _) hxg
  have hcomm : ⁅B, C⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro b hb
    rw [mem_centralizer_iff]
    intro c hc
    exact Subtype.ext (mem_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp h.commute hb) (c : G) hc)
  have hrank (A : Subgroup G) (hAN : A ≤ N) (hr : TwoRankAtLeastTwo A) :
      TwoRankAtLeastTwo (A.subgroupOf N) :=
    hr.map_of_injective (subgroupOfEquivOfLe hAN).symm.toMonoidHom
      (subgroupOfEquivOfLe hAN).symm.injective
  have hiI : ∀ a ∈ B, ∀ b ∈ C, a ^ 2 = 1 → b ^ 2 = 1 → q a = q b → a = b := by
    intro a ha b hb ha2 hb2 he
    have haL : (a : G) ∈ L := by
      by_cases ha1 : (a : G) = 1
      · rw [ha1]; exact L.one_mem
      · exact subset_closure (mem_terminalInvolutions (Or.inl ha)
          ⟨ha1, congrArg Subtype.val ha2⟩)
    have hbL : (b : G) ∈ L := by
      by_cases hb1 : (b : G) = 1
      · rw [hb1]; exact L.one_mem
      · exact subset_closure (mem_terminalInvolutions (Or.inr hb)
          ⟨hb1, congrArg Subtype.val hb2⟩)
    have hρab := hqeq he
    have hinjT := terminalQuotientAction_injective_on_twoSubgroup hL h.left_rank hs
      ((S : Subgroup G) ⊓ L) (S.isPGroup'.to_le inf_le_left) (fun _ hx _ => hx.2)
    have hab : (⟨a, h.left_le ha, haL⟩ : ((S : Subgroup G) ⊓ L : Subgroup G)) =
        ⟨b, h.right_le hb, hbL⟩ := hinjT hρab
    exact Subtype.ext (congrArg
      (fun x : ((S : Subgroup G) ⊓ L : Subgroup G) => (x : G)) hab)
  have hnested := suzuki_pair_lift P B C hBP hCP hclosed hcomm
    (hrank A₁ (h.left_le.trans hSN) h.left_rank)
    (hrank A₂ (h.right_le.trans hSN) h.right_rank)
    q hqsurj (hinj A₁ hi.1) (hinj A₂ hi.2) hiI hmodel
  exfalso
  rcases hnested with hn | hn
  · apply h12
    intro a ha
    exact hn (show (⟨a, hSN (h.left_le ha)⟩ : N) ∈ B from ha)
  · apply h21
    intro a ha
    exact hn (show (⟨a, hSN (h.right_le ha)⟩ : N) ∈ C from ha)
end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end
