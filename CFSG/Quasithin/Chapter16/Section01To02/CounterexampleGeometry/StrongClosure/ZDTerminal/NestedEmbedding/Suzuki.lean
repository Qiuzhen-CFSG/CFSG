module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.Span
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Transfer
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.SpanPlacement.QuotientAction
public import Theory.GroupAction.SylowPointwiseInner
public import Theory.GroupTheory.AutomorphismTowerSimple
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.GroupTheory.SetStrongClosureImage
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Nested-factor absorption for a Suzuki quotient

For nested factors their union is the larger, strongly closed subgroup. Its
conjugation action on the terminal odd-core quotient is faithful. Odd outer
index puts the ambient Sylow subgroup in the preimage K of the inner group.
There is a genuine surjection from K onto the product of the Suzuki group and
K/(L ∩ K): the span L supplies the entire first factor.

A Sylow subgroup of this image is a product. A nonidentity split-torus element
acts without nonidentity fixed points on its Suzuki coordinate and fixes the
second coordinate. Strong closure makes the factor image invariant, and
faithfulness of its first projection makes this action fixed-point-free there.
Surjectivity of the fixed-point-free commutator map therefore kills its second
projection. This handles all root elements, including those of order four.
Thus both original factors lie in L, and normality puts the actual normal
closure of A₁ in L in either nesting orientation.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed pp.94–96; Huppert--Blackburn III, XI.3.1 (root and torus geometry),
and XI.3.3 (the root group is Sylow). The quotient-action construction follows
the same inner-preimage construction used in the saved Suzuki placement proof.
-/

public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

private theorem root_fixed_free (m : ℕ) (hm : 1 ≤ m) :
    ∃ t ∈ normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)),
      ∀ x ∈ SuzukiRootSubgroup m, t⁻¹ * x * t = x → x = 1 := by
  have hc : 1 < Nat.card (SuzukiSplitTorus m) := by
    rw [suzukiSplitTorus_card m hm]
    have hh : 4 ≤ 2 ^ (2*m+1) :=
      (show 4 = 2^2 by norm_num).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  let : Nontrivial (SuzukiSplitTorus m) := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨t, ht⟩ := exists_ne (1 : SuzukiSplitTorus m)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hfree⟩ :=
    BenderSuzuki.External.huppert_blackburn_XI_3_1 m hm
      (iterateFrobeniusEquiv (BinaryGaloisField (2*m+1)) 2 (m+1))
      (BenderSuzuki.External.binaryGaloisField_tits_formula_sq m _
        (iterateFrobeniusEquiv_def _ 2 (m+1)))
  refine ⟨t, suzukiSplitTorus_le_normalizer_root m t.property, ?_⟩
  intro x hx he
  apply Subtype.ext
  apply hfree t.val.val t.property
    (fun hh => ht (Subtype.ext (Subtype.ext hh))) x.val hx
  exact congrArg Subtype.val he

private theorem sylow_fixed_free {Q : Type*} [Group Q] [Finite Q]
    (m : ℕ) (hm : 1 ≤ m) (e : Q ≃* SuzukiMatrixGroup m) (P : Sylow 2 Q) :
    ∃ t ∈ normalizer (P : Set Q),
      ∀ x ∈ (P : Subgroup Q), t⁻¹ * x * t = x → x = 1 := by
  obtain ⟨R, hR⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m)
    (P.mapSurjective (f := e.toMonoidHom) e.surjective) R
  let f := e.trans (MulAut.conj g)
  have hP : (P : Subgroup Q).map f.toMonoidHom = SuzukiRootSubgroup m := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((P : Subgroup Q).map e.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = (R : Subgroup _) at hh
    have hf : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
      ext x; rfl
    rw [hf]
    simpa only [map_map, hR] using hh
  obtain ⟨t, ht, hf⟩ := root_fixed_free m hm
  have hmem (x : Q) : x ∈ (P : Subgroup Q) ↔ f x ∈ SuzukiRootSubgroup m := by
    rw [← hP]
    simpa only [f.symm_apply_apply] using (mem_map_equiv (f := f) (x := f x)).symm
  refine ⟨f.symm t, mem_normalizer_iff.mpr ?_, ?_⟩
  · intro x
    rw [hmem, hmem]
    simpa only [map_mul, map_inv, f.apply_symm_apply] using
      mem_normalizer_iff.mp ht (f x)
  · intro x hx he
    apply f.injective
    rw [map_one]
    apply hf (f x) ((hmem x).mp hx)
    simpa only [map_mul, map_inv, f.apply_symm_apply] using congrArg f he


private theorem sylow_product {Q R : Type*} [Group Q] [Group R] [Finite Q] [Finite R]
    (S : Sylow 2 (Q × R)) :
    (S : Subgroup (Q × R)) =
      ((S : Subgroup (Q × R)).map (MonoidHom.fst Q R)).prod
        ((S : Subgroup (Q × R)).map (MonoidHom.snd Q R)) := by
  let P := (S : Subgroup (Q × R)).map (MonoidHom.fst Q R)
  let T := (S : Subgroup (Q × R)).map (MonoidHom.snd Q R)
  obtain ⟨i, hi⟩ := (S.isPGroup'.map (MonoidHom.fst Q R)).exists_card_eq
  obtain ⟨j, hj⟩ := (S.isPGroup'.map (MonoidHom.snd Q R)).exists_card_eq
  have hp : IsPGroup 2 (P.prod T) := by
    apply IsPGroup.of_card (n := i+j)
    rw [Nat.card_congr (P.prodEquiv T).toEquiv, Nat.card_prod, hi, hj, pow_add]
  exact (S.is_maximal' hp (fun x hx =>
    ⟨mem_map_of_mem _ hx, mem_map_of_mem _ hx⟩)).symm

private theorem product_projection_trivial
    {Q R : Type*} [Group Q] [Group R] [Finite Q] [Finite R]
    (S : Sylow 2 (Q × R)) (A : Subgroup (Q × R))
    (hc : IsStronglyClosedSet (A : Set (Q × R)) (S : Subgroup (Q × R)) ⊤)
    (hi : Function.Injective ((MonoidHom.fst Q R).comp A.subtype))
    (t : Q) (ht : t ∈ normalizer
      (((S : Subgroup (Q × R)).map (MonoidHom.fst Q R)) : Set Q))
    (hf : ∀ x ∈ (S : Subgroup (Q × R)).map (MonoidHom.fst Q R),
      t⁻¹ * x * t = x → x = 1) :
    ∀ a ∈ A, (a : Q × R).2 = 1 := by
  let u : Q × R := (t, 1)
  have hS : ∀ x ∈ (S : Subgroup (Q × R)), u⁻¹ * x * u ∈ (S : Subgroup (Q × R)) := by
    intro x hx
    rw [sylow_product S] at hx ⊢
    refine ⟨?_, ?_⟩
    · change t⁻¹ * x.1 * t ∈ (S : Subgroup (Q × R)).map (MonoidHom.fst Q R)
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp ((normalizer _).inv_mem ht) x.1).mp hx.1
    · simpa [u] using hx.2
  let α : A →* A := ((MulAut.conj u⁻¹).toMonoidHom.comp A.subtype).codRestrict A
    (fun a => by
      change u⁻¹ * (a : Q × R) * (u⁻¹)⁻¹ ∈ (A : Set (Q × R))
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype, MulAut.conj_apply, inv_inv] using
        hc.2 a a.property u (mem_top _) (hS a (hc.1 a.property)))
  have hα : MonoidHom.FixedPointFree α := by
    intro a ha
    apply hi
    change (a : Q × R).1 = 1
    apply hf _ (mem_map_of_mem (MonoidHom.fst Q R) (hc.1 a.property))
    simpa [α, u, MulAut.conj_apply] using
      congrArg (fun a : A => (a : Q × R).1) ha
  let π := (MonoidHom.snd Q R).comp A.subtype
  have hπ (a : A) : π (α a) = π a := by simp [π, α, u, MulAut.conj_apply]
  intro a ha
  obtain ⟨b, hb⟩ := hα.commutatorMap_surjective (⟨a, ha⟩ : A)
  change π (⟨a, ha⟩ : A) = 1
  rw [← hb, MonoidHom.commutatorMap_apply, map_div, hπ, div_self']

private theorem product_image_projection_trivial
    {G Q R : Type*} [Group G] [Finite G] [Group Q] [Group R] [Finite Q] [Finite R]
    (S : Sylow 2 G) (A : Subgroup G)
    (hc : IsStronglyClosedSet (A : Set G) (S : Subgroup G) ⊤)
    (φ : G →* Q × R) (hφ : Function.Surjective φ)
    (hi : Function.Injective (((MonoidHom.fst Q R).comp φ).comp A.subtype))
    (hfree : ∀ P : Sylow 2 Q, ∃ t ∈ normalizer (P : Set Q),
      ∀ x ∈ (P : Subgroup Q), t⁻¹ * x * t = x → x = 1) :
    ∀ a ∈ A, (φ a).2 = 1 := by
  let T := S.mapSurjective hφ
  let B := A.map φ
  have hB : IsStronglyClosedSet (B : Set (Q × R)) (T : Subgroup (Q × R)) ⊤ := by
    exact hc.image S φ hφ
  have hinj : Function.Injective ((MonoidHom.fst Q R).comp B.subtype) := by
    intro a b he
    obtain ⟨a₀, ha₀, hea⟩ := a.property
    obtain ⟨b₀, hb₀, heb⟩ := b.property
    have hh : (⟨a₀, ha₀⟩ : A) = ⟨b₀, hb₀⟩ := hi (by
      change (φ a₀).1 = (φ b₀).1
      change (a : Q × R).1 = (b : Q × R).1 at he
      simpa only [hea, heb] using he)
    exact Subtype.ext (hea.symm.trans ((congrArg (fun x : A => φ x) hh).trans heb))
  obtain ⟨t, ht, hf⟩ := hfree (T.mapSurjective (f := MonoidHom.fst Q R)
    (fun q => ⟨(q, 1), rfl⟩))
  intro a ha
  exact product_projection_trivial T B hB hinj t ht hf (φ a) (mem_map_of_mem φ ha)


open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1 BenderSuzuki.PFAppendixIII
open BenderSuzuki.MatrixGroups

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

private theorem suzuki_centerless (m : ℕ) (hm : 1 ≤ m) :
    center (SuzukiMatrixGroup m) = ⊥ := by
  have hmodel : BenderSuzuki.IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m, hm, ⟨MulEquiv.refl _⟩⟩
  rcases hmodel.isSimple.eq_bot_or_eq_top_of_normal (center _) inferInstance with h | h
  · exact h
  · exact False.elim (hmodel.not_commutative (fun x y =>
      mem_center_iff.mp (h ▸ mem_top y) x))

private theorem closed_factor_le_span
    (hL : (closure (terminalInvolutions A₁ A₂)).Normal)
    (m : ℕ) (hm : 1 ≤ m)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) (hAS : A ≤ (S : Subgroup G))
    (hclosed : IsStronglyClosedSet (A : Set G) (S : Subgroup G) ⊤)
    (hinj : Function.Injective ((terminalQuotientAction hL).comp A.subtype)) :
    A ≤ closure (terminalInvolutions A₁ A₂) := by
  let L := closure (terminalInvolutions A₁ A₂)
  let : L.Normal := hL
  let X := SuzukiMatrixGroup m
  let ρ := terminalQuotientAction hL
  let ψ := (MulAut.congr e).toMonoidHom.comp ρ
  let I := (MulAut.conj : X →* _).range
  let K := I.comap ψ
  have hSK : (S : Subgroup G) ≤ K := by
    intro s hs
    obtain ⟨k, hk⟩ := S.isPGroup' (⟨s, hs⟩ : S)
    have hh : ψ s ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      rw [show s ^ (2 ^ k) = 1 from congrArg Subtype.val hk, map_one]
    obtain ⟨x, hx⟩ := MulAut.inner_of_two_pow_eq_one_of_odd_index
      (suzuki_odd_outer_index m hm) (ψ s) hh
    exact ⟨x, hx.symm⟩
  have hLψ (l : L) : ψ (l : G) = MulAut.conj (e (QuotientGroup.mk' _ l)) := by
    dsimp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ρ]
    rw [terminalQuotientAction_inner, MulAut.congr_conj]
  have hLK : L ≤ K := fun l hl => ⟨e (QuotientGroup.mk' _ ⟨l, hl⟩), (hLψ ⟨l, hl⟩).symm⟩
  let j : X ≃* I :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot (suzuki_centerless m hm))
  let ψK : K →* I := (ψ.comp K.subtype).codRestrict I (fun k => k.property)
  let q : K →* X := j.symm.toMonoidHom.comp ψK
  have hq (k : K) : MulAut.conj (q k) = ψ (k : G) :=
    congrArg Subtype.val (j.apply_symm_apply (ψK k))
  let J := L.subgroupOf K
  let π := QuotientGroup.mk' J
  let φ : K →* X × (K ⧸ J) := q.prod π
  have hcovered (x : X) : ∃ l : K, (l : G) ∈ L ∧ q l = x := by
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L) (e.symm x)
    let k : K := ⟨l, hLK l.property⟩
    refine ⟨k, l.property, MulAut.conj_injective_of_center_eq_bot (suzuki_centerless m hm) ?_⟩
    rw [hq, hLψ l, hl, e.apply_symm_apply]
  have hφ : Function.Surjective φ := by
    rintro ⟨x, r⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective J r
    obtain ⟨l, hl, hql⟩ := hcovered (x * (q k)⁻¹)
    refine ⟨l * k, Prod.ext ?_ ?_⟩
    · change q (l * k) = x
      rw [map_mul, hql, inv_mul_cancel_right]
    · change π (l * k) = r
      have hlπ : π l = 1 := (QuotientGroup.eq_one_iff l).mpr (show l ∈ J from hl)
      rw [map_mul, hlπ, one_mul]
      exact hk
  let B := A.subgroupOf K
  let P := S.subtype hSK
  have hB : IsStronglyClosedSet (B : Set K) (P : Subgroup K) ⊤ := by
    refine ⟨fun b hb => hAS hb, ?_⟩
    intro b hb g _ hbg
    exact hclosed.2 (b : G) hb (g : G) (mem_top _) hbg
  have hiB : Function.Injective (((MonoidHom.fst X (K ⧸ J)).comp φ).comp B.subtype) := by
    intro a b he
    have heq : q (a : K) = q (b : K) := he
    have heρ : ρ ((a : K) : G) = ρ ((b : K) : G) := by
      apply (MulAut.congr e).injective
      exact (hq a).symm.trans ((congrArg MulAut.conj heq).trans (hq b))
    have hab : (⟨(a : K), a.property⟩ : A) = ⟨(b : K), b.property⟩ := hinj heρ
    have habG : ((a : K) : G) = ((b : K) : G) :=
      congrArg (fun x : A => (x : G)) hab
    exact Subtype.ext (Subtype.ext habG)
  have htriv := product_image_projection_trivial P B hB φ hφ hiB
    (sylow_fixed_free m hm (MulEquiv.refl X))
  intro a ha
  let aK : K := ⟨a, hSK (hAS ha)⟩
  exact (QuotientGroup.eq_one_iff aK).mp (htriv aK ha)

/-- The larger strongly closed factor, and hence both nested factors, lie in the
normal involution span for a Suzuki quotient. -/
theorem terminal_nested_factors_le_span_suzuki
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    (m : ℕ) (hm : 1 ≤ m)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* SuzukiMatrixGroup m) :
    A₁ ≤ closure (terminalInvolutions A₁ A₂) ∧
      A₂ ≤ closure (terminalInvolutions A₁ A₂) := by
  have hL := (terminalInvolutions_productDisconnected h f hp).closure_normal
  have hi := terminalQuotientAction_factors_injective hL h hs
  rcases hn with h12 | h21
  · have hc : IsStronglyClosedSet (A₂ : Set G) (S : Subgroup G) ⊤ := by
      simpa only [Set.union_eq_right.mpr h12] using f.closed
    have hA := closed_factor_le_span hL m hm e A₂ h.right_le hc hi.2
    exact ⟨h12.trans hA, hA⟩
  · have hc : IsStronglyClosedSet (A₁ : Set G) (S : Subgroup G) ⊤ := by
      simpa only [Set.union_eq_left.mpr h21] using f.closed
    have hA := closed_factor_le_span hL m hm e A₁ h.left_le hc hi.1
    exact ⟨hA, h21.trans hA⟩

/-- The original left normal closure has no involutions outside the span in the
nested Suzuki case. In fact the entire normal closure lies in the span. -/
theorem terminal_nested_involution_absorption_suzuki
    (h : Hypotheses S A₁ A₂) (f : FusionConclusion S A₁ A₂)
    (hp : intersectionGenerated A₁ A₂ ≠ ⊤)
    (hs : BenderSuzuki.ZD.StructureConclusion (terminalInvolutions A₁ A₂)
      (intersectionGenerated A₁ A₂))
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁)
    (m : ℕ) (hm : 1 ≤ m)
    (e : ((closure (terminalInvolutions A₁ A₂)) ⧸
      pPrimeCore 2 (closure (terminalInvolutions A₁ A₂))) ≃* SuzukiMatrixGroup m) :
    ∀ z ∈ normalClosure (A₁ : Set G), z ∈ intersectionGenerated A₁ A₂ →
      IsInvolution z → z ∈ closure (terminalInvolutions A₁ A₂) := by
  let := (terminalInvolutions_productDisconnected h f hp).closure_normal
  have hA := (terminal_nested_factors_le_span_suzuki h f hp hs hn m hm e).1
  have hN := Subgroup.normalClosure_le_normal hA
  exact fun z hz _ _ => hN hz

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
