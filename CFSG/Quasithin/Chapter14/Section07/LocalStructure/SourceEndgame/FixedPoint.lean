module

public import Theory.Representation.SLThreeCentralExtension.SubgroupSplitting
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The fixed-point contradiction in the rank-two U₀ branch

After R splits as V × C_R(L), its fixed factor has order two. T normalizes
that factor and therefore centralizes it. Decomposing an L₁-fixed vector
of U₀ outside V leaves a nonidentity factor in U₀ centralizing LT. The
preceding fixed-element centralizer bound then forces L ≤ H.

The splitting itself is proved from the original natural action and the
actual Sylow image of T ∩ L. No R ≤ L or U₀ ≤ L premise is used.
Source: Aschbacher–Smith 14.7.72, printed p.1076 (1 March 2004 manuscript).
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem fixed_point_outside_natural_of_split
    (L L₁ T R V V₁ U₀ : Subgroup G) [IsElementaryAbelian 2 R]
    (hVR : V ≤ R) (hU₀R : U₀ ≤ R) (hV₁U₀ : V₁ ≤ U₀)
    (hL₁L : L₁ ≤ L) (hU₀fix : U₀ ≤ centralizer (L₁ : Set G))
    (hVfix : V ⊓ centralizer (L₁ : Set G) = V₁)
    (hTL : T ≤ normalizer L) (hTR : T ≤ normalizer R)
    (hsplit : R = V ⊔ (R ⊓ centralizer (L : Set G)))
    (hcard : Nat.card (R ⊓ centralizer (L : Set G) : Subgroup G) = 2)
    (u : U₀) (hu : (u : G) ∉ V) :
    ∃ c ∈ U₀, c ≠ 1 ∧ c ∉ V ∧ c ∈ centralizer ((L ⊔ T : Subgroup G) : Set G) := by
  let C := R ⊓ centralizer (L : Set G)
  have hC : C ≤ R := inf_le_left
  have hnorm : T ≤ normalizer C :=
    (le_inf hTR (hTL.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hTC : T ≤ centralizer (C : Set G) :=
    hnorm.trans (normalizer_le_centralizer_of_card_two C hcard)
  have hsup : V.subgroupOf R ⊔ C.subgroupOf R = ⊤ := by
    rw [← subgroupOf_sup hVR hC, ← hsplit, subgroupOf_self]
  have humem : (⟨u,hU₀R u.property⟩ : R) ∈ V.subgroupOf R ⊔ C.subgroupOf R := by
    rw [hsup]; trivial
  obtain ⟨v,hv,c,hc,he⟩ := mem_sup_of_normal_right.mp humem
  have heG : (v : G) * (c : G) = u := congrArg Subtype.val he
  have hcL₁ : (c : G) ∈ centralizer (L₁ : Set G) :=
    centralizer_le (show (L₁ : Set G) ⊆ L from hL₁L) hc.2
  have hvL₁ : (v : G) ∈ centralizer (L₁ : Set G) := by
    have hh := (centralizer (L₁ : Set G)).mul_mem (hU₀fix u.property)
      ((centralizer (L₁ : Set G)).inv_mem hcL₁)
    rwa [← heG, mul_inv_cancel_right] at hh
  have hvV₁ : (v : G) ∈ V₁ := hVfix ▸ ⟨hv,hvL₁⟩
  have hcU₀ : (c : G) ∈ U₀ := by
    have hh := U₀.mul_mem (U₀.inv_mem (hV₁U₀ hvV₁)) u.property
    rwa [← heG, inv_mul_cancel_left] at hh
  have hcV : (c : G) ∉ V := fun hh => hu (heG ▸ V.mul_mem hv hh)
  refine ⟨c,hcU₀,fun h => hcV (h ▸ V.one_mem),hcV,?_⟩
  have hcT : (c : G) ∈ centralizer (T : Set G) := le_centralizer_iff.mp hTC hc
  have hh : L ⊔ T ≤ centralizer ({(c : G)} : Set G) := sup_le
    (fun l hl => mem_centralizer_singleton_iff.mpr (hc.2 l hl))
    (fun t ht => mem_centralizer_singleton_iff.mpr (hcT t ht))
  intro x hx
  exact (mem_centralizer_singleton_iff.mp (hh hx))

theorem four_space_obstruction
    (L L₁ T H R V V₁ A U₀ : Subgroup G) [IsElementaryAbelian 2 R]
    (hVR : V ≤ R) (hAL : A ≤ L) (hAT : A ≤ T) (hU₀T : U₀ ≤ T)
    (hU₀R : U₀ ≤ R) (hNT : T ≤ normalizer U₀)
    (hNR : L ≤ normalizer R) (hT : IsPGroup 2 T)
    (hfour : Nat.card U₀ = 4) (hRcard : Nat.card R = 16)
    (q : L →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (hk : ∀ l ∈ q.ker, (l : G) ∈ centralizer (R : Set G))
    (hNV : L ≤ normalizer V)
    (cV : V →* Multiplicative BinaryLinearThree.Vector)
    (hcV : Function.Bijective cV)
    (hcn : ∀ (l : L) (v : V),
      (cV ⟨l * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (hNV l.property) v).mp v.property⟩).toAdd =
      BinaryLinearThree.W (q l) (cV v).toAdd)
    (P : Sylow 2 BinaryLinearThree.Group)
    (hP : (q.comp (Subgroup.inclusion hAL)).range = (P : Subgroup _))
    (hcomm : ⁅R,L⁆ ≤ V)
    (hV₁U₀ : V₁ ≤ U₀) (hL₁L : L₁ ≤ L)
    (hU₀fix : U₀ ≤ centralizer (L₁ : Set G))
    (hVfix : V ⊓ centralizer (L₁ : Set G) = V₁)
    (hTL : T ≤ normalizer L) (hTR : T ≤ normalizer R)
    (h68 : ∀ c ∈ U₀, c ≠ 1 → c ∈ centralizer (T : Set G) →
      centralizer ({c} : Set G) ≤ H)
    (hLH : ¬ L ≤ H) : U₀ ≤ V := by
  intro u hu
  by_contra huv
  obtain ⟨hsplit,_,hcard⟩ := BinaryLinearThree.NaturalExtension.natural_four_space_splits
    L R V A T U₀ hVR hAL hAT hU₀T hU₀R hNT hNR hT hfour hRcard
    q hq hk hNV cV hcV hcn P hP hcomm ⟨u,hu⟩ huv
  obtain ⟨c,hc,hc1,_,hcLT⟩ := fixed_point_outside_natural_of_split
    L L₁ T R V V₁ U₀ hVR hU₀R hV₁U₀ hL₁L hU₀fix hVfix hTL hTR hsplit hcard ⟨u,hu⟩ huv
  apply hLH
  apply le_trans ?_ (h68 c hc hc1 (fun t ht => hcLT t (mem_sup_right ht)))
  intro l hl
  rw [mem_centralizer_singleton_iff]
  exact (hcLT l (mem_sup_left hl))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
