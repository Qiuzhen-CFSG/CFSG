module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.Rigidity
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.Parabolics.MarkedComparison
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Construction

/-!
# Applying Ree and Tits local rigidity to the source subgroups

For H ≤ Mc = C_G(Z), a marked isomorphism from either actual first
parabolic makes its distinguished involution central in Mc. The constructed
embedding into Mc therefore satisfies local rigidity once H contains a
Sylow two-subgroup of Mc and Mc has self-centralizing two-core. This proves
H = Mc. The source centralizer decomposition then gives M = YT.

The isomorphisms refer to the actual full-Ree and Tits parabolics, and their
marking refers to the same Z used in C_G(Z). The imported marked comparisons
identify these involutions with Ω₁(Z(T)) in the concrete models. There is
no independent family tag or assumed action on a coordinate space.

Source: Aschbacher--Smith, Lemma 14.2.21, printed pp.988--989. The parent
assembly must obtain the marked isomorphism from genuine amalgam recognition
and the local containment, Sylow, characteristic-two, intersection and
centralizer-decomposition inputs from Hypothesis 14.2.1 and its preliminary
lemmas. These conditional applications complete the Ree/Tits local branch;
they do not assert recognition or the other four amalgam alternatives.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal

open Subgroup ReeTwo.ParabolicConcrete ReeTwo.Centralizer

private theorem eq_of_marked_local
    {A G : Type*} [Group A] [Group G] (z : A)
    (H Mc Z : Subgroup G) (hHMc : H ≤ Mc) (e : A ≃* H)
    (hmark : zpowers (e z : G) = Z) (hMc : Mc = centralizer (Z : Set G))
    (S : Sylow 2 Mc) (hS : (S : Subgroup Mc) ≤ H.subgroupOf Mc)
    (hlocal : ∀ i : A →* Mc, Function.Injective i →
      (S : Subgroup Mc) ≤ i.range → zpowers (i z) ≤ center Mc → i.range = ⊤) :
    H = Mc := by
  let i : A →* Mc := (inclusion hHMc).comp e.toMonoidHom
  have hi : Function.Injective i := (inclusion_injective hHMc).comp e.injective
  have hr : i.range = H.subgroupOf Mc := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).property
    · intro hx
      obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
      exact ⟨a, Subtype.ext (congrArg (fun y : H => (y : G)) ha)⟩
  have hZ : zpowers (i z) ≤ center Mc := by
    apply zpowers_le.mpr
    apply mem_center_iff.mpr
    intro g
    apply Subtype.ext
    have hg : (g : G) ∈ centralizer (Z : Set G) := hMc ▸ g.property
    have hz : (e z : G) ∈ Z := hmark ▸ mem_zpowers _
    exact (hg _ hz).symm
  have ht := hlocal i hi (by rwa [hr]) hZ
  apply le_antisymm hHMc
  intro g hg
  have hm : (⟨g, hg⟩ : Mc) ∈ i.range := ht.ge (mem_top _)
  rw [hr] at hm
  exact hm

/-- The full-Ree branch of H = Mc, with the literal source centralizer
and an actual marked parabolic isomorphism. -/
public theorem ree_eq_mc {G : Type*} [Group G] [Finite G]
    (H Mc Z : Subgroup G) (hHMc : H ≤ Mc)
    (e : Tits.ExceptionalParabolics.FullRee.first ≃* H)
    (hmark : zpowers (e (reeDerivedEmbedding (Multiplicative.ofAdd markedVector)) : G) = Z)
    (hMc : Mc = centralizer (Z : Set G))
    (S : Sylow 2 Mc) (hS : (S : Subgroup Mc) ≤ H.subgroupOf Mc)
    (hc : centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc) : H = Mc := by
  apply eq_of_marked_local _ H Mc Z hHMc e hmark hMc S hS
  intro i hi hSi hZi
  exact (ree_rigidity i hi S hSi hZi hc).1

/-- The Tits branch of H = Mc, using its actual mixed-character parabolic. -/
public theorem tits_eq_mc {G : Type*} [Group G] [Finite G]
    (H Mc Z : Subgroup G) (hHMc : H ≤ Mc)
    (e : Tits.ExceptionalParabolics.first ≃* H)
    (hmark : zpowers (e (titsDerivedEmbedding (Multiplicative.ofAdd markedVector)) : G) = Z)
    (hMc : Mc = centralizer (Z : Set G))
    (S : Sylow 2 Mc) (hS : (S : Subgroup Mc) ≤ H.subgroupOf Mc)
    (hc : centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc) : H = Mc := by
  apply eq_of_marked_local _ H Mc Z hHMc e hmark hMc S hS
  intro i hi hSi hZi
  exact (tits_rigidity i hi S hSi hZi hc).1

/-- Either recognized, marked Ree/Tits first parabolic gives both source
equalities. Recognition and the earlier source-local inputs remain explicit. -/
public theorem rigidity_and_factorization {G : Type*} [Group G] [Finite G]
    (H M Mc Y T Z V : Subgroup G) (hHMc : H ≤ Mc)
    (hmodel :
      (∃ e : Tits.ExceptionalParabolics.FullRee.first ≃* H,
        zpowers (e (reeDerivedEmbedding (Multiplicative.ofAdd markedVector)) : G) = Z) ∨
      (∃ e : Tits.ExceptionalParabolics.first ≃* H,
        zpowers (e (titsDerivedEmbedding (Multiplicative.ofAdd markedVector)) : G) = Z))
    (hMc : Mc = centralizer (Z : Set G))
    (S : Sylow 2 Mc) (hS : (S : Subgroup Mc) ≤ H.subgroupOf Mc)
    (hc : centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc)
    (hint : H ⊓ M = T) (hZV : Z ≤ V)
    (hdecomp : M ≤ (Y ⊔ T) ⊔ (M ⊓ centralizer (V : Set G)))
    (hY : Y ≤ M) (hT : T ≤ M) : H = Mc ∧ M = Y ⊔ T := by
  have he : H = Mc := by
    rcases hmodel with ⟨e, hmark⟩ | ⟨e, hmark⟩
    · exact ree_eq_mc H Mc Z hHMc e hmark hMc S hS hc
    · exact tits_eq_mc H Mc Z hHMc e hmark hMc S hS hc
  exact ⟨he, m_eq_yt_of_rigidity H M Mc Y T Z V he hint hMc hZV hdecomp hY hT⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal
