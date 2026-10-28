module
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.PCoreSurjective
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The actual Sylow omega-center span at index three

The Sylow subgroup has index three. If its omega center is noncentral,
its centralizer is exactly the Sylow subgroup. The normal closure therefore
has centralizer equal to the ambient two-core. Characteristic two places
that closure in the center of the two-core; its involution generators make
it elementary abelian. The literal centralizer quotient has trivial
two-core, so this same closure is two-reduced.

Source: Kurzweil–Stellmacher §10.3.6, printed p.286, and Aschbacher–Smith
F.7.6–7, pp.312–313. No dimension, depth or classification premise is used.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.SylowOmegaSpan
variable {H : Type*} [Group H]

def seed (S : Sylow 2 H) : Subgroup H := omegaCenterIn (S : Subgroup H)
def span (S : Sylow 2 H) : Subgroup H := normalClosure (seed S : Set H)

instance span_normal (S : Sylow 2 H) : (span S).Normal := inferInstanceAs (normalClosure _).Normal

private theorem seed_centralizes (S : Sylow 2 H) : seed S≤centralizer (S : Set H) :=
  fun _ hx => (mem_omegaCenterIn_iff _ _).mp hx |>.2.1

private theorem seed_le_core (S : Sylow 2 H)
    (hc : centralizer (pCore 2 H : Set H)≤pCore 2 H) : seed S≤pCore 2 H :=
  (seed_centralizes S).trans ((centralizer_le (pCore_isPGroup.le_sylow_of_normal S)).trans hc)

/-- The original Sylow omega-center has Sylow centralizer whenever it is
noncentral and the Sylow has index three. -/
theorem seed_centralizer (S : Sylow 2 H) (hi : (S : Subgroup H).index=3)
    (hn : ¬ seed S≤center H) : centralizer (seed S : Set H)=(S : Subgroup H) := by
  have hs := le_centralizer_iff.mp (seed_centralizes S)
  rcases (isCoatom_of_index_three (S : Subgroup H) hi).le_iff.mp hs with he | he
  · exact (hn (centralizer_eq_top_iff_subset.mp he)).elim
  · exact he

/-- The actual normal closure has centralizer exactly the original two-core. -/
theorem span_centralizer (S : Sylow 2 H) (hi : (S : Subgroup H).index=3)
    (hn : ¬ seed S≤center H) : centralizer (span S : Set H)=pCore 2 H :=
  centralizer_normalClosure_eq_pCore_of_eq_sylow S (seed S) (seed_centralizer S hi hn)

/-- Characteristic two makes the literal normal closure elementary abelian. -/
theorem span_elementary (S : Sylow 2 H)
    (hc : centralizer (pCore 2 H : Set H)≤pCore 2 H) : IsElementaryAbelian 2 (span S) := by
  have hr : seed S≤centralizer (pCore 2 H : Set H) :=
    (seed_centralizes S).trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal S))
  have hvq : span S≤pCore 2 H := normalClosure_le_normal (seed_le_core S hc)
  have hvc : span S≤centralizer (pCore 2 H : Set H) := normalClosure_le_normal hr
  let : IsMulCommutative (normalClosure (seed S : Set H)) := le_centralizer_iff_isMulCommutative.mp
    (hvc.trans (centralizer_le hvq))
  let : IsElementaryAbelian 2 (seed S) := omegaCenterIn_elementary _
  exact IsElementaryAbelian.normalClosure_of_isMulCommutative (seed S)

variable [Finite H]

/-- The same actual closure is two-reduced, with no representation premise. -/
theorem span_reduced (S : Sylow 2 H) (hi : (S : Subgroup H).index=3)
    (hn : ¬ seed S≤center H)
    (hc : centralizer (pCore 2 H : Set H)≤pCore 2 H) : IsPReduced 2 (span S) := by
  refine ⟨inferInstance,span_elementary S hc,?_⟩
  let C := centralizer (span S : Set H)
  have he : C=pCore 2 H := span_centralizer S hi hn
  let q := QuotientGroup.mk' C
  have hk : q.ker=pCore 2 H := (QuotientGroup.ker_mk' _).trans he
  have hp : IsPGroup 2 q.ker := hk ▸ pCore_isPGroup
  have hh := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective C) hp
  apply bot_unique
  intro x hx
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective C x
  have hy : y∈pCore 2 H := hh.le hx
  exact (QuotientGroup.eq_one_iff y).mpr (he ▸ hy)

omit [Finite H] in
theorem span_ne_bot (S : Sylow 2 H) (hn : ¬ seed S≤center H) : span S≠⊥ := by
  intro he
  apply hn
  exact (show seed S≤span S from le_normalClosure).trans (he ▸ bot_le)
end Theory.GroupTheory.SylowOmegaSpan

