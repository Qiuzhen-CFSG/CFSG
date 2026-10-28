module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterA.Section04.Defs
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.MaximalTwoLocalOvergroups

/-!
# The local families in the forward reduction

These are the specializations of Aschbacher–Smith Definition 1.2.3 and
`L_f(G,T) = L(G,T) ∩ X_f` (combined 1 March 2004 manuscript, pp. 505, 507)
to an ambient Sylow two-subgroup `T`. They provide a source-facing boundary
for the final reduction on p. 1166 without depending on chapter recognition.

The component condition is relative to `⟨L,T⟩`. The Sylow condition in
Definition 1.2.3 is automatic here, and `localComponents_iff_source` constructs
the actual Sylow subgroup witnessing it. The definition of `X_f` is reused
from A.4.5–7: it requires `L = O²(L)`, `F*(L) = O₂(L)`, and nontrivial
`V(L) = [Ω₁(Z(O₂(L))),L]`. In particular, no arbitrary family or label replaces
these conditions.

The local setup lemma normalizes the nontrivial core of `⟨L,T⟩` to place it
in an actual maximal two-local. Simplicity makes that overgroup proper;
quasithin and proper-K then supply the SQTK hypothesis used by the chapters.
These definitions specialize the source directly; they do not assert any
chapter classification theorem.
-/

@[expose] public section

namespace CFSG.Quasithin.MainForward

open Theory.GroupTheory

universe u
variable {G : Type u} [Group G]

/-- Definition 1.2.3 with an ambient Sylow subgroup fixed. Its redundant
Sylow clause is recovered explicitly below. -/
def localComponents (T : Sylow 2 G) : Set (Subgroup G) :=
  {L | (L.subgroupOf (L ⊔ (T : Subgroup G))).IsCComponent ∧
    pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥}

/-- The actual faithful local family `L_f(G,T)` from p. 507. -/
def faithfulLocalComponents (T : Sylow 2 G) : Set (Subgroup G) :=
  localComponents T ∩ {L | ChapterA.Section04.IsFaithfulSignalizerType L}

/-- All three clauses of Definition 1.2.3, including an actual Sylow witness
inside the generated subgroup. -/
theorem localComponents_iff_source (T : Sylow 2 G) (L : Subgroup G) :
    L ∈ localComponents T ↔
      (L.subgroupOf (L ⊔ (T : Subgroup G))).IsCComponent ∧
      (∃ S : Sylow 2 (L ⊔ (T : Subgroup G) : Subgroup G),
        (S : Subgroup (L ⊔ (T : Subgroup G) : Subgroup G)) =
          (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))) ∧
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥ :=
  ⟨fun h => ⟨h.1, ⟨T.subtype le_sup_right, rfl⟩, h.2⟩,
    fun h => ⟨h.1, h.2.2⟩⟩

/-- A local component determines a proper SQTK overgroup of `T`, contained
in a genuine member of `M(T)`. No recognition theorem is used. -/
theorem localComponents_local_setup [Finite G] {K : GroupClass.{u}}
    (h : IsSimpleQTKE K G) (T : Sylow 2 G) {L : Subgroup G}
    (hL : L ∈ localComponents T) :
    ∃ M ∈ maximalTwoLocalOvergroups (T : Subgroup G),
      L ⊔ (T : Subgroup G) ≤ M ∧
      (L ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊤ ∧
      IsSQTK K (L ⊔ (T : Subgroup G) : Subgroup G) := by
  obtain ⟨M, hM, hJM⟩ :=
    exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot (L ⊔ (T : Subgroup G)) hL.2
  let := h.simple
  have hMproper := twoLocal_ne_top_of_nonabelian_simple h.nonabelian hM.1
  have hJproper : (L ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊤ := by
    intro htop
    exact hMproper (top_le_iff.mp (htop ▸ hJM))
  have hMsqtk := h.twoLocal_sqtk hM.1
  refine ⟨M, ⟨hM, le_sup_right.trans hJM⟩, hJM, hJproper, ?_⟩
  exact ⟨hMsqtk.stronglyQuasithin.of_injective (Subgroup.inclusion hJM)
      (Subgroup.inclusion_injective hJM), h.properK _ hJproper⟩

end CFSG.Quasithin.MainForward
