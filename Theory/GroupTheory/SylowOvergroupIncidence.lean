module

public import Theory.GroupTheory.SubgroupConjugateIncidence
public import Mathlib.GroupTheory.Sylow

/-!
# Uniqueness of conjugate overgroups of a Sylow subgroup

Let S be a Sylow p-subgroup of a finite group and let M contain S.
Sylow conjugacy inside M shows that M controls fusion of S into M.
Consequently, if the ambient normalizer of S normalizes M, every conjugate
of M containing S equals M. In particular this holds when S is
self-normalizing in the ambient group.

This is the Sylow specialization of the transporter argument in
`SubgroupConjugateIncidence`. The application to J₄ in Aschbacher–Smith,
printed p.511 (PDF p.528 of `refs/quasithin.pdf`), additionally needs actual
conjugacy and normalizer calculations in that group; neither is asserted here.
-/

open Subgroup
open scoped Pointwise

namespace Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A subgroup containing an ambient Sylow subgroup controls its fusion
back into that subgroup. The conjugator is an element of the overgroup. -/
public theorem exists_overgroup_conjugator (S : Sylow p G)
    (M : Subgroup G) (hSM : S.toSubgroup ≤ M) (g : G)
    (hg : S.toSubgroup.map (MulAut.conj g).toMonoidHom ≤ M) :
    ∃ n ∈ M, S.toSubgroup.map (MulAut.conj n).toMonoidHom =
      S.toSubgroup.map (MulAut.conj g).toMonoidHom := by
  have hgSM : (g • S).toSubgroup ≤ M := hg
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq M
    (S.subtype hSM) ((g • S).subtype hgSM)
  refine ⟨n, n.property, ?_⟩
  have hs : (n : G) • S = g • S :=
    Sylow.subtype_injective ((S.smul_subtype hSM n).symm.trans hn)
  exact congrArg Sylow.toSubgroup hs

/-- Normalizer control makes a conjugacy class of overgroups meet the
overgroups of S in at most one subgroup. -/
public theorem conjugate_overgroup_eq_of_normalizer_le (S : Sylow p G)
    (M : Subgroup G) (hSM : S.toSubgroup ≤ M)
    (hN : normalizer (S : Set G) ≤ normalizer (M : Set G))
    (g : G) (hg : S.toSubgroup ≤ M.map (MulAut.conj g).toMonoidHom) :
    M.map (MulAut.conj g).toMonoidHom = M := by
  apply conjugate_eq_of_subgroup_fusion S.toSubgroup M ?_ hN g hg
  intro x hx
  obtain ⟨n, hn, he⟩ := S.exists_overgroup_conjugator M hSM x hx
  exact ⟨n, M.le_normalizer hn, he⟩

end Sylow
