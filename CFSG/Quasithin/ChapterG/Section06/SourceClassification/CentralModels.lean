module

public import CFSG.Quasithin.ChapterG.Section06.Source
public import Theory.GroupTheory.NormalClosurePairCentralSylow
public import Theory.Representation.BinaryPermutation.CentralTransvections

/-!
# The complete two-central clause of the original G.6.4 dispatcher

A two-central marked element cannot belong to an exchanged factor pair.
For a single factor the linear models are already permitted. The natural
S5 case and both S8 cases are excluded by the original rank-one involution
and its full Sylow centralizer. This leaves precisely the stated S6 and S7
natural modules and the S6 permutation core.

The final theorem assembles all of G.6.4 from its actual clauses (1)–(3),
retaining the original SQTK cover, faithful action, involution and rank-one
hypotheses. The central clause is proved here and is no longer a separate
source input. Source: Aschbacher–Smith G.6.4, printed pp.345–346.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section06
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.not_naturalFive_of_twoCentral
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (hm : HasModelOn ρ ⊤ ⊤ (BinaryPermutation.naturalRepresentation (Fin 5)))
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False := by
  let := h.finite_module
  obtain ⟨e,E,stable,hE⟩ := hm
  let eg : G ≃* Equiv.Perm (Fin 5) := topEquiv.symm.trans e
  let ev : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) := Submodule.topEquiv.symm.trans E
  have he : ∀ g v, ev (ρ g v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (eg g) (ev v) := by
    intro g v
    exact hE ⟨g,mem_top g⟩ ⟨v,Submodule.mem_top⟩
  exact BinaryPermutation.not_twoCentral_natural_five ρ eg ev he a h.nonidentity ht.le S hz

/-- The actor alone excludes S8; no natural/core module reconstruction is used. -/
theorem Hypotheses.not_symmetricEight_of_twoCentral
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (e : G ≃* Equiv.Perm (Fin 8))
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False := by
  let := h.finite_module
  exact BinaryPermutation.not_twoCentral_faithful_eight ρ h.faithful e a
    h.nonidentity h.involution ht S hz

/-- Inspection of every original single-factor module gives precisely the
central list on the actual original group and space. -/
theorem Hypotheses.centralModel_of_factorModel
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (hm : FactorModel ρ ⊤ ⊤)
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : CentralModel ρ := by
  rcases hm with ⟨n,hlo,hhi,hm⟩ | ⟨n,hlo,hhi,hm⟩ | ⟨n,hn,hm⟩
  · exact Or.inl ⟨n,hlo,hhi,hm⟩
  · interval_cases n
    · exact (h.not_naturalFive_of_twoCentral ht hm S hz).elim
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (Or.inl hm))
    · obtain ⟨e,_,_,_⟩ := hm
      exact (h.not_symmetricEight_of_twoCentral ht (topEquiv.symm.trans e) S hz).elim
  · rcases hn with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr hm))
    · obtain ⟨e,_,_,_⟩ := hm
      exact (h.not_symmetricEight_of_twoCentral ht (topEquiv.symm.trans e) S hz).elim

/-- Two-centrality excludes the literal G.6 factor pair without needing the
ambient extension or the earlier B.5.6 encoding. -/
theorem TwoFactorModules.not_twoCentral
    (d : TwoFactorModules ρ a) (hne : a ≠ 1)
    [Finite G] (S : Sylow 2 G)
    (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False :=
  Theory.GroupTheory.not_twoCentral_of_normalClosure_pair d.first d.second a
    d.marked hne d.join_eq (disjoint_iff.mpr d.disjoint) d.second_nontrivial d.permutation S hz

/-- Full G.6.4, with its entire central clause discharged from the literal
one-factor or two-factor decomposition. Earlier source owners construct that decomposition. -/
theorem Hypotheses.conclusion_of_factor_decomposition
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (hm : OneFactor ρ a ∨ Nonempty (TwoFactors ρ a)) : Conclusion ρ a := by
  let := h.finite_group
  refine ⟨hm,?_⟩
  intro S hz
  rcases hm with ho | hd
  · refine ⟨ho.1,?_⟩
    have hf : FactorModel ρ ⊤ ⊤ := ho.2.2 ▸ ho.2.1
    exact h.centralModel_of_factorModel ht hf S hz
  · obtain ⟨d⟩ := hd
    exact (d.toTwoFactorModules.not_twoCentral h.nonidentity S hz).elim
end CFSG.Quasithin.ChapterG.Section06
