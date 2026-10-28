module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.CentralModels
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.AmbientPlacement
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Sections

/-!
# Two-central exclusions on the original B.5 moved quotient

The normal closure has trivial ambient centralizer by the original rank-one
displacement generation. A symmetric normal-closure model of degree at least
five, other than six, therefore fills the ambient group since all of its
automorphisms are inner. The S8 actor is excluded directly. In the S5 row the
original involution still has displacement at most one on the literal moved
quotient, so its natural model identifies it as a transposition before any
central-kernel reconstruction. Its full Sylow centrality is impossible.

Source: Aschbacher–Smith G.6.4(4), p.346, with the original B.5.1 section.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.normalClosure_eq_top_of_symmetric_model
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : normalClosure ({a} : Set G) ≃* Equiv.Perm (Fin n)) :
    normalClosure ({a} : Set G) = ⊤ := by
  apply h.normalClosure_eq_top_of_inner_automorphisms ht
  intro f
  obtain ⟨p,hp⟩ := Equiv.Perm.conj_surjective_of_degree hn hn6 (MulAut.congr e f)
  refine ⟨e.symm p,?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj, e.apply_symm_apply]
  exact hp

/-- Exclude the S8 source actor before reconstructing its original module. -/
theorem Hypotheses.not_symmetricEight_normalClosure_of_twoCentral
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (e : normalClosure ({a} : Set G) ≃* Equiv.Perm (Fin 8))
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False := by
  have he := h.normalClosure_eq_top_of_symmetric_model ht (by decide) (by decide) e
  exact h.not_symmetricEight_of_twoCentral ht
    ((topEquiv.symm.trans (MulEquiv.subgroupCongr he.symm)).trans e) S hz

/-- The actual B.5 natural-five quotient row is impossible in the two-central
source case, with its original quotient maps and marked involution. -/
theorem Hypotheses.not_naturalFive_section_of_twoCentral
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    {L : Subgroup (normalClosure ({a} : Set G))}
    (s : MovedSection (ρ.comp (normalClosure ({a} : Set G)).subtype) L)
    (e : ActionEquiv s.action (BinaryPermutation.naturalRepresentation (Fin 5)))
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False := by
  let := h.finite_module
  let K := normalClosure ({a} : Set G)
  let t : K := ⟨a,subset_normalClosure (Set.mem_singleton a)⟩
  have hn : t ≠ 1 := fun he => h.nonidentity (congrArg Subtype.val he)
  have hc : Module.finrank (ZMod 2) (LinearMap.range (s.central.quotientRepresentation t - LinearMap.id)) ≤ 1 :=
    (subquotient_displacement_rank_le (ρ.comp K.subtype) s.space s.central t).trans ht.le
  have hs := BinaryPermutation.five_isSwap_of_natural_rank_one s.central.quotientRepresentation e.groupEquiv
    e.linearEquiv e.intertwines t hn hc
  have htop := h.normalClosure_eq_top_of_symmetric_model ht (by decide) (by decide) e.groupEquiv
  let eg : G ≃* Equiv.Perm (Fin 5) :=
    (topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e.groupEquiv
  exact Equiv.Perm.not_twoCentral_of_isSwap_model (Or.inl rfl) eg a hs S hz
end CFSG.Quasithin.ChapterG.Section06
