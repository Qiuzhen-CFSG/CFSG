module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ConjugateFactors
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Literal orbit supports of the selected factor partition

The ambient permutation of the original starred blocks gives literal actor and
support joins for each factor orbit. Their moved support is exactly the
commutator support of the orbit actor, and the original fixed-complement clause
splits it from the orbit actor's fixed space. Independence of the factor spaces
identifies a full orbit with one transitive orbit on all of the module.

Source: Aschbacher--Smith 15.1.2, first paragraph, printed p.1085, using
D.2.16's decomposition and the completed ambient partition action.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
namespace FactorData
@[expose] def orbitActor (π : G →* Equiv.Perm d.Index) (i : d.Index) : Subgroup G :=
  ⨆ g : G, (c.ambientFactor d (π g i)).actor
@[expose] def orbitSpace (π : G →* Equiv.Perm d.Index) (i : d.Index) : Submodule (ZMod 2) V :=
  ⨆ g : G, (c.ambientFactor d (π g i)).space

theorem ambient_spaces_generate : (⨆ i, (c.ambientFactor d i).space) = U := by
  simp only [ambientFactor,Factor.map_space,embedding,←Submodule.map_iSup,
    d.space_generation,Submodule.map_top,Submodule.range_subtype]

theorem ambient_spaces_independent : iSupIndep (fun i => (c.ambientFactor d i).space) := by
  simpa only [ambientFactor,Factor.map_space,embedding] using
    LinearMap.iSupIndep_map U.subtype U.subtype_injective d.space_independent

theorem ambient_space_ne_bot (i : d.Index) : (c.ambientFactor d i).space ≠ ⊥ := by
  let F := c.ambientFactor d i
  intro hz
  have hzero (w : F.Space) : F.embedding.spaceMap w = 0 := by
    exact (Submodule.mem_bot (R := ZMod 2)).mp (hz ▸ (show F.embedding.spaceMap w ∈ F.space from ⟨w,rfl⟩))
  have hw (w : F.Space) : w = 0 := F.embedding.space_injective (by rw [hzero,map_zero])
  obtain ⟨g,hg⟩ := exists_ne (1 : F.Carrier)
  apply hg
  apply F.faithful
  ext w
  rw [hw (F.action g w),hw (F.action 1 w)]

theorem ambient_cross {i j : d.Index} (hij : i ≠ j) :
    (c.ambientFactor d i).space ≤ fixedSpace ρ (c.ambientFactor d j).actor := by
  simpa only [ambientFactor,Factor.map_space,Factor.map_actor] using
    (c.embedding ρ).map_fixed _ _ (d.cross i j hij)

theorem orbitActor_le (π : G →* Equiv.Perm d.Index) (i : d.Index) :
    c.orbitActor d π i ≤ K := by
  apply iSup_le
  intro g
  simp only [ambientFactor,Factor.map_actor,embedding]
  exact map_subtype_le _

theorem orbitSpace_le (π : G →* Equiv.Perm d.Index) (i : d.Index) :
    c.orbitSpace d π i ≤ U := by
  apply iSup_le
  intro g
  exact (le_iSup (fun j => (c.ambientFactor d j).space) (π g i)).trans
    (c.ambient_spaces_generate d).le

theorem orbitSpace_eq_support (π : G →* Equiv.Perm d.Index) (i : d.Index) :
    c.orbitSpace d π i = subspaceCommutator ρ ⊤ (c.orbitActor d π i) := by
  rw [orbitActor,subspaceCommutator_iSup_family]
  exact iSup_congr fun g => (c.ambientFactor d (π g i)).space_eq_support

theorem orbitSpace_ne_bot (π : G →* Equiv.Perm d.Index) (i : d.Index) :
    c.orbitSpace d π i ≠ ⊥ := by
  intro hz
  exact c.ambient_space_ne_bot d (π 1 i) (le_bot_iff.mp
    ((le_iSup (fun g : G => (c.ambientFactor d (π g i)).space) 1).trans_eq hz))

theorem orbitSpace_fixed_complement (π : G →* Equiv.Perm d.Index) (i : d.Index) :
    c.orbitSpace d π i ⊔ fixedSpace ρ (c.orbitActor d π i) = ⊤ := by
  classical
  apply top_unique
  rw [←c.fixed_complement]
  apply sup_le
  · apply (c.ambient_spaces_generate d).ge.trans
    apply iSup_le
    intro j
    by_cases hj : ∃ g : G, π g i = j
    · obtain ⟨g,rfl⟩ := hj
      exact (le_iSup (fun g : G => (c.ambientFactor d (π g i)).space) g).trans le_sup_left
    · apply le_trans _ le_sup_right
      rw [orbitActor,fixedSpace_iSup_family]
      apply le_iInf
      intro g
      exact c.ambient_cross d (fun he => hj ⟨g,he.symm⟩)
  · exact (fixedSpace_antitone ρ (c.orbitActor_le d π i)).trans le_sup_right

theorem orbitSpace_eq_top_iff (π : G →* Equiv.Perm d.Index) (i : d.Index) :
    c.orbitSpace d π i = ⊤ ↔ U = ⊤ ∧ ∀ j, ∃ g : G, π g i = j := by
  constructor
  · intro he
    refine ⟨top_unique (he ▸ c.orbitSpace_le d π i),?_⟩
    intro j
    have hs : (⨆ k ∈ {k | ∃ g : G, π g i = k}, (c.ambientFactor d k).space) = ⊤ := by
      apply top_unique
      rw [←he]
      apply iSup_le
      intro g
      exact le_iSup_of_le (π g i) (le_iSup_of_le ⟨g,rfl⟩ le_rfl)
    exact (c.ambient_spaces_independent d).mem_of_biSup_eq_top hs (c.ambient_space_ne_bot d j)
  · rintro ⟨hU,ht⟩
    apply top_unique
    apply hU.ge.trans
    apply (c.ambient_spaces_generate d).ge.trans
    apply iSup_le
    intro j
    obtain ⟨g,rfl⟩ := ht j
    exact le_iSup (fun g : G => (c.ambientFactor d (π g i)).space) g

theorem orbitActor_normal (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor) (i : d.Index) : (c.orbitActor d π i).Normal := by
  constructor
  intro x hx g
  have hm : (c.orbitActor d π i).map (MulAut.conj g).toMonoidHom ≤ c.orbitActor d π i := by
    rw [orbitActor,Subgroup.map_iSup]
    apply iSup_le
    intro h
    rw [hp]
    simpa only [map_mul,Equiv.Perm.mul_apply] using
      le_iSup (fun h : G => (c.ambientFactor d (π h i)).actor) (g*h)
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

theorem orbitSpace_invariant (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor) (i : d.Index) :
    (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (c.orbitSpace d π i) := by
  let := c.orbitActor_normal d π hp i
  rw [c.orbitSpace_eq_support d π i]
  exact subspaceCommutator_invariant_normalizer ρ
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_normalizer_of_normal

/-- A full orbit support means exactly one factor orbit and no outside fixed
summand. This is the source alternative a=1 and V=V₀. -/
theorem orbitSpace_eq_top_iff_transitive (π : G →* Equiv.Perm d.Index) (i : d.Index) :
    c.orbitSpace d π i = ⊤ ↔ U = ⊤ ∧ ∀ j k, ∃ g : G, π g j = k := by
  rw [c.orbitSpace_eq_top_iff d π i]
  constructor
  · rintro ⟨hU,ht⟩
    refine ⟨hU,fun j k => ?_⟩
    obtain ⟨g,hg⟩ := ht j
    obtain ⟨h,hh⟩ := ht k
    refine ⟨h*g⁻¹,?_⟩
    rw [map_mul,Equiv.Perm.mul_apply,←hg,map_inv]
    simpa using hh
  · rintro ⟨hU,ht⟩
    exact ⟨hU,ht i⟩

end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
