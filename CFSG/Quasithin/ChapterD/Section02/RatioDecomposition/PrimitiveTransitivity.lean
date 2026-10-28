module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.OrbitSupports
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# Primitive odd residuals permute the ratio factors transitively

A nonzero orbit product is normal. Its intersection with a self-centralizing
minimal normal subgroup P cannot vanish: otherwise the two normal subgroups
commute, forcing the orbit product into P. Thus every orbit product contains P.
A factor outside that orbit centralizes P and hence lies in the orbit product,
contrary to independence of the factors. This proves transitivity without
excluding the possible single elementary-nine factor.

Source: Aschbacher--Smith 14.6.12(2), printed p.1031, with the literal
D.2.16 factor action and the primitive residual supplied in 14.6.11.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition.FactorData
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)

private theorem primitive_actor_ne_bot (i : d.Index) :
    (c.ambientFactor d i).actor ≠ ⊥ := by
  intro hz
  obtain ⟨x,hx⟩ := exists_ne (1 : (d.factor i).Carrier)
  have hm := mem_bot.mp (hz ▸ (show
    (c.ambientFactor d i).embedding.groupMap x ∈ (c.ambientFactor d i).actor from ⟨x,rfl⟩))
  exact hx ((c.ambientFactor d i).embedding.group_injective
    (hm.trans (map_one _).symm))

/-- Each actual direct factor meets a self-centralizing normal subgroup
contained in the decomposed group. -/
theorem actor_inf_ne_bot_of_selfCentralizing
    (P : Subgroup G) [P.Normal] (hPK : P ≤ K)
    (hself : centralizer (P : Set G) ≤ P) (i : d.Index) :
    (c.ambientFactor d i).actor ⊓ P ≠ ⊥ := by
  let A := (d.factor i).actor
  let : A.Normal := d.actor_normal c.representation c.faithful i
  intro hz
  have hd : Disjoint A (P.subgroupOf K) := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hb : (x : G) ∈ (c.ambientFactor d i).actor ⊓ P := by
      refine ⟨?_,hx.2⟩
      simp only [ambientFactor,Factor.map_actor,embedding]
      change (x : G) ∈ (d.factor i).actor.map K.subtype
      exact mem_map_of_mem K.subtype hx.1
    exact Subtype.ext (mem_bot.mp (hz ▸ hb))
  have hc := commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
  have hAC : (c.ambientFactor d i).actor ≤ centralizer (P : Set G) := by
    simp only [ambientFactor,Factor.map_actor,embedding]
    rintro _ ⟨x,hx,rfl⟩ p hp
    exact congrArg Subtype.val (hc hx ⟨p,hPK hp⟩ hp)
  exact primitive_actor_ne_bot c d i ((inf_eq_left.mpr (hAC.trans hself)).symm.trans hz)

/-- Minimal normality and self-centralization of the actual residual force
one orbit on the literal factor family. -/
theorem transitive_of_minimal_normal_selfCentralizing
    (P : Subgroup G) [P.Normal]
    (hmin : ∀ B : Subgroup G, B.Normal → B ≤ P → B = ⊥ ∨ B = P)
    (hself : centralizer (P : Set G) ≤ P)
    (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor) :
    ∀ i j, ∃ g : G, π g i = j := by
  intro i j
  let A := c.orbitActor d π i
  let : A.Normal := c.orbitActor_normal d π hp i
  have hAne : A ≠ ⊥ := by
    intro hz
    apply primitive_actor_ne_bot c d (π 1 i)
    exact le_bot_iff.mp ((le_iSup (fun g : G => (c.ambientFactor d (π g i)).actor) 1).trans_eq hz)
  have hPA : P ≤ A := by
    rcases hmin (A ⊓ P) inferInstance inf_le_right with hz | he
    · have hc : A ≤ centralizer (P : Set G) :=
        commutator_eq_bot_iff_le_centralizer.mp
          (commutator_eq_bot_of_disjoint (disjoint_iff.mpr hz))
      exact (hAne ((inf_eq_left.mpr (hc.trans hself)).symm.trans hz)).elim
    · exact he ▸ inf_le_left
  by_contra hj
  have hAF : A ≤ centralizer ((c.ambientFactor d j).actor : Set G) := by
    apply iSup_le
    intro g x hx y hy
    simp only [ambientFactor,Factor.map_actor,embedding] at hx hy
    obtain ⟨x,hx,rfl⟩ := hx
    obtain ⟨y,hy,rfl⟩ := hy
    exact congrArg K.subtype (d.actors_commute c.faithful (fun he => hj ⟨g,he⟩) hx hy).symm.eq
  have hFA : (c.ambientFactor d j).actor ≤ A :=
    ((le_centralizer_iff.mpr (hPA.trans hAF)).trans hself).trans hPA
  have hi : Disjoint (c.ambientFactor d j).actor
      (⨆ k, ⨆ (_ : k ≠ j), (c.ambientFactor d k).actor) := by
    simpa only [ambientFactor,Factor.map_actor,embedding,Subgroup.map_iSup] using
      Subgroup.disjoint_map K.subtype_injective (d.actors_independent j)
  have hA : A ≤ ⨆ k, ⨆ (_ : k ≠ j), (c.ambientFactor d k).actor := by
    apply iSup_le
    intro g
    exact le_iSup_of_le (π g i) (le_iSup_of_le (fun he => hj ⟨g,he⟩) le_rfl)
  exact primitive_actor_ne_bot c d j (disjoint_self.mp (hi.mono_right (hFA.trans hA)))

end CFSG.Quasithin.ChapterD.RatioDecomposition.FactorData
