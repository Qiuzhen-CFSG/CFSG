module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneNatural

/-!
# Chapter 10 natural kernels and actor reflections

The actual b=1 coordinate producer gives a surjective map on the vertex
core with kernel the full local-actor center. When that center is trivial,
it gives natural coordinates on the kernel of the unchanged actor quotient.
The nonbinary diagonal calculation then constructs a reflection in that
actor, conjugate there to the prescribed upper-root involution. It normalizes
the whole abelian Cartan and centralizes its part in the full local kernel.

The original coordinate markings, full diagonal image and nonzero nonidentity
diagonal parameter remain explicit. No SL₂ identification of the full vertex
stabilizer quotient is assumed. The paired source producer proves Q=Z;
the nontrivial-center and binary branches remain separate source obligations.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157, and
(14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
open Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace BOneActor
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F W : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {v w : Vertex (family P)} (h : LocallyRankOneTriple P B)
  (c : BOneActionData (family P) v w F W)
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The genuine Chapter 10 coordinates give the natural kernel on the
original actor, when its full center is trivial. The quotient map is unchanged. -/
def naturalKernel (hcore : Q (family P) v=Z (family P) v)
    (hz : centerIn c.actor=⊥) (E : W ≃ₗ[ZMod 2] (Fin 2 → F)) :
    NaturalKernel c.quotient := Classical.choice (by
  obtain ⟨φ,honto,hker,hact⟩ := natural_core_coordinates c h hcore E
  have hinj : Function.Injective φ := by
    apply (MonoidHom.ker_eq_bot_iff φ).mp
    rw [hker,hz]
    exact bot_subgroupOf _
  exact ⟨naturalKernelOfCoordinates c.actor (Q (family P) v) c.core_le
    c.quotient c.kernel φ ⟨hinj,honto⟩ hact⟩)

include h in
/-- The local actor, rather than the full endpoint, supplies the natural
reflection. It normalizes the entire chosen Cartan and has the prescribed
actor conjugacy, and it centralizes the Cartan part of the full local kernel. -/
theorem exists_reflection
    (hcore : Q (family P) v=Z (family P) v) (hz : centerIn c.actor=⊥)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (K : Subgroup G) [Finite K] [IsMulCommutative K]
    (hn : K ≤ normalizer (c.actor : Set G)) (hodd : Nat.Coprime 2 (Nat.card K))
    (hdiag : ∀ k : c.actor, (k:G)∈K → ∃ a : F, ∃ ha : a≠0,
      c.quotient k=Matrix.SpecialLinearGroup.diag2 a ha)
    (hfull : ∀ a : F, ∀ ha : a≠0,
      Matrix.SpecialLinearGroup.diag2 a ha∈(K.subgroupOf c.actor).map c.quotient)
    (htri : ∀ k : c.actor, (k:G)∈stabilizer (family P) w → (c.quotient k).val 1 0=0)
    (b : F) (hb : b≠0) (hb1 : b≠1)
    (x : c.actor) (hx : x*x=1) (a : F) (ha : a≠0) (hπx : c.quotient x=upper a) :
    ∃ t : c.actor,
      (t:G) • v=v ∧ (t:G) • w≠w ∧
      (t:G)∈normalizer (K : Set G) ∧ t*t=1 ∧ orderOf t=2 ∧
      c.quotient t=upper a*lower a⁻¹*upper a ∧
      (∃ g : c.actor, g*x*g⁻¹=t) ∧
      ∀ z∈K, z∈ballKernel (family P) v 1 → Commute (t:G) z := by
  let := finite_endpoints h
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  let d := naturalKernel h c hcore hz E
  obtain ⟨t,ht,htsq,ho,hπt,g,hg⟩ := d.exists_actor_cartan_reflection c.actor K
    c.quotient c.onto hn hodd hdiag hfull b hb hb1 x hx a ha hπx
  refine ⟨t,c.actor_le t.property,?_,ht,htsq,ho,hπt,⟨g,hg⟩,?_⟩
  · intro hfix
    have he := htri t hfix
    rw [hπt,braid_matrix a ha] at he
    exact inv_ne_zero ha he
  · intro z hzK hzM
    apply d.commutes_cartan_localKernel c.actor K (ballKernel (family P) v 1)
      c.quotient c.onto hn
      (c.actor_le.trans (stabilizer_le_normalizer_ballKernel (family P) v 1))
      hodd _ t ht z hzK hzM
    intro y hy
    exact htri y (ballKernel_one_le_edge (family P) c.adjacent hy).2

end BOneActor
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
