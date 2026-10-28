module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorPerfect
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorCentralCore

/-!
# Faithful elementary apartment actors and exact cubic root pairs

Perfectness and the proved trivial derived-core intersection eliminate the
whole two-root actor core, including the beta orbit and field order four,
under the Cartan-kernel clause of DGS (14.5)(c). Consequently the original
midpoint quotient map restricts to an actual SL2 isomorphism. The existing
reciprocal root coordinates now lift to involutions with product of exact
order three: their cube lies in the now trivial core, and opposite upper
and lower images prevent their product from being the identity.

The final source application constructs the full-Cartan reflections and
apartment without catalogue, reflection or root-coordinate premises.
The nontrivial Cartan-kernel clause remains explicit. Control of the
adjoined reflection, exchange, root signs, binary choices, nonelementary
catalogue exclusions and full original (11.7)--(11.8) marked recognition
remain source obligations; the full original Borel and endpoint maps are
retained throughout.
Source: DGS, Groups and Graphs (1985), (14.9), p.215, and
(14.12), p.217; source profile (11.7), pp.174--175.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

include h hc hb hcomm helem


variable (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i*t i=1)
    (htnorm : ∀ i, t i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

include c t htfix htmove htsq htnorm

variable {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=8)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t))
include hp hl hT

/-- Under the Cartan-kernel clause of DGS (14.5)(c), the entire two-root
core vanishes on both vertex orbits. -/
theorem original_elementary_nonbinary_actor_core_eq_bot
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hne : (cartan c).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥) :
    pCore 2 (halfPathActor (X := (A).Universal) p 4)=⊥ := by
  let _ := original_elementary_nonbinary_actor_perfect h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT hnb
  simpa only [Group.IsPerfect.commutator_eq_top,inf_top_eq] using
    original_elementary_nonbinary_actor_derived_core h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT hnb hne

omit p hp hl hT in
/-- The original midpoint map is an isomorphism on the actual two-root
actor. Reciprocal root lifts have exact cubic order, not merely cube in O₂. -/
theorem original_elementary_nonbinary_faithful_actors
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ m, 0 < m ∧ ∃ (K : Bool → Type) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Finite (K i)) (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i) = 2^(if i then m else 2*m)) ∧
    ∃ e : ∀ v : Vertex F,
      (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type),
    ∀ {a b} (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=8),
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c t)) →
      (cartan c).map (bOne_tree_map h) ⊓
        U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥ →
      let D := halfPathActor (X := (A).Universal) p 4
      let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
      let V := (pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D
      let k := K ((bOne_tree_cover h).vertex (p.getVert 4)).type
      pCore 2 D=⊥ ∧
      ∃ E : D ≃* SL(2,k),
        (∀ x, E x=e _ (QuotientGroup.mk' _ (halfPathLocalMap h p 4 hl x))) ∧
        ∀ x∈R, x≠1 → ∃ y∈V, x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 := by
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hroots⟩ :=
    original_elementary_apartment_root_coordinates h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  refine ⟨m,hm,K,fK,finK,chK,hK,e,?_⟩
  intro a b p hp hl hT hne D R V k
  obtain ⟨hf,hker,hr,hv,z,hR,hV,hxy⟩ := hroots p hp hl hT
  have hzero : pCore 2 D=⊥ := original_elementary_nonbinary_actor_core_eq_bot
    h hc hb hcomm helem c t htfix htmove htsq htnorm p hp hl hT hnb hne
  let f := halfPathLinearMap h p 4 hl (e ((bOne_tree_cover h).vertex (p.getVert 4)))
  have hi : Function.Injective f := (f.ker_eq_bot_iff).mp (hker.trans hzero)
  let E : D ≃* SL(2,k) := MulEquiv.ofBijective f ⟨hi,hf⟩
  refine ⟨hzero,E,fun _ => rfl,?_⟩
  intro x hx hxne
  obtain ⟨y,hy,hxx,hyy,hcube⟩ := hxy x hx hxne
  have hcube' : (x*y)^3=1 := mem_bot.mp (hzero ▸ hcube)
  let g := (MulAut.conj z).toMonoidHom.comp f
  have hgi : Function.Injective g := (MulAut.conj z).injective.comp hi
  have hprod : x*y≠1 := by
    intro he
    have hyx : y=x := mul_left_cancel (he.trans hxx.symm)
    have hxV : x∈V := hyx ▸ hy
    obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent k (g x)).mp
      (hR ▸ mem_map_of_mem g hx)
    obtain ⟨b,hb⟩ := (hV (g x)).mp (mem_map_of_mem g hxV)
    have ha0 : a=0 := by
      have hh := congrArg (fun w : SL(2,k) => w.val 0 1) (ha.trans hb.symm)
      simpa [Matrix.SpecialLinearGroup.transvection_coe] using hh
    apply hxne
    apply hgi
    rw [map_one,←ha,ha0,Matrix.SpecialLinearGroup.transvection_coeff_zero]
  exact ⟨y,hy,hxx,hyy,orderOf_eq_prime hcube' hprod⟩

omit c t htfix htmove htsq htnorm p hp hl hT in
/-- The nonbinary elementary source supplies the full-Cartan apartment and
faithful rank-one actors with exact cubic root pairs. The Cartan-kernel
clause remains explicit at each path, as in DGS (14.5)(c). -/
theorem original_elementary_nonbinary_faithful_apartment
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i=base T i) ∧
      (∀ i, t i • base T (!i)≠base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan (chosenCartans h) : Set (A).Universal)) ∧
    ∃ m, 0 < m ∧ ∃ (K : Bool → Type) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Finite (K i)) (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i) = 2^(if i then m else 2*m)) ∧
    ∃ e : ∀ v : Vertex F,
      (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type),
    ∀ {a b} (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=8),
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup (chosenCartans h) t)) →
      (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
        U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥ →
      let D := halfPathActor (X := (A).Universal) p 4
      let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
      let V := (pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D
      let k := K ((bOne_tree_cover h).vertex (p.getVert 4)).type
      pCore 2 D=⊥ ∧
      ∃ E : D ≃* SL(2,k),
        (∀ x, E x=e _ (QuotientGroup.mk' _ (halfPathLocalMap h p 4 hl x))) ∧
        ∀ x∈R, x≠1 → ∃ y∈V, x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb (chosenCartans h)
  exact ⟨t,htfix,htmove,htsq,htnorm,
    original_elementary_nonbinary_faithful_actors h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm hnb⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
