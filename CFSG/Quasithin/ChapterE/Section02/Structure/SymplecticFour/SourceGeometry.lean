module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.InnerCore
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.MovingPair
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# Original nonbinary Sp4 source geometry

Align the original Sylow inside the normal simple component. Minimal
parabolicity gives the diagram-moving actor and identifies the original
maximal-subgroup intersection with the Borel. Core-freeness then puts V inside
the component. Transport V through that same marking, preserving its normal
Sylow action and cardinality, and apply the central-root opposite-pair proof.

This is the complete placement and irreducibility part of E.2.7, printed
pp.219–220. Recognition of the generated group, its internal conjugator and
the final witness model are separate obligations; none is asserted here.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour DiagramAutomorphisms EvenBorelTorus TwoConjugate
open ChapterB
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original V has the required central-root and irreducible opposite-pair geometry. -/
theorem source_geometry {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:2<Nat.card V) :
    let f:=L.subtype.comp e.toMonoidHom
    let W:=V.comap f
    V≤L ∧ W.map f=V ∧
    W≤(center (unipotent (F:=F))).map (unipotent (F:=F)).subtype ∧
    Representation.IsIrreducible (pairAction W) ∧ pCore 2 (oppositePair W)=⊥ := by
  dsimp only
  let f:=L.subtype.comp e.toMonoidHom
  let W:=V.comap f
  have hf:Function.Injective f:=L.subtype_injective.comp e.injective
  have hVL:=source_inner_placement hF hn T hP hJ L e hmark hgen V hVT hVM
  have hfr:f.range=L := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hmap:W.map f=V := by rw [map_comap_eq,hfr,inf_eq_right.mpr hVL]
  let j:W→*V := (f.comp W.subtype).codRestrict V (fun x=>x.property)
  have hj:Function.Injective j := by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun z:V=>(z:G)) h))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective j hj
  have hcard:Nat.card W=Nat.card V := by
    rw [←hmap,card_map_of_injective hf]
  obtain ⟨t,ht⟩:=exists_moving_sylow_actor hF hn T hP L e hmark hgen
  let a:ActorReduction.stabilizer (F:=F):=
    ⟨extensionAction L e t,sylow_actor T L e hmark t⟩
  have hWU:W≤unipotent := by
    rw [←hmark]
    exact comap_mono hVT
  have hWa:W.map a.val.toMonoidHom=W := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change f (a.val x)∈V
      rw [show f (a.val x)=t.val*f x*t.val⁻¹ from extensionAction_apply L e t x]
      exact (mem_normalizer_iff.mp (hVN t.property) (f x)).mp hx
    · rw [card_map_of_injective a.val.injective]
  exact ⟨hVL,hmap,Witnesses.SymplecticFour.source_moving_pair hF hn a ht W hWU hWa
    (hcard.symm ▸ hr)⟩

/-- All model marks and opposite-pair geometry on the original source V.
No inner-placement, diagram, Borel or irreducibility premise is retained. -/
theorem source_geometry_aligned {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:L≃*Sp F)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2)
    (hVN:(T:Subgroup G)≤normalizer (V:Set G)) (hr:1<Group.rank V) :
    ∃g:Sp F, let e':=(e.trans (MulAut.conj g)).symm
      let f:=L.subtype.comp e'.toMonoidHom
      let W:=V.comap f
      (T:Subgroup G).comap f=unipotent ∧
      (minimalParabolicMax T hP).comap f=borel ∧
      V≤L ∧ W.map f=V ∧
      W≤(center (unipotent (F:=F))).map (unipotent (F:=F)).subtype ∧
      Representation.IsIrreducible (pairAction W) ∧ pCore 2 (oppositePair W)=⊥ := by
  obtain ⟨g,hg,_,hB⟩:=source_diagram_and_borel hF hn T hP L e hgen
  have hc:2<Nat.card V := by
    by_contra! h
    have hh:=IsElementaryAbelian.rank_le_of_card_le (p:=2) (n:=1) V (by simpa using h)
    omega
  exact ⟨g,hg,hB,source_geometry hF hn T hP hJ L _ hg hgen V hVT hVM hVN hc⟩

/-- Literal derived-Sp4 source specialization, with normality inside the
original Sylow. The binary derived-A6 case is deliberately excluded by n>1. -/
theorem source_derived_geometry {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:L≃*commutator (Sp F))
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    [(V.subgroupOf T).Normal]
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2) (hr:1<Group.rank V) :
    ∃e':Sp F≃*L, let f:=L.subtype.comp e'.toMonoidHom
      let W:=V.comap f
      (T:Subgroup G).comap f=unipotent ∧
      (minimalParabolicMax T hP).comap f=borel ∧
      V≤L ∧ W.map f=V ∧
      W≤(center (unipotent (F:=F))).map (unipotent (F:=F)).subtype ∧
      Representation.IsIrreducible (pairAction W) ∧ pCore 2 (oppositePair W)=⊥ := by
  have hq:2<Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  let e0:=e.trans (derivedEquivFull_of_card_gt_two hq)
  obtain ⟨g,hg⟩:=source_geometry_aligned hF hn T hP hJ L e0 hgen V hVT hVM
    ((normal_subgroupOf_iff_le_normalizer hVT).mp inferInstance) hr
  exact ⟨(e0.trans (MulAut.conj g)).symm,hg⟩

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
