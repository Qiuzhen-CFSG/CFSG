module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.Borel
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.Graph
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CenterAction
public import Theory.GroupTheory.PCoreRestriction
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient

/-!
# Inner placement in the original Sp4 source

An element of the maximal subgroup's two-core acts trivially on its marked
Borel torus: every displacement belongs to the intrinsic Borel two-core.
The actual torus action then forces the automorphism to be inner. Original
core-freeness kills the component centralizer, so equality of automorphisms
lifts to equality of group elements. This proves V ≤ L without an inner
placement premise, in E.2.7, printed pp.219–220.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour DiagramAutomorphisms EvenBorelTorus ActorReduction
open ChapterB
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite G] in
/-- Trivial action on the Borel torus forces each two-core element to be inner. -/
theorem core_element_inner {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (M L:Subgroup G) [L.Normal] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hB:M.comap (L.subtype.comp e.toMonoidHom)=borel)
    (hC:centralizer (L:Set G)=⊥)
    (v:G) (hvT:v∈T) (hv:v∈M.pCoreIn 2) : v∈L := by
  let f:Sp F→*G:=L.subtype.comp e.toMonoidHom
  let bmap:borel (F:=F)→*M := (f.comp borel.subtype).codRestrict M
    (fun b=>hB.ge b.property)
  have hbmap:Function.Injective bmap := by
    intro x y hh
    apply Subtype.ext
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun z:M=>(z:G)) hh
  let a:ActorReduction.stabilizer (F:=F) :=
    ⟨extensionAction L e v,sylow_actor T L e hmark ⟨v,hvT⟩⟩
  have hvM:v∈M := pCoreIn_le 2 M hv
  let vM:M:=⟨v,hvM⟩
  have hvMcore:vM∈pCore 2 M := (mem_map_iff_mem M.subtype_injective).mp hv
  have hd:(pCore 2 M).comap bmap≤pCore 2 (borel (F:=F)) :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective bmap hbmap⟩
  have hdisp (b:borel (F:=F)) : borelAction a b / b ∈ pCore 2 (borel (F:=F)) := by
    apply hd
    change bmap (borelAction a b/b)∈pCore 2 M
    have he:bmap (borelAction a b/b)=⁅vM,bmap b⁆ := by
      apply Subtype.ext
      change f (a.val b.val / b.val)=v*f b.val*v⁻¹*(f b.val)⁻¹
      rw [map_div]
      have hact:f (a.val b.val)=v*f b.val*v⁻¹ := extensionAction_apply L e v b.val
      rw [hact,div_eq_mul_inv]
    rw [he]
    have hnormal: bmap b * vM⁻¹ * (bmap b)⁻¹ ∈ pCore 2 M :=
      (inferInstance : (pCore 2 M).Normal).conj_mem _ ((pCore 2 M).inv_mem hvMcore) _
    simpa only [commutatorElement_def,mul_assoc] using (pCore 2 M).mul_mem hvMcore hnormal
  have htorus:torusAction hF a=1 := by
    apply MulEquiv.ext
    intro x
    obtain ⟨b,rfl⟩:=characters_surjective x
    rw [torusAction_characters]
    change borelCharacters (borelAction a b)=borelCharacters b
    have hh:=hdisp b
    rw [twoCore_eq_unipotent hF,←characters_ker] at hh
    change borelCharacters (borelAction a b/b)=1 at hh
    rw [map_div,div_eq_one] at hh
    exact hh
  obtain ⟨x,hx⟩ := (torusAction_eq_one_iff_inner hF hn
    SemilinearClassification.inner_field_of_preservesDiagram a).mp htorus
  have he:extensionAction L e (e x).val=MulAut.conj x := by
    apply MulEquiv.ext
    intro y
    apply e.injective
    apply Subtype.ext
    rw [extensionAction_apply]
    simp
  have hvx:v=(e x).val := extensionAction_injective L e hC (hx.symm.trans he.symm)
  exact hvx ▸ (e x).property

omit [Finite G] in
/-- Core-freeness makes the original normal simple supplement self-centralizing. -/
theorem source_centralizer {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hgen:L⊔(T:Subgroup G)=⊤) : centralizer (L:Set G)=⊥ := by
  have hq:2<Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  let : Group.IsPerfect (Sp F) := perfect_of_card_gt_two hq
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f:=e.toMonoidHom) e.surjective
  apply Theory.GroupTheory.centralizer_eq_bot_of_simple_two_quotient L
    (Group.IsPerfect.not_isMulCommutative L)
    (isPGroup_quotient_of_sup_eq_top L T T.isPGroup' hgen)
  exact le_bot_iff.mp ((minimalParabolicTwoCore_le_core T hP).trans hJ.le)

/-- The original elementary group lies in the inner component. In fact only
its Sylow and maximal-subgroup two-core containment are needed here. -/
theorem source_inner_placement {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) (hVT:V≤T) (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2) : V≤L := by
  intro v hv
  exact core_element_inner hF hn T _ L e hmark
    (source_borel_intersection hF hn T hP L e hmark hgen)
    (source_centralizer hF hn T hP hJ L e hgen) v (hVT hv) (hVM hv)

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
