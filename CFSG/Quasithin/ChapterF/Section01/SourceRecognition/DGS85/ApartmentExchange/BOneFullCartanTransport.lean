module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneFullCartanPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PathRootTransport

/-!
# Conjugacy in the same chosen reflection apartment

The original Borel two-group is contained in each actual lifted Chapter 10
actor. Apply oriented path transport to the profile's supplied path and the
constructed reflection path, retaining the chosen source length (three or
four), original covering and actor. This puts the selected reflection's
conjugacy formula in the actual apartment root without changing the reflection.
The actor's central correction remains explicit; when the original actor
center is trivial it disappears, giving exact root conjugacy.

Length, preceding-vertex and Cartan-fixation compatibility of the supplied
path remain explicit inputs. Neither those markings nor removal of the
central defect in the nontrivial-center branch is asserted. Exchange,
quotient root signs and the other Chapter 14 branches remain obligations.
Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157,
and (14.1)--(14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open Theory.GroupTheory.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))

/-- The original Borel two-group lies in each lifted source actor. -/
theorem twoGroup_le_bOneActor
    {F W : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup W] [Module (ZMod 2) W] (i : Bool)
    (d : BOneActionData (reducedFamily L S) (base (reducedFamily L S) i)
      (base (reducedFamily L S) (!i)) F W)
    (hactor : d.actor=((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)) :
    twoGroup L S≤universalBOneActor h i d := by
  have hU : reducedSylow L S≤(B₀ L S).pCoreIn 2 := by
    rw [B₀_eq_source h]
    exact le_pCoreIn_of_normalizes (reduced_hypothesis h).S_isP
      le_sup_right ((normal_subgroupOf_iff_le_normalizer le_sup_right).mp (reduced_sylow_normal h))
  intro u hu
  refine ⟨?_,?_⟩
  · obtain ⟨x,hx,rfl⟩ := hu
    rw [hactor]
    change (bOne_tree_map h (middleMap L S x):G)∈(B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)
    change (bOne_tree_map h (Universal.left (reducedAmalgam L S) ((reducedAmalgam L S).left x)):G)∈(B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)
    rw [bOne_tree_map_middle]
    exact (show (B₀ L S).pCoreIn 2≤(B₀ L S).pCoreIn 2⊔starredParabolic L S (if i then 1 else 0) from le_sup_left) (hU hx)
  · have hm := twoGroup_le (L := L) (S := S) hu
    rw [originalMiddle,←Universal.overlap_eq _
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))] at hm
    cases i
    · exact hm.1
    · exact hm.2

/-- Triviality of the original actor center survives the marked covering. -/
theorem universalBOne_center_eq_bot
    {F W : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup W] [Module (ZMod 2) W] (i : Bool)
    (d : BOneActionData (reducedFamily L S) (base (reducedFamily L S) i)
      (base (reducedFamily L S) (!i)) F W)
    (hcenter : centerIn d.actor=⊥) :
    centerIn (universalBOneActor h i d)=⊥ := by
  apply le_bot_iff.mp
  intro z hz
  let H := universalBOneActor h i d
  let e := universalBOneActorEquiv h i d
  let zH : H := ⟨z,hz.1⟩
  have hc : zH∈center H := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hz.2 y y.property)
  have hc' : e zH∈center d.actor := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hc x)
  have hz' : (e zH:G₀ L S)∈centerIn d.actor := by
    rw [centerIn_eq_map_center]
    exact mem_map_of_mem d.actor.subtype hc'
  have he : e zH=1 := Subtype.ext (show (e zH:G₀ L S)=1 by simpa only [hcenter,mem_bot] using hz')
  exact congrArg H.subtype (e.injective (he.trans e.map_one.symm))

universe uF
variable {h c}
variable (d : ∀ i : Bool, FullCartanReflectionProfile.{uF} h c i)

/-- The supplied source root and the constructed apartment root are conjugate
inside the same actual actor when their length and Cartan marking agree. -/
theorem fullCartanRoots_transport (i : Bool)
    (hlen : (d i).path.length=fullCartanPathLength d)
    (hprev : (d i).path.penultimate=base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (hfixed : cartan c≤pathFixer (X := (reducedAmalgam L S).Universal) (d i).path) :
    ∃ u∈universalBOneActor h i (d i).data,
      (pathRoot (X := (reducedAmalgam L S).Universal) (d i).path).map
        (MulAut.conj u).toMonoidHom=(fullCartanPathRoots d i).root := by
  let q := reflectionPath c (fullCartanReflections d) (fullCartanReflections_fix d)
    (fullCartanReflections_move d) (fullCartanReflections_normalize d) (fullCartanPathLength d)
    (Nat.zero_lt_of_lt (fullCartanPathLength_gt d)) i
  obtain ⟨u,hu,he⟩ := exists_twoGroup_pathRoot_transport h c (fullCartanPathLength d)
    (fullCartanProfiles_path_transitive d) (fullCartanProfiles_tree_thick d)
    (d i).path q.walk (d i).path_isPath q.isPath hlen q.length_eq hprev q.previous hfixed
  refine ⟨u,twoGroup_le_bOneActor h i (d i).data (d i).actor_eq hu,?_⟩
  rw [fullCartanRoots_root]
  exact he

/-- The same chosen reflection has its conjugacy formula in the actual
chosen apartment root. The central factor is retained verbatim. -/
theorem fullCartanRoots_actual_conjugacy (i : Bool)
    (hlen : (d i).path.length=fullCartanPathLength d)
    (hprev : (d i).path.penultimate=base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (hfixed : cartan c≤pathFixer (X := (reducedAmalgam L S).Universal) (d i).path) :
    ∃ y∈(fullCartanPathRoots d i).root, orderOf y=2 ∧
      ∃ z∈centerIn (universalBOneActor h i (d i).data),
        bOne_tree_map h z∈Q (reducedFamily L S) (base (reducedFamily L S) i) ∧
        ∃ g∈universalBOneActor h i (d i).data,
          g*(z*y)*g⁻¹=(fullCartanPathRoots d i).reflection := by
  obtain ⟨u,hu,hU⟩ := fullCartanRoots_transport d i hlen hprev hfixed
  obtain ⟨y,hy,ho,z,hz,hzQ,g,hg,he⟩ := (fullCartanReflections_source_clauses d i).2.1
  have hy' : u*y*u⁻¹∈(fullCartanPathRoots d i).root := by
    rw [←hU]
    exact mem_map_of_mem (MulAut.conj u).toMonoidHom hy
  refine ⟨u*y*u⁻¹,hy',?_,z,hz,hzQ,g*u⁻¹,
    (universalBOneActor h i (d i).data).mul_mem hg
      ((universalBOneActor h i (d i).data).inv_mem hu),?_⟩
  · exact ((MulAut.conj u).orderOf_eq y).trans ho
  · rw [fullCartanRoots_reflection,←he]
    have hzcomm : u*z=z*u := hz.2 u hu
    calc
      (g*u⁻¹)*(z*(u*y*u⁻¹))*(g*u⁻¹)⁻¹ = g*(u⁻¹*z*u)*y*g⁻¹ := by group
      _ = g*(z*y)*g⁻¹ := by rw [mul_assoc u⁻¹,←hzcomm,inv_mul_cancel_left]; group

/-- In the centerless branch the preceding transport removes the central
factor and gives the source root-conjugacy clause for these exact roots. -/
theorem fullCartanRoots_actual_conjugacy_of_center_eq_bot (i : Bool)
    (hlen : (d i).path.length=fullCartanPathLength d)
    (hprev : (d i).path.penultimate=base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (hfixed : cartan c≤pathFixer (X := (reducedAmalgam L S).Universal) (d i).path)
    (hcenter : centerIn (d i).data.actor=⊥) :
    ∃ y∈(fullCartanPathRoots d i).root, orderOf y=2 ∧
      ∃ g∈universalBOneActor h i (d i).data,
        g*y*g⁻¹=(fullCartanPathRoots d i).reflection := by
  obtain ⟨y,hy,ho,z,hz,_,g,hg,he⟩ := fullCartanRoots_actual_conjugacy d i hlen hprev hfixed
  have hz1 : z=1 := by simpa only [universalBOne_center_eq_bot h i (d i).data hcenter,mem_bot] using hz
  exact ⟨y,hy,ho,g,hg,by simpa only [hz1,one_mul] using he⟩

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
