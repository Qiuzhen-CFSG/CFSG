module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.First
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.Consumers
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.JankoEscape

/-!
# The exterior weak-closure and fusion branch of 12.5.1

The original full automizer gives r > 3 and m = s = 3. The TI argument
then proves the zeroth weak-closure bounds. These bounds and the independent
point-core containment make the point span elementary and promote the
L-reselected nonsingular point centralizer to an ambient Sylow subgroup.
The two point orbits separate, giving literal L-controlled fusion. The first
weak-closure alternative bounds the C₁-centralizer and excludes generation
one; positive attained generation strengthens this to n(H) > 1. The local
component escape theorem then identifies K₁ with L₁, and the specialized
12.2.11 argument supplies generation two and the nontrivial odd Hall 3-group.

`ExteriorFusion` collects conclusions only. `exteriorFusion_of_local` proves
every field from the original chosen module and marking, without numerical,
weak-closure, fusion, actor-image, generation or Hall premises. Its three
local containments retain their producer qt-d-1251-local. Structural1222At
retains its producer qt-d-1222-source. The final exterior exclusion, including
construction of the terminal configuration and discharge of those earlier
inputs, belongs to qt-d-1251-source and its existing source branches.

Source: Aschbacher--Smith, 12.5.6--7 and 12.5.8(2)--12, printed pp.819--821.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The conclusions of the weak-closure and fusion branch, on the unchanged
ambient subgroups. The nonsingular Sylow point is an actual L-conjugate of
z′; no Sylow assertion is imposed on the canonical coordinate representative. -/
structure ExteriorFusion (s : SylowExteriorMarking D) : Prop where
  parameters : let := D.elementary
    (3 : ℕ∞) < globalR V ∧ localM V = 3 ∧ globalS V = 3
  zero_centralizes : indexedWeakClosure V (T : Subgroup G) 0 ≤
    (T : Subgroup G) ⊓ centralizer (V : Set G)
  positive_weakClosure : 0 < globalW V (T : Subgroup G)
  zero_normalizer : normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
    s.marking.M
  elementary_span : IsElementaryAbelian 2 s.marking.U
  nonsingular_sylow : ∃ l : L,
    (pointSylow s l).relIndex (T : Subgroup G) = 4 ∧
    ¬ 2 ∣ (pointSylow s l).relIndex
      (s.marking.M ⊓ centralizer ({MulAut.conj (l : G) s.marking.zPrime} : Set G)) ∧
    ∃ P : Sylow 2 (centralizer ({MulAut.conj (l : G) s.marking.zPrime} : Set G)),
      (P : Subgroup (centralizer ({MulAut.conj (l : G) s.marking.zPrime} : Set G))).map
        (centralizer ({MulAut.conj (l : G) s.marking.zPrime} : Set G)).subtype =
          pointSylow s l
  separated : ¬ IsConj s.marking.z s.marking.zPrime
  point_control : PointControl s.marking
  conjugate_commutation : ∀ g : G,
    s.marking.Vi 1 ≤ V.map (MulAut.conj g).toMonoidHom →
      (∃ c ∈ s.marking.Gi 1, V.map (MulAut.conj c).toMonoidHom =
        V.map (MulAut.conj g).toMonoidHom) ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥
  first_alternative :
    indexedWeakClosure V (T : Subgroup G) 1 ≤ centralizer (V : Set G) ∨
      s.actorImage (indexedWeakClosure V (T : Subgroup G) 1) =
        s.actorImage (s.marking.Ri 6)
  first_centralizes : indexedWeakClosure V (T : Subgroup G) 1 ≤
    centralizer (s.marking.Vi 6 : Set G)
  weakCentralizer_bound : centralizer (weakCentralizer V (T : Subgroup G) 1 : Set G) ≤
    s.marking.M
  generation_gt_one : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
    1 < generationParameter H
  point_component_eq : ∀ K ∈ Chapter1.cComponentsIn (s.marking.Gi 1),
    s.marking.Li 1 ≤ K → (K.subgroupOf (s.marking.Gi 1)).Normal →
      s.marking.Li 1 = K
  point_component_normal :
    s.marking.Li 1 ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧
      ((s.marking.Li 1).subgroupOf (s.marking.Gi 1)).Normal
  generation_two_hall_three : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
    H ≤ s.marking.Gi 1 → generationParameter H = 2 ∧
      ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ H ⊓ s.marking.M ∧
        IsHallSubgroup oddPrimes (C.subgroupOf (H ⊓ s.marking.M)) ∧ IsPGroup 3 C

/-- Assemble original 12.5.6--7 and 12.5.8(2)--12 from their proved source
branches. The remaining inputs are precisely the authorized earlier structural
result and the local G₃,G₆ and point-core containments. -/
theorem exteriorFusion_of_local (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hcore : V ≤ (s.marking.Gi 1).pCoreIn 2) : ExteriorFusion s := by
  let := D.elementary
  have hp := s.source_parameters h structural hG₃ hG₆
  obtain ⟨hW, hw, hN⟩ := zero_clauses_of_parameters s h structural hG₆ hp.1 hp.2.2
  let : IsElementaryAbelian 2 s.marking.U := elementary_point_span s hcore hW
  obtain ⟨geometry⟩ := pointSylowGeometry_nonempty s h structural
  have p := pointControl_of_weakClosure s geometry hcore hW hN
  have hW₁ := first_centralizes_V₆ s p hp.1 hp.2.2
  have hC := centralizer_weakCentralizer_one_le s.marking hG₆ hW₁
  have hgen : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
      generationParameter H ≠ 1 := fun _ hH =>
    generation_ne_one s.marking hp.2.2 hN hC hH
  refine
    { parameters := hp
      zero_centralizes := le_inf (indexedWeakClosure_le _ _ _) hW
      positive_weakClosure := hw
      zero_normalizer := hN
      elementary_span := inferInstance
      nonsingular_sylow := ⟨geometry.conjugator, geometry.index_four,
        geometry.local_sylow, point_centralizer_sylow s geometry hW hN⟩
      separated := point_orbit_separation s geometry hW hN
      point_control := p
      conjugate_commutation := fun g hg =>
        point_conjugate_and_commutator s geometry hcore hW hN g hg
      first_alternative := first_alternative s p hp.1 hp.2.2
      first_centralizes := hW₁
      weakCentralizer_bound := hC
      generation_gt_one := ?_
      point_component_eq := fun K hK hLK hnormal =>
        s.point_component_eq_of_generation_exclusion h hK hLK hnormal hgen
      point_component_normal := s.point_component_normal_of_generation_exclusion h hgen
      generation_two_hall_three := fun H hH hHG =>
        exterior_generation_two_and_hall_three D h s hH hHG (hgen H hH) structural }
  intro H hH
  have hpos := (exterior_generation_spec D h s hH).1
  have hne := hgen H hH
  omega

/-- Apply the assembled point fusion to the literal terminal commutator
argument. The source owner must still construct its terminal configuration. -/
theorem ExteriorFusion.exterior_contradiction {s : SylowExteriorMarking D}
    (f : ExteriorFusion s) (d : TerminalConfiguration s.marking) : False :=
  exterior_contradiction_of_point_and_terminal s.marking f.point_control d

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
