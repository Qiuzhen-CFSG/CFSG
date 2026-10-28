module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCore
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.ReducedNormal.IrreducibleClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# Reducedness of the ordinary root span

The short-root torus acts transitively on nonidentity elements of the seed.
Condition (E) makes the root normalizer a group of characteristic two, so the
irreducible Sylow-central seed argument gives reducedness of its normal span.
Consequently the span lies in the two-core and is centralized by that core.
All groups are restricted to the literal root normalizer before applying the
reduced-subgroup result.

Source: Aschbacher--Smith 4.3.6 (*), printed pp.614--615, and B.2.14.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Theory.SpecificGroups.SymplecticFour
namespace OrdinarySymplecticMarking
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

theorem fullModule_le_sylow (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    c.ordinaryModule ≤ (T : Subgroup G) := by
  intro w hw
  obtain ⟨a, ha, he⟩ := (m.planeRadical_image hn).ge hw
  have hau : a ∈ unipotent := ⟨OrdinaryRootCoreMatrix.plane_radical_le_point ha,
    map_subtype_le _ ha⟩
  exact ((m.unipotent_image).le ⟨a, hau, he⟩).1

theorem shortRoot_ne_bot (m : OrdinarySymplecticMarking c n) (hn : 1 < n) :
    c.ordinaryModule ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro he
  have hx : m.modelEmbedding (Representation.OneCohomology.SymplecticFour.rootElement 4 1) ∈
      c.ordinaryModule ⊓ centralizer (L : Set G) :=
    (m.shortRoot_image hn).le (mem_map_of_mem m.modelEmbedding
      ((RootSubgroup.mem_group_iff 4 _).mpr ⟨1, rfl⟩))
  rw [he, mem_bot] at hx
  have hh : Representation.OneCohomology.SymplecticFour.rootElement (K := m.Field) 4 1 =
      Representation.OneCohomology.SymplecticFour.rootElement 4 0 :=
    m.modelEmbedding_injective (by rw [RootSubgroup.element_zero, map_one]; exact hx)
  exact one_ne_zero (RootSubgroup.element_injective 4 hh)

/-- The diagonal torus inside the actual root normalizer acts transitively on
the nonidentity elements of the original short root. -/
theorem shortRoot_invariant_dichotomy (m : OrdinarySymplecticMarking c n) (hn : 1 < n)
    (E : Subgroup G) (hE : E ≤ c.ordinaryModule ⊓ centralizer (L : Set G))
    (hN : m.rootNormalizer ⊓ normalizer
        ((c.ordinaryModule ⊓ centralizer (L : Set G) : Subgroup G) : Set G) ≤ normalizer (E : Set G)) :
    E = ⊥ ∨ E = c.ordinaryModule ⊓ centralizer (L : Set G) := by
  by_cases hbot : E = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨a, ha, ha1⟩ := E.bot_or_exists_ne_one.resolve_left hbot
  obtain ⟨x, hx, he⟩ := (m.shortRoot_image hn).ge (hE ha)
  have hx1 : x ≠ 1 := by intro hx1; apply ha1; rw [←he, hx1, map_one]
  apply le_antisymm hE
  intro b hb
  by_cases hb1 : b = 1
  · rw [hb1]; exact E.one_mem
  obtain ⟨y, hy, hey⟩ := (m.shortRoot_image hn).ge hb
  have hy1 : y ≠ 1 := by intro hy1; apply hb1; rw [←hey, hy1, map_one]
  obtain ⟨t, ht, _⟩ := RootTori.regular 4 x y hx hy hx1 hy1
  have htP : (t : Sp m.Field) ∈ pointParabolic := by
    obtain ⟨s, hs⟩ := t.property
    rw [← hs]
    exact (diagonalTorus_mem_borel _ _).1
  have htN : m.modelEmbedding t ∈ m.rootNormalizer :=
    ((m.pointParabolic_image).le (mem_map_of_mem m.modelEmbedding htP)).2
  have htS : m.modelEmbedding t ∈ normalizer
      ((c.ordinaryModule ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    rw [← m.shortRoot_image hn]
    exact (RootSubgroup.group (F := m.Field) 4).le_normalizer_map m.modelEmbedding
      (mem_map_of_mem m.modelEmbedding (RootTori.torus_le_normalizer 4 t.property))
  have hc := (mem_normalizer_iff.mp (hN ⟨htN, htS⟩) a).mp ha
  have heq : m.modelEmbedding t * a * (m.modelEmbedding t)⁻¹ = b := by
    rw [← he, ← hey, ← map_inv, ← map_mul, ← map_mul, ht]
  exact heq ▸ hc

variable [Finite G]
/-- Condition (E) supplies characteristic two for the literal root normalizer. -/
theorem rootNormalizer_characteristicTwo (m : OrdinarySymplecticMarking c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    HasCharacteristicTwo m.rootNormalizer :=
  Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
    (h.simpleQTKE.evenCharacteristic T) (m.rootNormalizer_twoLocal hn)
    (m.sylow_le_rootNormalizer hn D))

/-- The Sylow-central generation argument of (*) and B.2.14, applied to the
actual normalizer span and its literal centralizer quotient. -/
theorem rootSpan_isPReduced (m : OrdinarySymplecticMarking c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    IsPReduced 2 (m.rootSpan.subgroupOf m.rootNormalizer) := by
  let S := c.ordinaryModule ⊓ centralizer (L : Set G)
  have hSN : S ≤ m.rootNormalizer :=
    inf_le_left.trans ((m.fullModule_le_second hn).trans m.second_le_rootNormalizer)
  have hST : S ≤ (T : Subgroup G) := inf_le_left.trans (m.fullModule_le_sylow hn)
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) := by
    have hTW : (T : Subgroup G) ≤ normalizer (c.ordinaryModule : Set G) := by
      rw [m.full_module]
      exact D.sylow_normalizes_component.trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
    exact (le_inf hTW (D.sylow_normalizes_component.trans
      (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf
  let S' := S.subgroupOf m.rootNormalizer
  let A := normalizer (S' : Set m.rootNormalizer)
  let P := T.subtype (m.sylow_le_rootNormalizer hn D)
  have hPA : (P : Subgroup m.rootNormalizer) ≤ A := by
    change (P : Subgroup m.rootNormalizer) ≤ normalizer (S.subgroupOf m.rootNormalizer : Set m.rootNormalizer)
    rw [← subgroupOf_normalizer_eq hSN]
    exact fun x hx => hTS hx
  have hS'P : S' ≤ P := fun _ hx => hST hx
  have he : IsElementaryAbelian 2 S' := by
    let := c.c28.module_elementary
    let : IsElementaryAbelian 2 S := IsElementaryAbelian.of_le (show S ≤ c.ordinaryModule from inf_le_left)
    exact IsElementaryAbelian.subgroupOf hSN
  have hne : S' ≠ ⊥ := by
    intro hb
    have hh := congrArg (fun B : Subgroup m.rootNormalizer => B.map m.rootNormalizer.subtype) hb
    rw [map_subgroupOf_eq_of_le hSN, Subgroup.map_bot] at hh
    exact m.shortRoot_ne_bot hn hh
  have hirr (E : Subgroup m.rootNormalizer) (_ : (MonoidHom.id m.rootNormalizer).ker ≤ E)
      (hE : E ≤ S') (hAE : A ≤ normalizer (E : Set m.rootNormalizer)) :
      E = (MonoidHom.id m.rootNormalizer).ker ∨ E = S' := by
    have hES : E.map m.rootNormalizer.subtype ≤ S := by
      simpa only [S', map_subgroupOf_eq_of_le hSN] using
        (map_mono (f := m.rootNormalizer.subtype) hE)
    have hNE : m.rootNormalizer ⊓ normalizer (S : Set G) ≤
        normalizer (E.map m.rootNormalizer.subtype : Set G) := by
      rintro x ⟨hxN, hxS⟩
      have hxA : (⟨x, hxN⟩ : m.rootNormalizer) ∈ A := by
        change (⟨x, hxN⟩ : m.rootNormalizer) ∈ normalizer (S.subgroupOf m.rootNormalizer : Set m.rootNormalizer)
        rw [← subgroupOf_normalizer_eq hSN]
        exact hxS
      exact E.le_normalizer_map m.rootNormalizer.subtype
        (mem_map_of_mem m.rootNormalizer.subtype (hAE hxA))
    rcases m.shortRoot_invariant_dichotomy hn (E.map m.rootNormalizer.subtype) hES hNE with hb | heq
    · left
      rw [MonoidHom.ker_id]
      exact (map_eq_bot_iff_of_injective _ m.rootNormalizer.subtype_injective).mp hb
    · right
      apply map_injective m.rootNormalizer.subtype_injective
      simpa only [S', map_subgroupOf_eq_of_le hSN] using heq
  have hr := isPReduced_normalClosure_image_of_irreducible (MonoidHom.id m.rootNormalizer)
    Function.surjective_id S' A P (m.rootNormalizer_characteristicTwo hn D h) he
    (by rw [MonoidHom.ker_id]; exact bot_le) (by rw [MonoidHom.ker_id]; exact Ne.symm hne)
    hS'P hPA le_rfl hirr
  simpa only [map_id, S', normalClosure_subgroupOf_eq_conjugateSpanBy S m.rootNormalizer hSN, S, rootSpan] using hr
/-- The reduced span lies in the actual two-core. -/
theorem rootSpan_le_rootCore (m : OrdinarySymplecticMarking c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    m.rootSpan ≤ m.rootCore := by
  have hh := map_mono (f := m.rootNormalizer.subtype) (m.rootSpan_isPReduced hn D h).le_pCore
  rwa [map_subgroupOf_eq_of_le (m.rootSpan_le_rootNormalizer hn)] at hh

/-- Reducedness makes the whole root core centralize the root span. -/
theorem rootCore_le_centralizer_rootSpan (m : OrdinarySymplecticMarking c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    m.rootCore ≤ centralizer (m.rootSpan : Set G) := by
  rintro q ⟨x, hx, rfl⟩ u hu
  have huN := m.rootSpan_le_rootNormalizer hn hu
  have hh := (m.rootSpan_isPReduced hn D h).le_centralizer_pCore
    (show (⟨u, huN⟩ : m.rootNormalizer) ∈ m.rootSpan.subgroupOf m.rootNormalizer from hu) x hx
  exact (congrArg Subtype.val hh).symm

omit [Finite G] in
/-- The ambient Sylow contains the root-normalizer core. -/
theorem rootCore_le_sylow (m : OrdinarySymplecticMarking c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) : m.rootCore ≤ (T : Subgroup G) := by
  let P := T.subtype (m.sylow_le_rootNormalizer hn D)
  exact (pCoreIn_le_sylow m.rootNormalizer P).trans (by
    rintro _ ⟨x, hx, rfl⟩
    exact hx)

end OrdinarySymplecticMarking
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
