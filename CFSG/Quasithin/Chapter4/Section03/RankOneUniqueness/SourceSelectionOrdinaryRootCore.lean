module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryRootGeometry
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.ReducedNormal.IrreducibleClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCore.Automorphism
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Reduced root span and actual root-core decomposition in the raw choice

The torus acts transitively on the short-root seed. The original Sylow
normalizes the long root, so even characteristic and the Sylow-central seed
argument prove reducedness of its normal span. Thus the root core centralizes
that span and the second two-core. The concrete plane automorphism calculation
then gives Q_Z = O₂(K₂) C_{Q_Z}(W), using the actual full module W.

These arguments extend OrdinaryRootCore.Reduced/Decomposition to OutsideChoice.
They do not require the unproved H = N_G(K). The terminal source consumer
uses the decomposition here; its secondary/FF comparison remains explicit.
Source: Aschbacher–Smith 4.3.6 (*) and (**), printed pp.614–615.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
namespace OutsideSymplecticMarking
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : OutsideChoice T L} {K : Subgroup c.H} {n : ℕ}
theorem shortRoot_image (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    (RootSubgroup.group (F := m.Field) 4).map m.modelEmbedding =
      c.ordinaryModule ⊓ centralizer (L : Set G) := by
  have hh := map_inf_centralizer_of_injective m.modelEmbedding m.modelEmbedding_injective
    ((Plane.radical (F := m.Field)).map planeLocal.subtype) planeLocal
  rw [m.planeRadical_image hn, m.planeLocal_image,
    OrdinaryRootCoreMatrix.plane_fixed_eq_root_four] at hh
  exact hh.symm

theorem second_le_rootNormalizer (m : OutsideSymplecticMarking c K n) :
    m.second ≤ m.rootNormalizer := (map_subtype_le _).trans inf_le_right

theorem rootSpan_le_rootNormalizer (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    m.rootSpan ≤ m.rootNormalizer :=
  conjugateSpanBy_le_self (inf_le_left.trans
    ((m.fullModule_le_second hn).trans m.second_le_rootNormalizer))

theorem second_core_conjugateSpan (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    conjugateSpanBy (c.ordinaryModule ⊓ centralizer (L : Set G)) m.second =
      m.second.pCoreIn 2 := by
  rw [← m.shortRoot_image hn, ← m.pointLocal_image hn, ← map_conjugateSpanBy,
    OrdinaryRootCoreMatrix.root_four_span m.card hn]
  rw [AmalgamLocalCores.pCoreIn_map_of_injective 2 _ m.modelEmbedding_injective,
    pCoreIn, pointLocal_core_eq m.card hn]

theorem second_core_le_rootSpan (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    m.second.pCoreIn 2 ≤ m.rootSpan := by
  rw [← m.second_core_conjugateSpan hn]
  exact conjugateSpanBy_mono le_rfl m.second_le_rootNormalizer

theorem fullModule_le_sylow (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
    c.ordinaryModule ≤ (T : Subgroup G) := by
  intro w hw
  obtain ⟨a, ha, he⟩ := (m.planeRadical_image hn).ge hw
  have hau : a ∈ unipotent := ⟨OrdinaryRootCoreMatrix.plane_radical_le_point ha,
    map_subtype_le _ ha⟩
  exact ((m.unipotent_image).le ⟨a, hau, he⟩).1

theorem shortRoot_ne_bot (m : OutsideSymplecticMarking c K n) (hn : 1 < n) :
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
theorem shortRoot_invariant_dichotomy (m : OutsideSymplecticMarking c K n) (hn : 1 < n)
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
theorem rootNormalizer_characteristicTwo (m : OutsideSymplecticMarking c K n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    HasCharacteristicTwo m.rootNormalizer :=
  Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
    (h.simpleQTKE.evenCharacteristic T) (m.rootNormalizer_twoLocal hn)
    (m.sylow_le_rootNormalizer hn D))

/-- The Sylow-central generation argument of (*) and B.2.14, applied to the
actual normalizer span and its literal centralizer quotient. -/
theorem rootSpan_isPReduced (m : OutsideSymplecticMarking c K n) (hn : 1 < n)
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
    have hw : IsElementaryAbelian 2 c.ordinaryModule := by
      rw [←m.planeRadical_image hn]
      let : IsElementaryAbelian 2 ((Plane.radical (F := m.Field)).map planeLocal.subtype) :=
        IsElementaryAbelian.map _
      exact IsElementaryAbelian.map _
    let := hw
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
theorem rootSpan_le_rootCore (m : OutsideSymplecticMarking c K n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    m.rootSpan ≤ m.rootCore := by
  have hh := map_mono (f := m.rootNormalizer.subtype) (m.rootSpan_isPReduced hn D h).le_pCore
  rwa [map_subgroupOf_eq_of_le (m.rootSpan_le_rootNormalizer hn)] at hh

/-- Reducedness makes the whole root core centralize the root span. -/
theorem rootCore_le_centralizer_rootSpan (m : OutsideSymplecticMarking c K n) (hn : 1 < n)
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
theorem rootCore_le_sylow (m : OutsideSymplecticMarking c K n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) : m.rootCore ≤ (T : Subgroup G) := by
  let P := T.subtype (m.sylow_le_rootNormalizer hn D)
  exact (pCoreIn_le_sylow m.rootNormalizer P).trans (by
    rintro _ ⟨x, hx, rfl⟩
    exact hx)
/-- Every root-core element induces on the full module the action of an
actual element of the second subgroup's two-core. -/
theorem rootCore_action (m : OutsideSymplecticMarking c K n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (x : G) (hx : x ∈ m.rootCore) :
    ∃ y ∈ m.second.pCoreIn 2, ∀ w ∈ c.ordinaryModule,
      x * w * x⁻¹ = y * w * y⁻¹ := by
  let : Algebra (ZMod 2) m.Field := ZMod.algebra m.Field 2
  have hxL : x ∈ normalizer (L : Set G) :=
    D.sylow_normalizes_component (m.rootCore_le_sylow hn D hx)
  let e : planeLocal (F := m.Field) ≃* L :=
    ((planeLocal (F := m.Field)).equivMapOfInjective m.modelEmbedding
      m.modelEmbedding_injective).trans (MulEquiv.subgroupCongr m.planeLocal_image)
  let aL : MulAut L := L.normalizerMonoidHom ⟨x, hxL⟩
  let α : MulAut (planeLocal (F := m.Field)) := e.trans (aL.trans e.symm)
  have he (g : planeLocal (F := m.Field)) : (e g : G) = m.modelEmbedding g := rfl
  have hα (g : planeLocal (F := m.Field)) :
      m.modelEmbedding (α g) = x * m.modelEmbedding g * x⁻¹ := by
    have hh : e (α g) = aL (e g) := e.apply_symm_apply _
    exact congrArg Subtype.val hh
  have hfix (q : Plane.radical (F := m.Field))
      (hq : q.val.val ∈ (pointRadical (F := m.Field)).map pointLocal.subtype) :
      α q.val = q.val := by
    apply Subtype.ext
    apply m.modelEmbedding_injective
    rw [hα]
    have hqB : m.modelEmbedding q.val.val ∈ m.second.pCoreIn 2 :=
      (m.pointRadical_image hn).le (mem_map_of_mem m.modelEmbedding hq)
    have hcomm := m.rootCore_le_centralizer_rootSpan hn D h hx
      (m.modelEmbedding q.val.val) (m.second_core_le_rootSpan hn hqB)
    rw [← hcomm, mul_inv_cancel_right]
  obtain ⟨t, ht⟩ := OrdinaryRootCoreMatrix.plane_automorphism_fixing_point_radical
    m.card hn α hfix
  let y : G := m.modelEmbedding (Plane.levi (Representation.SL2OrthogonalCover.upper t)).val
  have hy : y ∈ m.second.pCoreIn 2 :=
    (m.pointRadical_image hn).le (mem_map_of_mem m.modelEmbedding
      (OrdinaryRootCoreMatrix.levi_upper_mem_point_radical t))
  refine ⟨y, hy, ?_⟩
  intro w hw
  obtain ⟨g, hg, rfl⟩ := (m.planeRadical_image hn).ge hw
  obtain ⟨q, hq, rfl⟩ := hg
  have hh := congrArg (fun g : planeLocal (F := m.Field) => m.modelEmbedding g.val)
    (ht ⟨q, hq⟩)
  rw [hα] at hh
  simpa only [y, Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    map_mul, map_inv] using hh

/-- The source equality (**) for the literal root core and full source module. -/
theorem rootCore_decomposition (m : OutsideSymplecticMarking c K n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)) := by
  have hBQ : m.second.pCoreIn 2 ≤ m.rootCore :=
    (m.second_core_le_rootSpan hn).trans (m.rootSpan_le_rootCore hn D h)
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, ha⟩ := m.rootCore_action hn D h x hx
    have hz : y⁻¹*x ∈ m.rootCore ⊓ centralizer (c.ordinaryModule : Set G) := by
      refine ⟨m.rootCore.mul_mem (m.rootCore.inv_mem (hBQ hy)) hx, ?_⟩
      intro w hw
      have hzconj : (y⁻¹*x)*w*(y⁻¹*x)⁻¹ = w := by
        calc
          _ = y⁻¹*(x*w*x⁻¹)*y := by group
          _ = y⁻¹*(y*w*y⁻¹)*y := by rw [ha w hw]
          _ = w := by group
      calc
        w*(y⁻¹*x) = ((y⁻¹*x)*w*(y⁻¹*x)⁻¹)*(y⁻¹*x) := by rw [hzconj]
        _ = (y⁻¹*x)*w := by group
    simpa only [mul_inv_cancel_left] using
      (m.second.pCoreIn 2 ⊔ (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G))).mul_mem
        (mem_sup_left hy) (mem_sup_right hz)
  · exact sup_le hBQ inf_le_left

end OutsideSymplecticMarking
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
