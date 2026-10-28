module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceDegree.Preparation
public import Theory.Mathieu.M22.Properties.ConjugateGeneration
public import Theory.Representation.BinaryOffender.CubicConjugateBound

/-!
# The simple M₂₂ degree window from actual involution displacements

The simple component is centerless. Generalized-Fitting self-centralization
makes the ambient conjugation action faithful. The concrete three-conjugate
inner and four-conjugate automorphism bounds therefore lift to the original
group with conjugators in its marked component. Faithful irreducibility on that
component gives zero fixed space, and the displacement bound yields the degree
window of thirty using the rank and index estimates in `Preparation`.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript pp.15–16; Aschbacher–Smith, Chapter K, printed pp.451–452 and 457.
No module catalogue, module recognition or full-normalizer SQTK is assumed.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M22ConjugateGeneration
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

omit [FiniteDimensional (ZMod 2) V] in
/-- The simple marking makes the source ambient centralizer trivial. -/
theorem source_simple_centralizer_eq_bot (h : SourceHypotheses ρ L)
    (e : L ≃* M22) : centralizer (L : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have hgL : g ∈ L := by
    have hc : centralizer (L : Set G) ≤ L := by
      rw [h.component]
      exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
    exact hc hg
  let l : L := ⟨g, hgL⟩
  have hl : e l ∈ center M22 := by
    rw [mem_center_iff]
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.mp hg) y y.property
  have he : e l = 1 := mem_bot.mp (m22_center_eq_bot ▸ hl)
  have hl1 : l = 1 := e.injective (he.trans (map_one e).symm)
  exact congrArg Subtype.val hl1

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The three conjugators are elements of the given marked component. -/
theorem source_simple_inner_conjugates (e : L ≃* M22) (t : G) (htL : t ∈ L) (ht : orderOf t = 2) :
    ∃ c : Fin 3 → L, L ≤ closure (Set.range fun i =>
      (c i : G) * t * (c i : G)⁻¹) := by
  let s : L := ⟨t, htL⟩
  obtain ⟨c, hc⟩ := m22_three_conjugates_generate (e s)
    ((e.orderOf_eq s).trans ((Subgroup.orderOf_coe s).symm.trans ht))
  let f : M22 →* G := L.subtype.comp e.symm.toMonoidHom
  refine ⟨fun i => e.symm (c i), ?_⟩
  have hf : f.range = L := by
    change (L.subtype.comp e.symm.toMonoidHom).range = L
    rw [MonoidHom.range_comp,
      show e.symm.toMonoidHom.range = ⊤ from MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hm := congrArg (fun H : Subgroup M22 => H.map f) hc
  rw [map_conjugate_closure, ← MonoidHom.range_eq_map, hf] at hm
  simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    e.symm_apply_apply, Subgroup.subtype_apply, s] using hm.ge

omit [FiniteDimensional (ZMod 2) V] in
/-- Every ambient involution has four component conjugates whose closure contains L. -/
theorem source_simple_ambient_conjugates (h : SourceHypotheses ρ L)
    (e : L ≃* M22) (t : G) (ht : orderOf t = 2) :
    ∃ c : Fin 4 → L, L ≤ closure (Set.range fun i =>
      (c i : G) * t * (c i : G)⁻¹) := by
  let : L.Normal := h.component.symm ▸ inferInstance
  let f : G →* MulAut M22 :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut L)
  have hf : Function.Injective f := (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L
      (source_simple_centralizer_eq_bot ρ L h e))
  have he (l : L) : f (l : G) = MulAut.conj (e l) := by
    change MulAut.congr e (MulAut.conjNormal (l : G)) = _
    rw [MulAut.conjNormal_val, MulAut.congr_conj]
  obtain ⟨c, hc⟩ := m22_four_conjugates_automorphisms (f t)
    ((orderOf_injective f hf t).trans ht)
  refine ⟨fun i => e.symm (c i), ?_⟩
  apply le_conjugate_closure_of_map f hf L t
    (fun i => (e.symm (c i) : G))
  have hL : L.map f ≤ (MulAut.conj : M22 →* MulAut M22).range := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨e ⟨l, hl⟩, (he ⟨l, hl⟩).symm⟩
  simpa only [he, e.apply_symm_apply] using hL.trans hc

omit [Finite G] in
/-- An inner involution moves at least one third of the original binary module. -/
theorem source_simple_inner_involution_bound (h : SourceHypotheses ρ L)
    (e : L ≃* M22) (t : G) (htL : t ∈ L) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (zpowers t) := by
  let : Nontrivial M22 := m22_isSimpleGroup.toNontrivial
  let : Nontrivial L := e.toEquiv.nontrivial
  obtain ⟨c, hc⟩ := source_simple_inner_conjugates L e t htL ht
  exact finrank_le_mul_fixedCodim_of_conjugate_generation ρ L
    (fixedSpace_eq_bot_of_faithful_irreducible_on ρ L h.faithful h.irreducible)
    t (fun i => (c i : G)) hc

/-- Any ambient involution moves at least one quarter of the original binary module. -/
theorem source_simple_ambient_involution_bound (h : SourceHypotheses ρ L)
    (e : L ≃* M22) (t : G) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) V ≤ 4 * fixedCodim ρ (zpowers t) := by
  let : Nontrivial M22 := m22_isSimpleGroup.toNontrivial
  let : Nontrivial L := e.toEquiv.nontrivial
  obtain ⟨c, hc⟩ := source_simple_ambient_conjugates ρ L h e t ht
  exact finrank_le_mul_fixedCodim_of_conjugate_generation ρ L
    (fixedSpace_eq_bot_of_faithful_irreducible_on ρ L h.faithful h.irreducible)
    t (fun i => (c i : G)) hc

/-- The genuine source action with simple M₂₂ component has binary degree at most thirty. -/
theorem source_simple_finrank_le_thirty (h : SourceHypotheses ρ L)
    (e : L ≃* M22) : Module.finrank (ZMod 2) V ≤ 30 := by
  exact source_finrank_le_thirty_of_involution_bounds ρ L h
    (source_simple_inner_involution_bound ρ L h e)
    (source_simple_ambient_involution_bound ρ L h e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
