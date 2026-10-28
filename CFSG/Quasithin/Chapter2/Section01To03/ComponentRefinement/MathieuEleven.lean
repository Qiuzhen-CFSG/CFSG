module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import Theory.Mathieu.M11.Properties.InvolutionCentralizer

/-!
# The M₁₁ intersection in Lemma 2.3.9(7)(d)

Every involution in the concrete M₁₁ model is conjugate to the standard
generator. Its centralizer is a maximal subgroup, by the existing permutation
and word-certificate proof. Transporting this fact through the supplied model
isomorphism forces L ∩ M = C_L(z_L). The projection z_L is constructed from
the actual inner action of z and is proved to be an involution.

This proves the M₁₁ intersection case conditional on the genuine M₁₁
identification and inner action from 1.1.5(3). Excluding other sporadic models
or central covers is not assumed to follow from this calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 2.3.9(7)(d), printed pp.525–526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup Sporadic.Mathieu

variable {K P : Type*} [Group K] [Group P]

private theorem map_centralizer_equiv (e : K ≃* P) (t : K) :
    (centralizer ({t} : Set K)).map e.toMonoidHom =
      centralizer ({e t} : Set P) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa using congrArg e (mem_centralizer_singleton_iff.mp hx)
  · intro hy
    refine mem_map.mpr ⟨e.symm y, mem_centralizer_singleton_iff.mpr ?_, by simp⟩
    apply e.injective
    simpa using mem_centralizer_singleton_iff.mp hy

private theorem m11_centralizer_maximal (t : M11) (ht : orderOf t = 2) :
    IsCoatom (centralizer ({t} : Set M11)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (m11_involution_isConj_generatorA t ht)
  have he : (MulAut.conj g) t = m11GeneratorAInM11 := hg
  apply (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup
    (centralizer ({t} : Set M11))).mp
  change IsCoatom ((centralizer ({t} : Set M11)).map (MulAut.conj g).toMonoidHom)
  rw [map_centralizer_equiv, he]
  exact m11_involutionCentralizer_isCoatom

private theorem m11_center_eq_bot : center M11 = ⊥ := by
  let : IsSimpleGroup M11 := m11_isSimpleGroup
  rcases (inferInstance : (center M11).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply m11_involutionCentralizer_isCoatom.ne_top
    apply top_unique
    intro x _
    have hx : x ∈ center M11 := by rw [h]; trivial
    exact mem_centralizer_singleton_iff.mpr
      (mem_center_iff.mp hx m11GeneratorAInM11).symm

private theorem center_eq_bot_of_m11 (e : K ≃* M11) : center K = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have he : e x ∈ center M11 := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    simpa using congrArg e (mem_center_iff.mp hx a)
  rw [m11_center_eq_bot, mem_bot] at he
  exact e.injective (he.trans (map_one e).symm)

/-- The concrete M₁₁ branch of 2.3.9(7)(d), including the actual involution
projection and the equality of subgroups inside G. -/
theorem mathieuEleven_intersection {G : Type*} [Group G]
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M11)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃ t : L, orderOf t = 2 ∧ IsConjugationProjection L z t ∧
      L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G) := by
  obtain ⟨t, ht, _⟩ := h.exists_unique_projection (center_eq_bot_of_m11 e) α hα hinner
  have hmax : IsCoatom (centralizer ({t} : Set L)) := by
    apply (OrderIso.isCoatom_iff e.mapSubgroup (centralizer ({t} : Set L))).mp
    change IsCoatom ((centralizer ({t} : Set L)).map e.toMonoidHom)
    rw [map_centralizer_equiv]
    apply m11_centralizer_maximal
    simpa using ht.2
  have hle : centralizer ({t} : Set L) ≤ M.subgroupOf L := by
    intro x hx
    have hc : (x : G) ∈ centralizer ({(t : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))
    exact (projection_centralizer_le_intersection ht.1 h.centralizer_le
      ⟨x.property, hc⟩).2
  have hproper : M.subgroupOf L ≠ ⊤ :=
    fun he => h.outside (subgroupOf_eq_top.mp he)
  have heq := (hmax.le_iff_eq hproper).mp hle
  refine ⟨t, ht.2, ht.1, ?_⟩
  apply le_antisymm _ (projection_centralizer_le_intersection ht.1 h.centralizer_le)
  rintro x ⟨hxL, hxM⟩
  refine ⟨hxL, mem_centralizer_singleton_iff.mpr ?_⟩
  have hx : (⟨x, hxL⟩ : L) ∈ M.subgroupOf L := hxM
  rw [heq] at hx
  exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
