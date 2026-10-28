module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.GM02.Inputs
public import Theory.Representation.BinaryOffender.CentralCoverConjugateGeneration
public import Theory.Representation.BinaryOffender.CubicConjugateBound.CentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.InnerAutomorphisms
public import Theory.Mathieu.M23.Properties.TwoRank
public import Theory.Mathieu.SmallModuleRanks

/-!
# The generation and displacement reductions for large Mathieu modules

The simple quotient's involution generation lifts to the original component:
faithfulness excludes central involutions, and perfectness lifts generation
through the central kernel. Innerness of all model automorphisms gives
G = F*(G), so this also handles every ambient involution.

The proved native two-rank bounds then give binary degree at most 24 for
M23 and at most 48 for M24, conditional only on the intrinsic conjugate
calculations. Independently of generation, a source M24 module has an
involution moving at most twelve dimensions. This excludes degree 44 once
the representation-theoretic lower bound eighteen is supplied.

Source: GM02 equations (2.5)--(2.6) and Proposition 5.1, manuscript pp.4,16--17.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Sporadic.Mathieu
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem source_generation {S : Type*} [Group S] {n : ℕ}
    (hg : InvolutionGeneration S n)
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* S)
    (htop : generalizedFitting G = ⊤) :
    ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      ∃ c : Fin n → G, generalizedFitting G ≤
        closure (Set.range fun i => c i * t * (c i)⁻¹) := by
  let L := generalizedFitting G
  let : IsQuasisimple L := h.quasisimple
  let σ : Representation (ZMod 2) L V := ρ.comp L.subtype
  let : σ.IsIrreducible := h.irreducible
  intro t ht ht2
  let x : L := ⟨t, by change t ∈ generalizedFitting G; simp only [htop, mem_top]⟩
  obtain ⟨d, hd⟩ := conjugate_generation_of_central_quotient σ
    (h.faithful.comp Subtype.val_injective) e hg x
    (fun hx => ht (congrArg Subtype.val hx)) (Subtype.ext ht2)
  refine ⟨fun i => (d i : G), ?_⟩
  have hm := congrArg (fun H : Subgroup L => H.map L.subtype) hd
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype] at hm
  rw [← Set.range_comp] at hm
  exact (show closure (Set.range fun i => (d i : G) * t * (d i : G)⁻¹) = L
    from hm).ge

omit [FiniteDimensional (ZMod 2) V] in
/-- The central quotient bounds the original actor's two-rank, even for covers. -/
theorem m23_source_twoRank
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M23) :
    primeRank 2 G ≤ 4 := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  exact (primeRank_le_central_quotient_automorphisms_of_irreducible ρ (generalizedFitting G)
    h.faithful e).trans m23_automorphism_twoRank_le_four

omit [FiniteDimensional (ZMod 2) V] in
/-- The M24 automorphism two-rank six bounds all allowed original actors. -/
theorem m24_source_twoRank
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M24) :
    primeRank 2 G ≤ 6 := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  exact (primeRank_le_central_quotient_automorphisms_of_irreducible ρ (generalizedFitting G)
    h.faithful e).trans m24_automorphism_twoRank_le_six

/-- The exact M23 degree window follows from its three-conjugate calculation. -/
theorem m23_degree_le_twenty_four (hg : InvolutionGeneration M23 3)
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M23) :
    Module.finrank (ZMod 2) V ≤ 24 := by
  let L := generalizedFitting G
  let : IsQuasisimple L := h.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have ht := generalizedFitting_eq_top_of_inner_centralQuotient e m23_conj_surjective
  exact finrank_le_of_cubicRatio_and_conjugates ρ L
    (fixedSpace_eq_bot_of_faithful_irreducible_restriction ρ L h.faithful)
    (m23_source_twoRank ρ h e) (source_generation hg ρ h e ht) h.cubic_le_two

/-- The exact M24 degree window follows from its four-conjugate calculation. -/
theorem m24_degree_le_forty_eight (hg : InvolutionGeneration M24 4)
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M24) :
    Module.finrank (ZMod 2) V ≤ 48 := by
  let L := generalizedFitting G
  let : IsQuasisimple L := h.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have ht := generalizedFitting_eq_top_of_inner_centralQuotient e
    M24OuterRestriction.conj_surjective
  exact finrank_le_of_cubicRatio_and_conjugates ρ L
    (fixedSpace_eq_bot_of_faithful_irreducible_restriction ρ L h.faithful)
    (m24_source_twoRank ρ h e) (source_generation hg ρ h e ht) h.cubic_le_two

/-- The original M24 source action contains an involution of displacement at most twelve. -/
theorem m24_exists_small_involution
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M24) :
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧ fixedCodim ρ (zpowers t) ≤ 12 := by
  obtain ⟨t, ht, ht2, hd⟩ := exists_involution_of_cubicRatio_le_nat ρ h.cubic_le_two
  exact ⟨t, ht, ht2, hd.trans (Nat.mul_le_mul_left 2 (m24_source_twoRank ρ h e))⟩

/-- The degree-forty-four displacement calculation excludes that row for the
actual source action. The generation and spectrum calculations are not used. -/
theorem m24_degree_ne_forty_four (hmoved : M24Degree44Displacement.{u,v})
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* M24) :
    Module.finrank (ZMod 2) V ≠ 44 := by
  intro hd
  let L := generalizedFitting G
  let : IsQuasisimple L := h.quasisimple
  have htop := generalizedFitting_eq_top_of_inner_centralQuotient e
    M24OuterRestriction.conj_surjective
  obtain ⟨t, ht, ht2, hsmall⟩ := m24_exists_small_involution ρ h e
  let x : L := ⟨t, by change t ∈ generalizedFitting G; simp only [htop, mem_top]⟩
  have hlarge := hmoved (ρ.comp L.subtype)
    (h.faithful.comp Subtype.val_injective) h.irreducible ⟨e⟩ hd x
    (fun hx => ht (congrArg Subtype.val hx)) (Subtype.ext ht2)
  have he : fixedCodim (ρ.comp L.subtype) (zpowers x) = fixedCodim ρ (zpowers t) := by
    rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
    rfl
  rw [he] at hlarge
  omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
