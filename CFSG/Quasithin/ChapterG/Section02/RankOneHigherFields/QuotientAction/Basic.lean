module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Reduction
public import CFSG.Quasithin.ChapterG.Section02.Binary.Quotient
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# The literal higher-field quotient action in G.2.3

The Frattini bound and the product S=WWᵍ make the actual S/S₂ elementary
abelian. Its conjugation action descends through the literal I/S comparison
with SL₂(F). The original marked factors are complementary, their root
commutators are bounded, and the full root normalizer preserves the first
factor by lifting through L₁*. No projective map or natural decomposition is
assumed in these constructions.

The final two counting lemmas are conditional on an equivalence with s
natural planes; they tie the marked relative index and |U| to that same s.
Constructing the projective map and invoking recognition remain separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3(6–7), printed pp.333–334, and G.1.5(3), printed p.328.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
open Setup
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g : G} (d : Hypothesis D F n g)

namespace Hypothesis
include d

/-- The actor map is the literal I/S comparison followed by the given model. -/
def quotientActionProjection (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) : D.I g →* SL(2, F) :=
  (d.coreQuotientEquiv hUT hstar).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 (D.I g)))

theorem quotientActionProjection_apply (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) (i : D.I g) :
    d.quotientActionProjection hUT hstar i = d.model (d.IStarProjection hUT hstar i) := rfl

theorem quotientActionProjection_surjective (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) :
    Function.Surjective (d.quotientActionProjection hUT hstar) :=
  (d.coreQuotientEquiv hUT hstar).surjective.comp (QuotientGroup.mk'_surjective _)

theorem quotientActionProjection_ker (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) :
    (d.quotientActionProjection hUT hstar).ker = (D.S g).subgroupOf (D.I g) := by
  have hk : (d.quotientActionProjection hUT hstar).ker = pCore 2 (D.I g) := by
    ext i
    change d.model (d.IStarProjection hUT hstar i) = 1 ↔ _
    rw [d.model.map_eq_one_iff]
    change i ∈ (d.IStarProjection hUT hstar).ker ↔ _
    rw [d.IStarProjection_ker hUT hstar]
  rw [hk]
  exact ((pCore 2 (D.I g)).comap_map_eq_self_of_injective (D.I g).subtype_injective).symm

/-- Transport of every literal subgroup image through the same starred map. -/
theorem quotientActionProjection_map (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) (A : Subgroup G) (hAI : A ≤ D.I g) :
    (A.subgroupOf (D.I g)).map (d.quotientActionProjection hUT hstar) =
      ((D.star A).subgroupOf (D.star D.L)).map d.model.toMonoidHom := by
  have he : (A.subgroupOf (D.I g)).map (d.IStarProjection hUT hstar) =
      (D.star A).subgroupOf (D.star D.L) := by
    ext a
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨inclusion (d.I_le_LT hUT) i, hi, rfl⟩
    · intro ha
      obtain ⟨x, hx, he⟩ := ha
      refine ⟨⟨x, hAI hx⟩, hx, Subtype.ext ?_⟩
      exact he
  change (A.subgroupOf (D.I g)).map
    (d.model.toMonoidHom.comp (d.IStarProjection hUT hstar)) = _
  rw [← map_map, he]

/-- The marked root image is an image of the original U, not a chosen conjugate. -/
def quotientRoot (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) : Subgroup SL(2, F) :=
  (D.U.subgroupOf (D.I g)).map (d.quotientActionProjection hUT hstar)

theorem quotientRoot_eq_star (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) :
    d.quotientRoot hUT hstar =
      ((D.star D.U).subgroupOf (D.star D.L)).map d.model.toMonoidHom :=
  d.quotientActionProjection_map hUT hstar D.U le_sup_left

/-- The Sylow marking is transported from the literal L*, preserving U*. -/
theorem quotientRoot_sylow (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U) :
    ∃ R : Sylow 2 SL(2, F), (R : Subgroup SL(2, F)) = d.quotientRoot hUT hstar := by
  obtain ⟨P, hP⟩ := hSylow
  refine ⟨P.mapSurjective (f := d.model.toMonoidHom) d.model.surjective, ?_⟩
  change (P : Subgroup (D.star D.L)).map d.model.toMonoidHom = _
  rw [d.quotientRoot_eq_star hUT hstar, ← hP]
  congr 1
  exact (P : Subgroup (D.star D.L)).comap_map_eq_self_of_injective
    (D.star D.L).subtype_injective |>.symm

theorem quotientRoot_card (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L)
    (hU : Nat.card (D.star D.U) = 2 ^ n) :
    Nat.card (d.quotientRoot hUT hstar) = 2 ^ n := by
  have hUL : D.star D.U ≤ D.star D.L :=
    (binary_star_mono (show D.U ≤ D.I g from le_sup_left)).trans hstar.le
  rw [d.quotientRoot_eq_star hUT hstar,
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ d.model.injective).toEquiv.symm,
    Nat.card_congr (subgroupOfEquivOfLe hUL).toEquiv, hU]

theorem quotientIntersection_normalizes (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.I g ≤ normalizer (D.S₂ g : Set G) :=
  (normal_subgroupOf_iff_le_normalizer
    (show D.S₂ g ≤ D.I g from inf_le_left.trans le_sup_left)).mp
      (d.intersection hUT hf).2.2.1

theorem quotientIntersection_normal (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    ((D.S₂ g).subgroupOf (D.S g)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 (D.I g)).trans (d.quotientIntersection_normalizes hUT hf))

/-- The elementary structure on the literal S/S₂ is proved from G.2.2. -/
theorem quotient_elementary (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (hsplit : D.S g = WProduct D g) :
    let := d.quotientIntersection_normal hUT hf
    IsElementaryAbelian 2 ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g)) := by
  have hl := d.intersection hUT hf
  have hsquare : ∀ u ∈ D.U, u ^ 2 ∈ D.V₁ := by
    let : Fact (IsPGroup 2 D.U) := ⟨d.U_isPGroup hUT⟩
    intro u hu
    exact hf ⟨(⟨u, hu⟩ : D.U) ^ 2, pth_power_mem_frattini_of_isPGroup _, rfl⟩
  exact D.binary_quotient_elementary g (d.g_mem_I_of_star hUT hstar.ge)
    (normalizes_of_span D d.span_eq d.g_mem) d.setup.point_le hl.1 hl.2.1
    (d.quotientIntersection_normalizes hUT hf) (d.S_normalizes_U_of_star hUT hstar.ge)
    hsplit hsquare

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- The two source commutator bounds, for all lifts in U. -/
theorem quotient_root_bounds (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (σ : Representation (ZMod 2) SL(2, F) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
      (σ.comp (d.quotientActionProjection hUT hstar))) :
    ∀ a ∈ d.quotientRoot hUT hstar,
      LinearMap.range (σ a - 1) ≤ c.imageSpace (D.W g) ∧
      ∀ v ∈ c.imageSpace (D.W g), σ a v = v := by
  have hUS : ⁅D.U, D.S g⁆ ≤ D.W g :=
    le_inf (le_normalizer_iff_commutator_le_left.mp (d.S_normalizes_U_of_star hUT hstar.ge))
      (le_normalizer_iff_commutator_le_right.mp
        ((show D.U ≤ D.I g from le_sup_left).trans I_normalizes_core))
  have hUW : ⁅D.U, D.W g⁆ ≤ D.S₂ g :=
    ((commutator_mono le_rfl (show D.W g ≤ D.U from inf_le_left)).trans
      (derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf)).trans
        (d.setup.point_le.trans (d.intersection hUT hf).1)
  rintro a ⟨u, hu, rfl⟩
  exact ⟨c.displacement_range_le_imageSpace_of_commutator_le D.U (D.W g) hUS u hu,
    c.fixed_on_imageSpace_of_commutator_le D.U (D.W g) hUW u hu⟩

/-- The original marked conjugator gives the complementary image. -/
theorem quotient_marked_complement (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (hsplit : D.S g = WProduct D g)
    (σ : Representation (ZMod 2) SL(2, F) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
      (σ.comp (d.quotientActionProjection hUT hstar))) :
    IsCompl (c.imageSpace (D.W g)) (c.imageSpace (conjugate (D.W g) g)) ∧
    c.imageSpace (conjugate (D.W g) g) = (c.imageSpace (D.W g)).map
      (σ (d.quotientActionProjection hUT hstar
        (⟨g, d.g_mem_I_of_star hUT hstar.ge⟩ : D.I g)⁻¹)) := by
  exact ⟨c.isCompl_imageSpace _ _ hsplit
      (D.binary_marked_intersection g (d.g_mem_I_of_star hUT hstar.ge)
        (d.intersection hUT hf).2.1),
    c.imageSpace_conjBy (D.W g) inf_le_right
      (⟨g, d.g_mem_I_of_star hUT hstar.ge⟩ : D.I g)⁻¹⟩

/-- Relative L₁ normalization comes from its actual inclusion in H and I. -/
theorem L₁_normalizes_W (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) :
    D.L₁ ≤ normalizer (D.W g : Set G) := by
  have hL₁L : D.L₁ ≤ D.L := by
    rintro x ⟨y, _, rfl⟩
    exact y.property.1
  have hL₁H : D.L₁ ≤ D.H := le_sup_left.trans d.setup.local_le
  exact (le_inf (hL₁H.trans (le_normalizer_conjugateSpanBy D.V D.H))
    ((hL₁L.trans (d.L_le_I_of_star hUT hstar.ge)).trans I_normalizes_core)).trans
      inf_normalizer_le_normalizer_inf

/-- The Borel image is exactly the normalizer of the marked root subgroup. -/
theorem quotient_borel_image (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L)
    (hB : D.star D.L₁ = D.star D.L ⊓ normalizer (D.star D.U : Set D.Star)) :
    (D.L₁.subgroupOf (D.I g)).map (d.quotientActionProjection hUT hstar) =
      normalizer (d.quotientRoot hUT hstar : Set SL(2, F)) := by
  have hL₁L : D.L₁ ≤ D.L := by
    rintro x ⟨y, _, rfl⟩
    exact y.property.1
  have hUL : D.star D.U ≤ D.star D.L :=
    (binary_star_mono (show D.U ≤ D.I g from le_sup_left)).trans hstar.le
  rw [d.quotientActionProjection_map hUT hstar _
    (hL₁L.trans (d.L_le_I_of_star hUT hstar.ge)), hB,
    inf_subgroupOf_left, subgroupOf_normalizer_eq hUL, map_equiv_normalizer_eq,
    d.quotientRoot_eq_star hUT hstar]

/-- The full normalizer preserves the quotient mark; no invariance witness
is assumed in the construction of the subsequent projective orbit map. -/
theorem quotient_borel_invariant (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L)
    (hB : D.star D.L₁ = D.star D.L ⊓ normalizer (D.star D.U : Set D.Star))
    (σ : Representation (ZMod 2) SL(2, F) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
      (σ.comp (d.quotientActionProjection hUT hstar))) :
    ∀ a ∈ normalizer (d.quotientRoot hUT hstar : Set SL(2, F)),
      (c.imageSpace (D.W g)).map (σ a) = c.imageSpace (D.W g) := by
  intro a ha
  rw [← d.quotient_borel_image hUT hstar hB] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  have hc := c.imageSpace_conjBy (D.W g) inf_le_right i
  have hn : (D.W g).conjBy (i : G) = D.W g :=
    mem_normalizer_iff_map_conj_eq.mp (d.L₁_normalizes_W hUT hstar hi)
  rw [hn] at hc
  exact hc.symm

/-- Construction of the elementary quotient, its actual action and the full
G.1.5(3) marked linear configuration. -/
theorem exists_quotient_action (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (hB : D.star D.L₁ = D.star D.L ⊓ normalizer (D.star D.U : Set D.Star))
    (hsplit : D.S g = WProduct D g) :
    let := d.quotientIntersection_normal hUT hf
    let := d.quotient_elementary hUT hf hstar hsplit
    ∃ (σ : Representation (ZMod 2) SL(2, F)
        (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))
      (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
        (σ.comp (d.quotientActionProjection hUT hstar))),
      (∀ s : D.S g, (c.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((D.S₂ g).subgroupOf (D.S g)) s)) ∧
      IsCompl (c.imageSpace (D.W g)) (c.imageSpace (conjugate (D.W g) g)) ∧
      c.imageSpace (conjugate (D.W g) g) = (c.imageSpace (D.W g)).map
        (σ (d.quotientActionProjection hUT hstar
          (⟨g, d.g_mem_I_of_star hUT hstar.ge⟩ : D.I g)⁻¹)) ∧
      (∀ a ∈ d.quotientRoot hUT hstar,
        LinearMap.range (σ a - 1) ≤ c.imageSpace (D.W g) ∧
        ∀ v ∈ c.imageSpace (D.W g), σ a v = v) ∧
      ∀ a ∈ normalizer (d.quotientRoot hUT hstar : Set SL(2, F)),
        (c.imageSpace (D.W g)).map (σ a) = c.imageSpace (D.W g) := by
  let := d.quotientIntersection_normal hUT hf
  let := d.quotient_elementary hUT hf hstar hsplit
  obtain ⟨σ, c, hc⟩ := Representation.BinaryConjugationSection.exists_canonical
    (D.I g) (D.S g) (D.S₂ g) (pCoreIn_le 2 _) (d.intersection hUT hf).2.1
    I_normalizes_core (d.quotientIntersection_normalizes hUT hf)
    (d.quotientActionProjection hUT hstar)
    (d.quotientActionProjection_surjective hUT hstar)
    (d.quotientActionProjection_ker hUT hstar)
  obtain ⟨hs, hg⟩ := d.quotient_marked_complement hUT hf hstar hsplit σ c
  exact ⟨σ, c, hc, hs, hg, d.quotient_root_bounds hUT hf hstar σ c,
    d.quotient_borel_invariant hUT hstar hB σ c⟩

omit d [Field F] [Finite F] [Finite G] in
private theorem imageSpace_card {H S E : Subgroup G}
    {ρ : Representation (ZMod 2) H M}
    (c : Representation.BinaryConjugationSection H S E ρ)
    (B : Subgroup G) (hBS : B ≤ S) :
    Nat.card (c.imageSpace B) = E.relIndex B := by
  change Nat.card ((B.subgroupOf S).map c.coordinates) = _
  rw [← relIndex_ker, c.kernel_eq]
  have he := relIndex_map_map_of_injective (E.subgroupOf S) (B.subgroupOf S)
    S.subtype_injective
  rw [map_subgroupOf_eq_of_le c.kernel_le, map_subgroupOf_eq_of_le hBS] at he
  exact he.symm

/-- Once recognition supplies s natural copies, the marked index has precisely
that multiplicity. Counting only needs the underlying equivalence of carriers. -/
theorem quotient_mark_index [Finite M] (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (hsplit : D.S g = WProduct D g)
    (σ : Representation (ZMod 2) SL(2, F) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
      (σ.comp (d.quotientActionProjection hUT hstar)))
    (s : ℕ) (e : M ≃ (Fin s → Fin 2 → F)) :
    (D.S₂ g).relIndex (D.W g) = 2 ^ (n * s) := by
  obtain ⟨hc, hconj⟩ := d.quotient_marked_complement hUT hf hstar hsplit σ c
  have hdim : Module.finrank (ZMod 2) (c.imageSpace (conjugate (D.W g) g)) =
      Module.finrank (ZMod 2) (c.imageSpace (D.W g)) := by
    rw [hconj]
    exact (LinearMap.GeneralLinearGroup.toLinearEquiv
      (σ.asGroupHom (d.quotientActionProjection hUT hstar
        (⟨g, d.g_mem_I_of_star hUT hstar.ge⟩ : D.I g)⁻¹))).finrank_map_eq _
  have htotal := Submodule.finrank_add_eq_of_isCompl hc
  have he : Nat.card M = 2 ^ (n * (2 * s)) := by
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun, Nat.card_fin,
      Nat.card_fin, d.field_card, ← pow_mul, ← pow_mul]
  have hdimM : Module.finrank (ZMod 2) M = n * (2 * s) := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) M = 2 ^ (n * (2 * s))
    rw [← he, Module.natCard_eq_pow_finrank (K := ZMod 2)]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
  have hmult : Module.finrank (ZMod 2) (c.imageSpace (D.W g)) = n * s := by
    rw [hdim, hdimM] at htotal
    have hexp : n * (2 * s) = 2 * (n * s) := by ring
    omega
  rw [← imageSpace_card c (D.W g) inf_le_right,
    Module.natCard_eq_pow_finrank (K := ZMod 2), hmult]
  simp only [Nat.card_eq_fintype_card, ZMod.card]

/-- G.2.3(7) uses the same s as any equivariant natural decomposition of the
literal quotient. The projective recognition step must still construct it. -/
theorem order_of_quotient_natural_copies [Finite M] (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (hU : Nat.card (D.star D.U) = 2 ^ n)
    (hsplit : D.S g = WProduct D g)
    (σ : Representation (ZMod 2) SL(2, F) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
      (σ.comp (d.quotientActionProjection hUT hstar)))
    (s : ℕ) (e : M ≃ (Fin s → Fin 2 → F)) :
    Nat.card D.U = 2 ^ (n * (s + 3)) * D.V.relIndex (D.S₂ g) :=
  d.order_of_natural_indices hUT hf hstar hU s
    (d.quotient_mark_index hUT hf hstar hsplit σ c s e)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
