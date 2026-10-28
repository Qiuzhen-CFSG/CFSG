module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.Initial
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.Algebra
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.FourGroupChoice.Reflection
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.FourGroupChoice.Square
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.FourGroupChoice.Dihedral
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.FourGroupChoice.SquareMembership.Fusion
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.ActionNormalizer

/-!
# Compatible four-groups in the terminal A₆ construction

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.569–570, following Lemma 2.5.27; the initial choice of `x` is on p.554.

A reflection in the dihedral inner Sylow subgroup and its central involution
generate a Klein four-group. An explicit orbit identity in actual `Aut(A₆)`
permits replacing `x` by `xs` so that the conjugate reflection centralizes its
full `K`-normalizer. The replacement preserves `Setup` and `CoreReduction`.
The completed action-normalizer lift then gives the normalizer order 64.

Square stability is equivalent to `x² ∈ S_K S_Kˣ`; changing the representative
of `xS` cannot repair failure of that membership. The fusion argument proves
the membership using `C_G(t) ≤ H`, supplied by source 2.5.22(2), and explicit
identities in the actual A₆ model. `exists_compatible_four_of_source` combines
this result with the compatible-choice construction, retaining `xs` in its
conclusion. The source assembly must supply that centralizer premise and the
model identities; the stronger `Setup`-only assertion remains unresolved.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction
open Subgroup
variable {G : Type*} [Group G]

/-- A dihedral inner Sylow subgroup supplies the four-group and its noncentral
reflection. The four-group contains the specified central involution. -/
public theorem Setup.exists_four_with_reflection (d : Setup G)
    (hD : Nonempty (d.sk ≃* DihedralGroup 4)) :
    ∃ (E : Subgroup G) (e : G), IsKleinFour E ∧ E ≤ d.sk ∧ d.zK ∈ E ∧
      e ∈ E ∧ e ∉ zpowers d.zK := by
  obtain ⟨j⟩ := hD
  let e := j.symm (DihedralGroup.sr 0)
  have he2 : (e : G) * e = 1 := by
    have hh : e ^ 2 = 1 := by
      apply j.injective
      simp only [map_pow, map_one, e, j.apply_symm_apply]
      decide
    simpa only [pow_two, coe_mul, coe_one] using congrArg Subtype.val hh
  have heout : (e : G) ∉ zpowers d.zK := by
    intro heZ
    have hecenter : e ∈ center d.sk := by
      have hh : (e : G) ∈ (center d.sk).map d.sk.subtype := by
        change (e : G) ∈ (center (d.S ⊓ d.K : Subgroup G)).map (d.S ⊓ d.K).subtype
        rw [d.center_sk]
        exact heZ
      obtain ⟨k, hk, hke⟩ := hh
      exact (show k = e from Subtype.ext hke) ▸ hk
    have hc := congrArg j (mem_center_iff.mp hecenter (j.symm (DihedralGroup.r 1)))
    have hbad : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr 0 =
        DihedralGroup.sr 0 * DihedralGroup.r 1 := by
      simpa only [map_mul, e, j.apply_symm_apply] using hc
    exact (by decide : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1) hbad
  have hz2 : d.zK * d.zK = 1 := by
    have hh : ((MulAut.conj d.x⁻¹) d.t) ^ 2 = 1 := by
      rw [← map_pow, d.t_square, map_one]
    simpa only [MulAut.conj_apply, inv_inv, d.t_conjugate, pow_two] using hh
  have hz1 : d.zK ≠ 1 := by
    intro h
    apply d.t_ne_one
    rw [← d.zK_conjugate, h]
    simp
  have he1 : (e : G) ≠ 1 := fun h => heout (h ▸ (zpowers d.zK).one_mem)
  have hze : d.zK ≠ (e : G) := fun h => heout (h ▸ mem_zpowers d.zK)
  have hzcenter : (⟨d.zK, CoreReduction.zK_mem_sk d⟩ : d.sk) ∈ center d.sk := by
    have hh : d.zK ∈ (center d.sk).map d.sk.subtype := by
      change d.zK ∈ (center (d.S ⊓ d.K : Subgroup G)).map (d.S ⊓ d.K).subtype
      rw [d.center_sk]
      exact mem_zpowers _
    obtain ⟨k, hk, hval⟩ := hh
    exact (show k = ⟨d.zK, CoreReduction.zK_mem_sk d⟩ from Subtype.ext hval) ▸ hk
  have hcomm : Commute d.zK (e : G) :=
    (congrArg Subtype.val (mem_center_iff.mp hzcenter e)).symm
  let E := closure ({d.zK, (e : G)} : Set G)
  refine ⟨E, e, isKleinFour_closure_pair d.zK (e : G) hz2 he2 hz1 he1 hze hcomm,
    ?_, subset_closure (by simp), subset_closure (by simp), heout⟩
  apply (closure_le d.sk).2
  intro a ha
  rcases (show a = d.zK ∨ a = (e : G) from by simpa only
    [Set.mem_insert_iff, Set.mem_singleton_iff] using ha) with rfl | rfl
  · exact CoreReduction.zK_mem_sk d
  · exact e.property

variable [Finite G]

/-- The normalizer order needs the compatible reflection but does not need
square stability. It follows from the completed action-normalizer lift and the
dihedral algebra, so no ambient cardinality is taken as a model premise. -/
public theorem Setup.four_normalizer_card_of_reflection (d : Setup G)
    (r : CoreReduction d) (m : ActionNormalizer.ModelFacts)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK)
    (hc : d.x⁻¹ * e * d.x ∈
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G)) :
    Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G) = 64 := by
  have hgen := ActionNormalizer.normalizer_eq_of_model d r m E hE he heout
  have hdisj := (NormalizerCalculation.factors_disjoint d r E hE he heout).mono
    le_rfl (show d.K ⊓ normalizer (E : Set G) ≤ d.K from inf_le_left)
  have hcomm := NormalizerCalculation.factors_commute d E hc
  obtain ⟨f, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core) (d.K ⊓ normalizer (E : Set G)) hdisj hcomm
  obtain ⟨a⟩ := NormalizerCalculation.conjugate_dihedral d r E hE he heout
  obtain ⟨b⟩ := ActionNormalizer.normalizer_symmetric_of_model d m E hE
  exact NormalizerCalculation.card_base_of_normalizer_model d E hE
    ⟨(MulEquiv.subgroupCongr hgen).trans (f.symm.trans (a.prodCongr b))⟩

private theorem four_normalizer_card (d : Setup G) (r : CoreReduction d)
    (m : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (n : ActionNormalizer.ModelFacts)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) :
    Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G) = 64 := by
  obtain ⟨e, he, heout⟩ := d.four_exists_noncentral E
  obtain ⟨s, hc⟩ := FourGroupChoice.exists_replaceX_centralizing d m E hE he heout
  exact (d.replaceX s).four_normalizer_card_of_reflection
    (CoreReduction.replaceX d r s) n E hE he heout hc

/-- Every inner four-group has the same normalizer inside `S`: the product of
the two commuting dihedral factors. Only concrete finite-model identities are
additional hypotheses; the ambient order is derived. -/
public theorem Setup.four_normalizer_eq_product_of_model (d : Setup G)
    (r : CoreReduction d)
    (m : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (n : ActionNormalizer.ModelFacts)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) :
    d.S ⊓ normalizer (E : Set G) = d.sk ⊔ conjugate d.x d.sk :=
  d.four_normalizer_eq_factor_product d.sk_card E hE
    (four_normalizer_card d r m n E hE)

/-- Choosing a different inner four-group cannot fix square stability: for
every such four-group it is exactly the same factor-product membership. -/
public theorem Setup.square_normalizes_four_iff_product (d : Setup G)
    (r : CoreReduction d)
    (m : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (n : ActionNormalizer.ModelFacts)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) :
    d.x ^ 2 ∈ normalizer (E : Set G) ↔
      d.x ^ 2 ∈ d.sk ⊔ conjugate d.x d.sk := by
  have h : d.x ^ 2 ∈ d.S ⊓ normalizer (E : Set G) ↔
      d.x ^ 2 ∈ d.sk ⊔ conjugate d.x d.sk := by
    rw [d.four_normalizer_eq_product_of_model r m n E hE]
  simpa only [mem_inf, d.square_mem, true_and] using h

/-- Conditional compatible choice, with the four-group, reflection, normalizer
order and change of crossing representative all constructed. The only additional
ambient premise is square membership in `S_K S_Kˣ`, which remains a source
obligation. Every other extra premise concerns the actual finite A₆ model.
`CoreReduction.replaceX` supplies the reduction for the resulting `xs`. -/
public theorem Setup.exists_compatible_four_of_square_product (d : Setup G)
    (r : CoreReduction d)
    (m : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (n : ActionNormalizer.ModelFacts)
    (hsquare : d.x ^ 2 ∈ d.sk ⊔ conjugate d.x d.sk) :
    ∃ (s : d.S) (E : Subgroup G) (e : G),
      IsKleinFour E ∧ E ≤ (d.replaceX s).sk ∧ (d.replaceX s).zK ∈ E ∧
      e ∈ E ∧ e ∉ zpowers (d.replaceX s).zK ∧
      (d.replaceX s).x ^ 2 ∈ normalizer (E : Set G) ∧
      (d.replaceX s).x⁻¹ * e * (d.replaceX s).x ∈
        centralizer (((d.replaceX s).K ⊓ normalizer (E : Set G) : Subgroup G) : Set G) := by
  have hD' := d.sk_dihedral
  obtain ⟨E, e, hfour, hE, hz, he, heout⟩ := d.exists_four_with_reflection hD'
  let : IsKleinFour E := hfour
  have hDcard : Nat.card d.sk = 8 := by
    obtain ⟨f⟩ := hD'
    rw [Nat.card_congr f.toEquiv, DihedralGroup.nat_card]
  obtain ⟨s, hcentral⟩ := FourGroupChoice.exists_replaceX_centralizing d m E hE he heout
  have hUcard : Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G) = 64 :=
    (d.replaceX s).four_normalizer_card_of_reflection (CoreReduction.replaceX d r s) n E hE he heout hcentral
  have hsquareE : d.x ^ 2 ∈ normalizer (E : Set G) := by
    have hU : d.x ^ 2 ∈ d.S ⊓ normalizer (E : Set G) := by
      rw [d.four_normalizer_eq_factor_product hDcard E hE hUcard]
      exact hsquare
    exact hU.2
  exact ⟨s, E, e, hfour, hE, hz, he, heout,
    (d.four_square_replaceX_iff r hDcard E hE hUcard s).mpr hsquareE, hcentral⟩

/-- Exact remaining ambient obligation for a compatible choice, allowing any
permissible representative `xs`. The forward implication shows that neither
changing the four-group nor changing the representative bypasses it. This is
a reduction of the source problem, not a proof of its right-hand side. -/
public theorem Setup.compatible_four_iff_square_product (d : Setup G)
    (r : CoreReduction d)
    (m : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (n : ActionNormalizer.ModelFacts) :
    (∃ (s : d.S) (E : Subgroup G) (e : G),
      IsKleinFour E ∧ E ≤ (d.replaceX s).sk ∧ (d.replaceX s).zK ∈ E ∧
        e ∈ E ∧ e ∉ zpowers (d.replaceX s).zK ∧
        (d.replaceX s).x ^ 2 ∈ normalizer (E : Set G) ∧
        (d.replaceX s).x⁻¹ * e * (d.replaceX s).x ∈
          centralizer (((d.replaceX s).K ⊓ normalizer (E : Set G) :
            Subgroup G) : Set G)) ↔
      d.x ^ 2 ∈ d.sk ⊔ conjugate d.x d.sk := by
  constructor
  · rintro ⟨s, E, e, hfour, hE, _, _, _, hsquare, _⟩
    let : IsKleinFour E := hfour
    have hsq := (d.four_square_replaceX_iff r d.sk_card E hE
      (four_normalizer_card d r m n E hE) s).mp hsquare
    exact (d.square_normalizes_four_iff_product r m n E hE).mp hsq
  · exact d.exists_compatible_four_of_square_product r m n

/-- Construct a square-stable four-group and a compatible conjugate reflection
from the full source centralizer premise in 2.5.22(2) and the explicit A₆ model
identities. Square membership follows from involution nonfusion and is not an
input. The crossing representative may change to `xs`; its setup is preserved
by `Setup.replaceX`, and its reduction is `CoreReduction.replaceX d r s`.
The source assembly owns the centralizer premise and the model identities. -/
public theorem Setup.exists_compatible_four_of_source (d : Setup G)
    (r : CoreReduction d)
    (m : SquareMembership.Fusion.ModelFacts)
    (n : ActionNormalizer.ModelFacts)
    (o : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (hC : centralizer ({d.t} : Set G) ≤ d.H) :
    ∃ (s : d.S) (E : Subgroup G) (e : G),
      IsKleinFour E ∧ E ≤ (d.replaceX s).sk ∧ (d.replaceX s).zK ∈ E ∧
      e ∈ E ∧ e ∉ zpowers (d.replaceX s).zK ∧
      (d.replaceX s).x ^ 2 ∈ normalizer (E : Set G) ∧
      (d.replaceX s).x⁻¹ * e * (d.replaceX s).x ∈
        centralizer (((d.replaceX s).K ⊓ normalizer (E : Set G) : Subgroup G) : Set G) :=
  d.exists_compatible_four_of_square_product r o n
    (SquareMembership.Fusion.square_mem_of_source d r m n o hC)

end CFSG.Quasithin.Chapter2.A6ShadowConstruction
