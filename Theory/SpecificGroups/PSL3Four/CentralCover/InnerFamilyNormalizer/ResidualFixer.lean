module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer
public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphField
public import Theory.GroupAction.CentralKernelFixedResidual

/-!
# The marked residual and its pointwise fixer

The diagonal and cycle generators of the concrete Sylow E₉ lie in the
actual graph-field fixed two-residual. Its order-nine identification
therefore fixes its embedding, not only its abstract isomorphism type.
A compatible perfect central cover with two-group kernel maps its fixed
two-residual onto this subgroup; an E₉ residual projects injectively.

The standard projective fixer calculation then lifts through faithful
central descent to C_{N_G(L)}(D) ≤ C_G(L)D⟨r⟩. Coverage of the full
projective pointwise fixer by standard automorphisms remains explicit.
The argument makes no assumption that the cover has center E₄ and hence
also applies to the center-C₂ cover in Chapter 16.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(5) and the graph-field branch of 16.4.9(2), pp.1171, 1191–1192.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Four.InnerFamilyNormalizer
open ExtendedCentralizer.ProjectiveFixer

/-- The displayed cubic generators belong to the actual fixed two-residual. -/
theorem model_le_projectiveResidual : model ≤ projectiveGraphFieldResidual := by
  have hm (x : PSL) (hx : x ∈ graphField.fixedSubgroup) (h3 : x ^ 3 = 1) :
      x ∈ projectiveGraphFieldResidual := by
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply mem_pResidual_of_orderOf_coprime
    exact Nat.Coprime.of_dvd_right
      (orderOf_dvd_of_pow_eq_one (show (⟨x, hx⟩ : graphField.fixedSubgroup) ^ 3 = 1 from
        Subtype.ext h3)) (by decide : Nat.Coprime 2 3)
  rw [model_eq]
  apply sup_le
  · rintro x ⟨u, rfl⟩
    exact hm _ (graphField_fixes_model (diagonal_mem_model u)) (by
      rw [← map_pow, unit_cube, map_one])
  · exact zpowers_le.mpr (hm _ (graphField_fixes_model cycle_mem_model) cycle_cube)

/-- Order nine identifies the subgroup, with the actual embedding retained. -/
theorem projectiveResidual_eq_model (h9 : Nat.card projectiveGraphFieldResidual = 9) :
    projectiveGraphFieldResidual = model := by
  exact (eq_of_le_of_card_ge model_le_projectiveResidual (by rw [h9, model_card])).symm

variable {X : Type*} [Group X]

/-- A three-subgroup embeds through a homomorphism with two-group kernel. -/
theorem projection_injective (f : X →* PSL) (hp : IsPGroup 2 f.ker)
    (D : Subgroup X) (hD : IsPGroup 3 D) :
    Function.Injective (f.comp D.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  apply Subtype.ext
  exact disjoint_def.mp (hD.disjoint_of_coprime hp (by decide)) x.property hx

variable [Finite X]

/-- The residual projection and its E₉ size identify the marked matrix subgroup;
no four-cover or abstract replacement of the residual is used. -/
theorem residual_image_eq_model (c : PerfectCentralCovering.Cover X PSL)
    (hp : IsPGroup 2 c.toMonoidHom.ker) (a : MulAut X)
    (ha : ∀ x, c.toMonoidHom (a x) = graphField (c.toMonoidHom x))
    (hD : IsPGroup 3 ((pResidual 2 a.fixedSubgroup).map a.fixedSubgroup.subtype))
    (h9 : Nat.card ((pResidual 2 a.fixedSubgroup).map a.fixedSubgroup.subtype) = 9) :
    ((pResidual 2 a.fixedSubgroup).map a.fixedSubgroup.subtype).map c.toMonoidHom = model := by
  let D := (pResidual 2 a.fixedSubgroup).map a.fixedSubgroup.subtype
  have hm : D.map c.toMonoidHom = projectiveGraphFieldResidual :=
    MulAut.map_embedded_fixedResidual_of_central_pgroup_ker 2 a graphField
      c.toMonoidHom c.surjective c.ker_le_center hp ha
  have hc : Nat.card (D.map c.toMonoidHom) = 9 := by
    have hi := projection_injective c.toMonoidHom hp D hD
    have he : (c.toMonoidHom.comp D.subtype).range = D.map c.toMonoidHom := by
      rw [MonoidHom.range_comp, D.range_subtype]
    rw [← he, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    exact h9
  rw [hm]
  exact projectiveResidual_eq_model (hm ▸ hc)

/-- Lift the computed standard projective fixer to an ambient component normalizer.
The pointwise-fixer coverage hypothesis is explicit and must be proved by the caller. -/
theorem residual_fixer_bound {G : Type*} [Group G] (L D : Subgroup G)
    (c : PerfectCentralCovering.Cover L PSL) (hk : c.toMonoidHom.ker = center L)
    (hmark : (D.subgroupOf L).map c.toMonoidHom = model)
    (r : normalizer (L : Set G))
    (hr : c.autMap hk (L.normalizerMonoidHom r) = graphField)
    (hstandard : fixingSubgroup (MulAut PSL) (model : Set PSL) ≤
      PSL3.OuterSolvable.standard F) :
    normalizer (L : Set G) ⊓ centralizer (D : Set G) ≤
      (centralizer (L : Set G) ⊔ D) ⊔ zpowers (r : G) := by
  intro n hn
  let nN : normalizer (L : Set G) := ⟨n, hn.1⟩
  have hnfix0 : c.autMap hk (L.normalizerMonoidHom nN) ∈
      fixingSubgroup (MulAut PSL) (model : Set PSL) := by
    intro y
    obtain ⟨x, hx, he⟩ := (show (y : PSL) ∈ (D.subgroupOf L).map c.toMonoidHom from hmark.symm ▸ y.property)
    change c.autMap hk (L.normalizerMonoidHom nN) (y : PSL) = y
    rw [← he, c.autMap_apply]
    apply congrArg c.toMonoidHom
    apply Subtype.ext
    change n * (x : G) * n⁻¹ = x
    rw [← hn.2 x hx, mul_inv_cancel_right]
  have hnfix : c.autMap hk (L.normalizerMonoidHom nN) ∈ fixer model :=
    ⟨hstandard hnfix0, hnfix0⟩
  rw [model_fixer_eq_candidate] at hnfix
  obtain ⟨⟨y, t⟩, hny⟩ := hnfix
  obtain ⟨d, hd, hdy⟩ := (show (y : PSL) ∈ (D.subgroupOf L).map c.toMonoidHom from hmark.symm ▸ y.property)
  let dN : normalizer (L : Set G) := ⟨d, L.le_normalizer d.property⟩
  have hdaut : c.autMap hk (L.normalizerMonoidHom dN) = MulAut.conj (y : PSL) := by
    ext x
    obtain ⟨u, rfl⟩ := c.surjective x
    rw [c.autMap_apply]
    change c.toMonoidHom (d * u * d⁻¹) = (y : PSL) * c.toMonoidHom u * (y : PSL)⁻¹
    rw [map_mul, map_mul, map_inv, hdy]
  have hnaut : L.normalizerMonoidHom nN =
      L.normalizerMonoidHom (dN * r ^ t.toAdd.val) := by
    apply c.autMap_injective hk
    rw [map_mul, map_pow, map_mul, map_pow, hdaut, hr]
    exact hny.symm
  have hker : nN * (dN * r ^ t.toAdd.val)⁻¹ ∈ L.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnaut, mul_inv_cancel]
  rw [L.normalizerMonoidHom_ker] at hker
  let B := (centralizer (L : Set G) ⊔ D) ⊔ zpowers (r : G)
  have hfirst : (nN * (dN * r ^ t.toAdd.val)⁻¹ : normalizer (L : Set G)).val ∈ B :=
    mem_sup_left (mem_sup_left hker)
  have hsecond : (dN * r ^ t.toAdd.val : normalizer (L : Set G)).val ∈ B :=
    B.mul_mem (mem_sup_left (mem_sup_right hd)) (mem_sup_right (npow_mem_zpowers _ _))
  have he := B.mul_mem hfirst hsecond
  change n * ((d : G) * (r : G) ^ t.toAdd.val)⁻¹ *
    ((d : G) * (r : G) ^ t.toAdd.val) ∈ B at he
  simpa only [inv_mul_cancel_right] using he

end Matrix.PSL3Four.InnerFamilyNormalizer
