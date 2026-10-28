module

public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeSection
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeChiefProjection

/-!
# The moved four-space in coordinates on an M22 quintet section

`M22FiveSection` records the literal five-dimensional `B/U` action.  This
bridge transports its moved four-space to any model of that same five-space
whose coordinates intertwine the original action. It does not identify a
chief section with the entire five-space.  The entire quintet remains
five-dimensional; only the commutator (moved) subspace is asserted to have
dimension four. A nonzero equivariant projection defined on that moved
four-space is injective; identifying its image with a chief displacement
then supplies displacement rank four. Chief selection, the projection and
its nonzero image remain source obligations.

Source: Aschbacher--Smith H.16.3(3), 8.2.8(4) and 8.2.9, printed pp.403,718--721,
`refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open MathieuCode.M22Quintet.CocodeTransfer
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows

open ChapterE Offenders.Parabolic.Construction Normalizer.SmallOvergroups

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Equivariant coordinates on the literal five-space preserve its moved
four-space. Normality and elementary abelianness are extracted before the
coordinates are supplied, so the action uses the actual section witnesses. -/
theorem m22_chief_four_space
    {B U R : Subgroup G} (f : R →* MathieuCode.M22Quintet.Q)
    (hsec : M22FiveSection R B U f)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] :
    ∃ hRB : R ≤ normalizer (B : Set G),
      ∃ hRU : R ≤ normalizer (U : Set G),
        ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
          ∃ hEl : IsElementaryAbelian 2 (B ⧸ U.subgroupOf B), letI := hEl
            ∀ (σ : Representation (ZMod 2) R W)
              (eW : W ≃ₗ[ZMod 2] Additive (B ⧸ U.subgroupOf B)),
              (∀ x w, eW (σ x w) =
                Additive.ofMul (sectionAction R B U hRB hRU x (eW w).toMul)) →
              Module.finrank (ZMod 2) W = 5 ∧
                Module.finrank (ZMod 2) (Coinvariants.ker σ) = 4 ∧
                Module.finrank (ZMod 2) (Coinvariants σ) = 1 := by
  rcases hsec with ⟨hRB,hRU,hBU,r,eB,hrsur,hrker,hrval,hact,hkernel,
    ⟨hEl,ρ,hρ,hd5,hd4,hd1⟩⟩
  let := hBU
  let := hEl
  refine ⟨hRB,hRU,hBU,hEl,?_⟩
  intro σ eW hσ
  have hσ' (x : R) (w : W) : eW (σ x w) = ρ x (eW w) := by
    exact (hσ x w).trans (hρ x (eW w).toMul).symm
  have hmap : (Coinvariants.ker σ).map eW.toLinearMap = Coinvariants.ker ρ := by
    apply le_antisymm
    · apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x,w⟩,rfl⟩
      change eW (σ x w - w) ∈ Coinvariants.ker ρ
      rw [map_sub,hσ']
      exact Coinvariants.sub_mem_ker _ _
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨x,v⟩,rfl⟩
      obtain ⟨w,rfl⟩ := eW.surjective v
      refine ⟨σ x w - w, Coinvariants.sub_mem_ker _ _, ?_⟩
      simp only [LinearEquiv.coe_coe, map_sub, hσ']
  have hdW : Module.finrank (ZMod 2) W = 5 := eW.finrank_eq.trans hd5
  have hd4W : Module.finrank (ZMod 2) (Coinvariants.ker σ) = 4 := by
    rw [← LinearEquiv.finrank_map_eq eW,hmap,hd4]
  have hq := (Coinvariants.ker σ).finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) (Coinvariants σ) +
      Module.finrank (ZMod 2) (Coinvariants.ker σ) =
      Module.finrank (ZMod 2) W at hq
  exact ⟨hdW,hd4W,by omega⟩

/-- A nonzero equivariant projection of the literal B/U moved space is
injective. This constructs injectivity from the actual quintet marking;
the projection need not be defined on the whole five-space. -/
theorem m22_chief_projection
    {B U R : Subgroup G} (f : R →* MathieuCode.M22Quintet.Q)
    (hsec : M22FiveSection R B U f)
    (hRB : R ≤ normalizer (B : Set G)) (hRU : R ≤ normalizer (U : Set G))
    [(U.subgroupOf B).Normal] [IsElementaryAbelian 2 (B ⧸ U.subgroupOf B)]
    (σ : Representation (ZMod 2) R (Additive (B ⧸ U.subgroupOf B)))
    (hσ : ∀ x b, σ x (Additive.ofMul b) =
      Additive.ofMul (sectionAction R B U hRB hRU x b))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) R W)
    (c : Coinvariants.ker σ →ₗ[ZMod 2] W)
    (hc : ∀ x (v w : Coinvariants.ker σ),
      (w : Additive (B ⧸ U.subgroupOf B)) = σ x v → c w = τ x (c v))
    (hne : c ≠ 0) :
    Function.Injective c ∧ Module.finrank (ZMod 2) (LinearMap.range c) = 4 := by
  obtain ⟨_,_,_,_,hd⟩ := m22_chief_four_space f hsec
    (W := Additive (B ⧸ U.subgroupOf B))
  obtain ⟨_,_,_,r,eB,hrsur,_,_,hact,_⟩ := hsec
  let e : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K :=
    LinearEquiv.ofBijective (eB.toAdditive.toAddMonoidHom.toZModLinearMap 2) eB.bijective
  have he (x : R) (v : Additive (B ⧸ U.subgroupOf B)) :
      e (σ x v) = MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r x) (e v) := by
    exact (congrArg (fun w => Additive.ofMul (eB w.toMul)) (hσ x v.toMul)).trans (hact x v.toMul)
  have hinj := (MathieuCode.NormalizedShadowRows.M22CodeSection.moved_projection_of_marking
    σ r hrsur e he τ c hc hne).1
  have hfour := (hd σ (LinearEquiv.refl (ZMod 2) _) (fun x w => hσ x w.toMul)).2.1
  exact ⟨hinj,(LinearMap.finrank_range_of_inj hinj).trans hfour⟩

/-- The literal moved-space projection gives displacement rank four once
its image is identified with the displacement. Injectivity is proved from
nonzero equivariance, rather than supplied as a source assumption. -/
theorem m22_chief_displacement_four
    {B U R : Subgroup G} (f : R →* MathieuCode.M22Quintet.Q)
    (hsec : M22FiveSection R B U f)
    (hRB : R ≤ normalizer (B : Set G)) (hRU : R ≤ normalizer (U : Set G))
    [(U.subgroupOf B).Normal] [IsElementaryAbelian 2 (B ⧸ U.subgroupOf B)]
    (σ : Representation (ZMod 2) R (Additive (B ⧸ U.subgroupOf B)))
    (hσ : ∀ x b, σ x (Additive.ofMul b) =
      Additive.ofMul (sectionAction R B U hRB hRU x b))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) R W) (δ : W →ₗ[ZMod 2] W)
    (c : Coinvariants.ker σ →ₗ[ZMod 2] W)
    (hc : ∀ x (v w : Coinvariants.ker σ),
      (w : Additive (B ⧸ U.subgroupOf B)) = σ x v → c w = τ x (c v))
    (hne : c ≠ 0) (himage : LinearMap.range c = LinearMap.range δ) :
    Module.finrank (ZMod 2) (LinearMap.range δ) = 4 :=
  himage ▸ (m22_chief_projection f hsec hRB hRU σ hσ τ c hc hne).2

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
