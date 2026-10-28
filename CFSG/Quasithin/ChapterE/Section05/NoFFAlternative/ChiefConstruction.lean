module

public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.Defs
public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.Rank
public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.Sections
public import Stellmacher.SectionThree.ResidualActiveChiefSection
public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# Constructing the active chief section in E.5.4

If O²(G) moves a normal elementary abelian subgroup E, select a literal
G-chief section B/D of E on which it acts nontrivially. Irreducibility forces
O₂(G) into this action's kernel. Conjugation on Additive E is the canonical
binary representation; the invariant subspaces from D and B have a quotient
with exactly the same kernel as the group quotient B/D.

Fixed vectors in E are precisely C_E(A), so their codimension is the logarithm
of the relative centralizer index. The sharp displacement bound descends to
the section. When the image of O²(G) is F*(G/O₂(G)), the faithful-section
construction produces a forbidden FF-module for an actual quotient G/X with
O₂(G) ≤ X ≤ O∞(G). Thus O²(G) centralizes E.

This is the conditional chief-section step, not the unrestricted source
lemma: the residual-image equality remains an explicit premise for the
source-theorem assembly owner to discharge.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.5.4,
printed p.244 (PDF p.255).
-/

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterE.NoFFAlternative.ChiefConstruction
universe u
variable {G : Type u} [Group G] [Finite G]
/-- Ambient conjugation, linearized over the canonical binary module. -/
private noncomputable def conjugationRepresentation (E : Subgroup G) [E.Normal]
    [IsElementaryAbelian 2 E] : Representation (ZMod 2) G (Additive E) :=
  (Representation.ofElementaryAbelianAction (A := MulAut E) (G := E) (p := 2)).comp
    MulAut.conjNormal

/-- The invariant subspace cut out by an ambient normal subgroup. -/
private noncomputable def invariantSubspace (E : Subgroup G) [E.Normal] [IsElementaryAbelian 2 E]
    (D : Subgroup G) [D.Normal] : Subrepresentation (conjugationRepresentation E) where
  toSubmodule := AddSubgroup.toZModSubmodule 2 (D.subgroupOf E).toAddSubgroup
  apply_mem_toSubmodule g := fun {v} hv => (inferInstance : D.Normal).conj_mem v.toMul hv g

private theorem twoResidualSubgroup_eq (P : Subgroup G) :
    Stellmacher.twoResidualSubgroup P = pResidual 2 P := by
  unfold Stellmacher.twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hN, hn⟩
    exact ⟨hN, IsPGroup.iff_card.mpr (by simpa only [index_eq_card] using hn)⟩
  · rintro ⟨hN, hn⟩
    exact ⟨hN, by simpa only [index_eq_card] using hn.exists_card_eq⟩

private theorem twoResidualAmbient_top :
    Stellmacher.twoResidualAmbient (⊤ : Subgroup G) = pResidual 2 G := by
  rw [Stellmacher.twoResidualAmbient, twoResidualSubgroup_eq]
  exact map_pResidual 2 Subgroup.topEquiv

omit [Finite G] in
private theorem mem_fixedSpace (E : Subgroup G) [E.Normal] [IsElementaryAbelian 2 E]
    (A : Subgroup G) (v : Additive E) :
    v ∈ fixedSpace (conjugationRepresentation E) A ↔
      (v.toMul : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hv a ha
    have h := congrArg (fun v : Additive E => (v.toMul : G)) (hv ⟨a, ha⟩)
    change a * (v.toMul : G) * a⁻¹ = (v.toMul : G) at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · intro hv a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a : G) * (v.toMul : G) * (a : G)⁻¹ = (v.toMul : G)
    rw [hv a a.property, mul_inv_cancel_right]

private noncomputable def fixedSpaceEquiv (E : Subgroup G) [E.Normal]
    [IsElementaryAbelian 2 E] (A : Subgroup G) :
    fixedSpace (conjugationRepresentation E) A ≃
      (E ⊓ centralizer (A : Set G) : Subgroup G) where
  toFun v := ⟨v.val.toMul, v.val.toMul.property, (mem_fixedSpace E A v.val).mp v.property⟩
  invFun v := ⟨Additive.ofMul ⟨v, v.property.1⟩, (mem_fixedSpace E A _).mpr v.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The linear codimension equals the source relative-centralizer rank. -/
private theorem fixedCodim_eq_log_relIndex (E : Subgroup G) [E.Normal]
    [IsElementaryAbelian 2 E] (A : Subgroup G) :
    fixedCodim (conjugationRepresentation E) A =
      Nat.log 2 ((E ⊓ centralizer (A : Set G)).relIndex E) := by
  have hE : Nat.card E = 2 ^ Module.finrank (ZMod 2) (Additive E) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at h
    simpa only [Nat.card_zmod] using h
  have hC : Nat.card ↥(E ⊓ centralizer (A : Set G)) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace (conjugationRepresentation E) A) := by
    rw [← Nat.card_congr (fixedSpaceEquiv E A)]
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := fixedSpace (conjugationRepresentation E) A))
  rw [← log_card_sub_log_card_eq_log_relIndex E _ inf_le_left, hE, hC,
    Nat.log_pow Nat.one_lt_two, Nat.log_pow Nat.one_lt_two]
  have hd := fixedCodim_add_finrank (conjugationRepresentation E) A
  omega

omit [Finite G] in
private theorem section_kernel_iff (E D B : Subgroup G)
    [E.Normal] [D.Normal] [B.Normal] [IsElementaryAbelian 2 E]
    (hBE : B ≤ E) (g : G) :
    g ∈ (actionHom (sectionRepresentation (conjugationRepresentation E)
      (invariantSubspace E D) (invariantSubspace E B))).ker ↔
      ∀ b ∈ B, g * b * g⁻¹ / b ∈ D := by
  rw [MonoidHom.mem_ker, actionHom_eq_one_iff, sectionRepresentation_trivial_iff]
  constructor
  · intro h b hb
    exact h (Additive.ofMul ⟨b, hBE hb⟩) hb
  · intro h w hw
    exact h w.toMul hw

omit [Finite G] in
private theorem quotient_kernel_iff (B D : Subgroup G) [D.Normal]
    (hn : (⊤ : Subgroup G) ≤ normalizer (B : Set G))
    (f : (⊤ : Subgroup G) →* MulAut (B ⧸ D.subgroupOf B))
    (hf : ∀ p : (⊤ : Subgroup G), ∀ b : B,
      f p (QuotientGroup.mk' (D.subgroupOf B) b) =
        QuotientGroup.mk' (D.subgroupOf B)
          ⟨(p : G) * (b : G) * (p : G)⁻¹,
            (mem_normalizer_iff.mp (hn p.property) b).mp b.property⟩)
    (g : G) :
    f ⟨g, mem_top g⟩ = 1 ↔ ∀ b ∈ B, g * b * g⁻¹ / b ∈ D := by
  constructor
  · intro hg b hb
    have he := hf ⟨g, mem_top g⟩ ⟨b, hb⟩
    rw [hg] at he
    have hm := (QuotientGroup.eq_iff_div_mem (N := D.subgroupOf B)).mp he.symm
    exact hm
  · intro hg
    apply MulEquiv.ext
    intro w
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf B) w
    rw [hf]
    exact QuotientGroup.eq_iff_div_mem.mpr (hg b b.property)

/-- Construct the section and prove its kernel bounds by chief irreducibility. -/
private theorem exists_active_section (E : Subgroup G) [E.Normal] [IsElementaryAbelian 2 E]
    (hmove : ¬ pResidual 2 G ≤ centralizer (E : Set G)) :
    ∃ U W : Subrepresentation (conjugationRepresentation E), U ≤ W ∧
      pCore 2 G ≤ (actionHom (sectionRepresentation (conjugationRepresentation E) U W)).ker ∧
      ¬ pResidual 2 G ≤ (actionHom (sectionRepresentation (conjugationRepresentation E) U W)).ker := by
  have hres : ⁅Stellmacher.twoResidualAmbient (⊤ : Subgroup G), E⁆ ≠ ⊥ := by
    rw [twoResidualAmbient_top]
    exact fun he => hmove (Subgroup.commutator_eq_bot_iff_le_centralizer.mp he)
  obtain ⟨B, D, hBE, hDB, hB, hD, hN, f, hf, hEl, hirr, hactive⟩ :=
    Stellmacher.SectionThree.exists_residual_active_chief_section (⊤ : Subgroup G) E
      le_top inferInstance inferInstance hres
  let : B.Normal := normalizer_eq_top_iff.mp (top_unique hB)
  let : D.Normal := normalizer_eq_top_iff.mp (top_unique hD)
  let : (D.subgroupOf B).Normal := hN
  let : IsElementaryAbelian 2 (B ⧸ D.subgroupOf B) := hEl
  let : Nontrivial (B ⧸ D.subgroupOf B) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    let := hs
    apply hactive
    intro g _
    apply MulEquiv.ext
    intro w
    exact Subsingleton.elim _ _
  let fG : G →* MulAut (B ⧸ D.subgroupOf B) := f.comp Subgroup.topEquiv.symm.toMonoidHom
  have hcore : pCore 2 G ≤ fG.ker := by
    apply irreducible_range_core_le_ker fG
    intro K hK
    apply hirr K
    intro p w hw
    exact hK ⟨fG p, ⟨p, rfl⟩⟩ w hw
  have hk (g : G) :
      g ∈ (actionHom (sectionRepresentation (conjugationRepresentation E)
        (invariantSubspace E D) (invariantSubspace E B))).ker ↔ g ∈ fG.ker := by
    rw [section_kernel_iff E D B hBE]
    exact (quotient_kernel_iff B D hB f hf g).symm
  refine ⟨invariantSubspace E D, invariantSubspace E B, ?_, ?_, ?_⟩
  · intro v hv
    exact hDB hv
  · intro g hg
    exact (hk g).mpr (hcore hg)
  · intro h
    apply hactive
    intro g hg
    have hgR : (g : G) ∈ pResidual 2 G := by
      rw [← twoResidualAmbient_top]
      exact mem_map_of_mem (⊤ : Subgroup G).subtype hg
    exact (hk g).mp (h hgR)

end CFSG.Quasithin.ChapterE.NoFFAlternative.ChiefConstruction

namespace CFSG.Quasithin.ChapterE.NoFFAlternative
open ChiefConstruction
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem core_quotient_eq_bot : pCore 2 (G ⧸ pCore 2 G) = ⊥ := by
  let Q := pCore 2 G
  let π := QuotientGroup.mk' Q
  have hk : IsPGroup 2 π.ker := by
    change IsPGroup 2 (QuotientGroup.mk' Q).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hn : IsPGroup 2 ((pCore 2 (G ⧸ Q)).comap π) :=
    pCore_isPGroup.comap_of_ker_isPGroup π hk
  have hle : (pCore 2 (G ⧸ Q)).comap π ≤ Q := le_sSup ⟨inferInstance, hn⟩
  apply bot_unique
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q x
  exact (QuotientGroup.eq_one_iff g).mpr (hle hx)

/-- The chief-section contradiction of E.5.4, conditional on the exact
residual-image equality. The action, chief section and offender are all
constructed from E and A; none is assumed. -/
public theorem residual_centralizes_of_noFF
    (hL : IsQuasisimple (generalizedFitting (G ⧸ pCore 2 G)))
    (hno : HasNoFFQuotients G)
    (himage : (pResidual 2 G).map (QuotientGroup.mk' (pCore 2 G)) =
      generalizedFitting (G ⧸ pCore 2 G))
    (E : Subgroup G) [E.Normal] [IsElementaryAbelian 2 E]
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hne : ¬ A ≤ pCore 2 G)
    (hdisp : Nat.log 2 ((E ⊓ centralizer (A : Set G)).relIndex E) ≤
      Nat.log 2 (Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))))) :
    pResidual 2 G ≤ centralizer (E : Set G) := by
  by_contra hmove
  obtain ⟨U, W, _, hQ, hactive⟩ := exists_active_section E hmove
  have hm : ¬ (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤
        (actionHom (sectionRepresentation (conjugationRepresentation E) U W)).ker := by
    intro h
    apply hactive
    intro g hg
    apply h
    change QuotientGroup.mk' (pCore 2 G) g ∈ generalizedFitting (G ⧸ pCore 2 G)
    rw [← himage]
    exact mem_map_of_mem _ hg
  have hd : fixedCodim (conjugationRepresentation E) A ≤
      rank (A.map (QuotientGroup.mk' (pCore 2 G))) := by
    rw [fixedCodim_eq_log_relIndex]
    exact hdisp
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  obtain ⟨hQX, hXR, hfaith, hFF⟩ := faithful_ff_quotient_of_section (pCore 2 G)
    core_quotient_eq_bot hL (conjugationRepresentation E) U W hQ hm A hne hd
  exact hno _ inferInstance hQX hXR _
    (faithfulQuotient (sectionRepresentation (conjugationRepresentation E) U W)) hfaith hFF

end CFSG.Quasithin.ChapterE.NoFFAlternative
