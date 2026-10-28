module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Extension
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.FusionTypes
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.ActionTypes
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The actual projective quotient of an embedded Sylow center

Conjugate the seed normalizer onto the normalizer of the embedded Z(P),
then compose its literal quotient map with the proved PGL₂(9) equivalence.
The kernel is precisely Z(P), relative to that normalizer. Since it lies
in P, the inverse image of the projective Sylow is P, and the inverse
image of its normalizer is the original normalizer of P.

Restriction therefore identifies P/Φ(P) with the projective Sylow. The
last theorem proves equivariance for the published Frattini action and
these exact restricted maps. No projective normalizer structure or
complement is assumed in this construction.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3(3), printed p.262.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.ProjectiveLift
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

abbrev PG := GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F
abbrev Z (P : Sylow 3 G) := (center P).map (P : Subgroup G).subtype
abbrev L (P : Sylow 3 G) := normalizer (Z P : Set G)

omit [Finite G] in
theorem normalizer_le_L (P : Sylow 3 G) : normalizer (P : Set G) ≤ L P :=
  normalizer_le_normalizer_characteristic_image (P : Subgroup G) (center P)

omit [Finite G] in
theorem le_L (P : Sylow 3 G) : (P : Subgroup G) ≤ L P :=
  (P : Subgroup G).le_normalizer.trans (normalizer_le_L P)

structure Coordinates (P : Sylow 3 G) where
  projection : L P →* PG
  surjective : Function.Surjective projection
  kernel : projection.ker = (Z P).subgroupOf (L P)

theorem coordinates (H : CentralizerCalculation D) (P : Sylow 3 G)
    (hV : Z P ∈ MulAction.orbit (ConjAct G) D.X) : Nonempty (Coordinates P) := by
  obtain ⟨g, hg⟩ := hV
  let a := MulAut.conj (ConjAct.ofConjAct g)
  change D.X.map a.toMonoidHom = Z P at hg
  have hM : (M D).map a.toMonoidHom = L P := by
    rw [map_equiv_normalizer_eq, hg]
  let e : M D ≃* L P := (a.subgroupMap (M D)).trans (MulEquiv.subgroupCongr hM)
  let f : L P →* PG := H.normalizerQuotientEquiv.toMonoidHom.comp
    ((QuotientGroup.mk' (XM D)).comp e.symm.toMonoidHom)
  refine ⟨⟨f, H.normalizerQuotientEquiv.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective), ?_⟩⟩
  ext x
  change H.normalizerQuotientEquiv (QuotientGroup.mk' (XM D) (e.symm x)) = 1 ↔
    (x : G) ∈ Z P
  rw [MulEquiv.map_eq_one_iff]
  change (QuotientGroup.mk (e.symm x) : M D ⧸ XM D) = 1 ↔ (x : G) ∈ Z P
  rw [QuotientGroup.eq_one_iff, ← hg, mem_map_equiv]
  rfl

namespace Coordinates
variable {P : Sylow 3 G} (c : Coordinates P)
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable def imageSylow : Sylow 3 PG :=
  (P.subtype (le_L P)).mapSurjective c.surjective

omit [Finite G] in
theorem kernel_le : c.projection.ker ≤ (P : Subgroup G).subgroupOf (L P) := by
  rw [c.kernel]
  intro x hx
  exact map_subtype_le (center P) hx

theorem image_comap : (c.imageSylow : Subgroup PG).comap c.projection =
    (P : Subgroup G).subgroupOf (L P) :=
  comap_map_eq_self c.kernel_le

theorem normalizer_comap : (normalizer (c.imageSylow : Set PG)).comap c.projection =
    (normalizer (P : Set G)).subgroupOf (L P) := by
  change (normalizer (c.imageSylow : Subgroup PG)).comap c.projection = _
  rw [comap_normalizer_eq_of_surjective _ c.surjective, c.image_comap,
    ← subgroupOf_normalizer_eq (le_L P)]
  rfl

noncomputable def onSylow : P →* c.imageSylow :=
  ((c.projection.comp (inclusion (le_L P))).codRestrict (c.imageSylow : Subgroup PG)
    (fun x => mem_map_of_mem c.projection x.property))

theorem onSylow_surjective : Function.Surjective c.onSylow := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem onSylow_ker : c.onSylow.ker = center P := by
  ext x
  change c.onSylow x = 1 ↔ x ∈ center P
  rw [Subtype.ext_iff]
  change c.projection (inclusion (le_L P) x) = 1 ↔ _
  change (inclusion (le_L P) x) ∈ c.projection.ker ↔ _
  rw [c.kernel]
  change (x : G) ∈ (center P).map (P : Subgroup G).subtype ↔ _
  exact mem_map_iff_mem (P : Subgroup G).subtype_injective

noncomputable def onNormalizer : normalizer (P : Set G) →*
    normalizer (c.imageSylow : Set PG) :=
  (c.projection.comp (inclusion (normalizer_le_L P))).codRestrict _
    (fun x => c.normalizer_comap.ge x.property)

theorem onNormalizer_surjective : Function.Surjective c.onNormalizer := by
  intro b
  obtain ⟨x, hx⟩ := c.surjective b
  have hn : (x : G) ∈ normalizer (P : Set G) :=
    c.normalizer_comap.le (show c.projection x ∈ normalizer (c.imageSylow : Set PG)
      from hx.symm ▸ b.property)
  exact ⟨⟨x, hn⟩, Subtype.ext hx⟩

theorem onNormalizer_ker : c.onNormalizer.ker =
    (Z P).subgroupOf (normalizer (P : Set G)) := by
  ext x
  change c.onNormalizer x = 1 ↔ (x : G) ∈ Z P
  rw [Subtype.ext_iff]
  change (inclusion (normalizer_le_L P) x) ∈ c.projection.ker ↔ _
  rw [c.kernel]
  rfl

theorem onNormalizer_comap :
    ((c.imageSylow : Subgroup PG).subgroupOf (normalizer (c.imageSylow : Set PG))).comap
      c.onNormalizer = (P : Subgroup G).subgroupOf (normalizer (P : Set G)) := by
  ext x
  change c.projection (inclusion (normalizer_le_L P) x) ∈ (c.imageSylow : Subgroup PG) ↔
    (x : G) ∈ (P : Subgroup G)
  change (inclusion (normalizer_le_L P) x) ∈
    (c.imageSylow : Subgroup PG).comap c.projection ↔ _
  rw [c.image_comap]
  rfl

theorem onSylow_conjugation (b : normalizer (P : Set G)) (x : P) :
    c.onSylow ((P : Subgroup G).normalizerMonoidHom b x) =
      (c.imageSylow : Subgroup PG).normalizerMonoidHom (c.onNormalizer b) (c.onSylow x) := by
  apply Subtype.ext
  change c.projection ((inclusion (normalizer_le_L P) b) *
    inclusion (le_L P) x * (inclusion (normalizer_le_L P) b)⁻¹) = _
  simp only [map_mul, map_inv]
  rfl

noncomputable def frattiniEquiv (hP : IsExtraspecial 3 P) :
    (P ⧸ frattini P) ≃* c.imageSylow := by
  let := hP
  exact (QuotientGroup.quotientMulEquivOfEq
    ((IsExtraspecial.frattini_eq_center (p := 3)).trans c.onSylow_ker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective c.onSylow c.onSylow_surjective)

theorem frattiniEquiv_mk (hP : IsExtraspecial 3 P) (x : P) :
    c.frattiniEquiv hP (QuotientGroup.mk' (frattini P) x) = c.onSylow x := rfl

theorem frattiniEquiv_conjugation (hP : IsExtraspecial 3 P)
    (b : normalizer (P : Set G)) (x : P ⧸ frattini P) :
    c.frattiniEquiv hP (sylowFrattiniAction P b x) =
      (c.imageSylow : Subgroup PG).normalizerMonoidHom (c.onNormalizer b)
        (c.frattiniEquiv hP x) := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    change c.frattiniEquiv hP (sylowFrattiniAction P b (QuotientGroup.mk' (frattini P) x)) =
      (c.imageSylow : Subgroup PG).normalizerMonoidHom (c.onNormalizer b)
        (c.frattiniEquiv hP (QuotientGroup.mk' (frattini P) x))
    rw [sylowFrattiniAction_apply_mk, c.frattiniEquiv_mk, c.frattiniEquiv_mk]
    exact c.onSylow_conjugation b x

end Coordinates
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.ProjectiveLift
