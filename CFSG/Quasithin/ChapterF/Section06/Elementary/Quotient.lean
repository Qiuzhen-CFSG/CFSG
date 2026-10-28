module

public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.Amalgam.RankTwoQuotientTransport

/-!
# Goldschmidt triples modulo their two-core

A surjection with two-group kernel inside the common Sylow subgroup preserves
the two local symmetric-three quotients and the whole overlap. Apply this to
`G → G/O₂(G)`: the new two-core is trivial, so its subgroup amalgam is a
Goldschmidt amalgam. The first isomorphism theorem identifies all three
intrinsic quotients with their images, with both inclusion squares commuting.
The representative formulas retain the actual ambient quotient map.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.5(1), printed p.305 (1 March 2004 manuscript).
-/

open Subgroup
open Theory.GroupTheory

namespace CFSG.Quasithin.ChapterF
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

private noncomputable def quotientTwoCoreEquivOfSurjective
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    (G ⧸ pCore 2 G) ≃* (H ⧸ pCore 2 H) := by
  let q := (QuotientGroup.mk' (pCore 2 H)).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have he : q.ker = pCore 2 G := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup hf hk
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

public theorem IsGoldschmidtTriple.map_of_two_kernel {G₁ G₂ : Subgroup G}
    (h : IsGoldschmidtTriple G₁ G₂)
    (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hker : f.ker ≤ G₁ ⊓ G₂) :
    IsGoldschmidtTriple (G₁.map f) (G₂.map f) := by
  have hlocal (M : Subgroup G)
      (e : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 3))) :
      Nonempty (((M.map f) ⧸ pCore 2 (M.map f)) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨e⟩ := e
    have hm : IsPGroup 2 (f.subgroupMap M).ker := by
      rw [Subgroup.ker_subgroupMap]
      exact hk.comap_subtype
    exact ⟨(quotientTwoCoreEquivOfSurjective (f.subgroupMap M)
      (f.subgroupMap_surjective M) hm).symm.trans e⟩
  refine ⟨?_, hlocal G₁ h.quotient_left, hlocal G₂ h.quotient_right, ?_⟩
  · rw [← Subgroup.map_sup, h.generated, map_top_of_surjective f hf]
  · obtain ⟨T, hT⟩ := h.intersection_sylow
    refine ⟨T.mapSurjective hf, ?_⟩
    change G₁.map f ⊓ G₂.map f = (T : Subgroup G).map f
    rw [← RankTwoAmalgam.map_overlap_of_ker_le f G₁ G₂ (hker.trans inf_le_right), hT]

public theorem IsGoldschmidtTriple.quotient_twoCore {G₁ G₂ : Subgroup G}
    (h : IsGoldschmidtTriple G₁ G₂) :
    IsGoldschmidtTriple (G₁.map (QuotientGroup.mk' (pCore 2 G)))
      (G₂.map (QuotientGroup.mk' (pCore 2 G))) := by
  apply h.map_of_two_kernel (QuotientGroup.mk' (pCore 2 G))
    (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  · rw [QuotientGroup.ker_mk']; exact h.twoCore_isGreatest.1.1

public theorem IsGoldschmidtTriple.quotient_twoCore_eq_bot {G₁ G₂ : Subgroup G}
    (_h : IsGoldschmidtTriple G₁ G₂) : pCore 2 (G ⧸ pCore 2 G) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := congrArg (Subgroup.map q) (q.comap_pCore_of_ker_isPGroup hs hk)
  rw [map_comap_eq_self_of_surjective hs] at he
  exact he.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))

public theorem IsGoldschmidtTriple.quotient_twoCore_intersection {G₁ G₂ : Subgroup G}
    (h : IsGoldschmidtTriple G₁ G₂) :
    (G₁ ⊓ G₂).map (QuotientGroup.mk' (pCore 2 G)) =
      G₁.map (QuotientGroup.mk' (pCore 2 G)) ⊓
        G₂.map (QuotientGroup.mk' (pCore 2 G)) := by
  apply RankTwoAmalgam.map_overlap_of_ker_le
  rw [QuotientGroup.ker_mk']
  exact h.twoCore_isGreatest.1.1.trans inf_le_right

public noncomputable def IsGoldschmidtTriple.quotientTwoCoreAmalgamIso {G₁ G₂ : Subgroup G}
    (_h : IsGoldschmidtTriple G₁ G₂) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroupQuotients (QuotientGroup.mk' (pCore 2 G))
        G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups
        (G₁.map (QuotientGroup.mk' (pCore 2 G)))
        ((G₁ ⊓ G₂).map (QuotientGroup.mk' (pCore 2 G)))
        (G₂.map (QuotientGroup.mk' (pCore 2 G)))
        (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)) :=
  RankTwoAmalgam.ofSubgroupQuotientsMapIso _ _ _ _ _ _

public theorem IsGoldschmidtTriple.quotientTwoCoreAmalgamIso_left_mk {G₁ G₂ : Subgroup G}
    (h : IsGoldschmidtTriple G₁ G₂) (g : G₁) :
    h.quotientTwoCoreAmalgamIso.left (QuotientGroup.mk' _ g) =
      (QuotientGroup.mk' (pCore 2 G)).subgroupMap G₁ g := by rfl

public theorem IsGoldschmidtTriple.quotientTwoCoreAmalgamIso_middle_mk {G₁ G₂ : Subgroup G}
    (h : IsGoldschmidtTriple G₁ G₂) (g : (G₁ ⊓ G₂ : Subgroup G)) :
    h.quotientTwoCoreAmalgamIso.middle (QuotientGroup.mk' _ g) =
      (QuotientGroup.mk' (pCore 2 G)).subgroupMap (G₁ ⊓ G₂) g := by rfl

public theorem IsGoldschmidtTriple.quotientTwoCoreAmalgamIso_right_mk {G₁ G₂ : Subgroup G}
    (h : IsGoldschmidtTriple G₁ G₂) (g : G₂) :
    h.quotientTwoCoreAmalgamIso.right (QuotientGroup.mk' _ g) =
      (QuotientGroup.mk' (pCore 2 G)).subgroupMap G₂ g := by rfl

end CFSG.Quasithin.ChapterF
