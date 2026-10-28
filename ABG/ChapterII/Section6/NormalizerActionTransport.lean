module

public import ABG.ChapterII.Section6.Defs

/-!
# Isomorphism transport of the normalizer-action p-core bound

An ambient group isomorphism carries the normalizer and centralizer of `P` to
those of its image. It therefore induces an isomorphism between the exact ABG
faithful action quotients `N(P)/C(P)`. The quotient image of every subgroup `A`
normalizing `P` maps to the quotient image of its ambient image. Since `pCore`
is invariant under isomorphism, containment of either action image in its
`p`-core is equivalent to containment of the other.

This supplies the action-bound transport used in the Sylow comparison of
ordinary and relative stability in Alperin--Brauer--Gorenstein, Chapter II,
Section 6, article p. 55 (`refs/latex/alperin-brauer-gorenstein-pages/page-056.tex`).
The source applies it to inner automorphisms. The transport itself requires
neither finiteness nor primality; only both actor-normalizer containments are
explicit parameters. The proof first restricts the isomorphism to normalizers,
identifies the centralizer subgroups, and applies `QuotientGroup.congr`. The
commuting square with the quotient projections then identifies the actor
images, and `pCore_map_iso` completes the argument.
-/

namespace ABG

variable {G H : Type*} [Group G] [Group H]

private def normalizerMapEquiv (e : G ≃* H) (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≃*
      Subgroup.normalizer (P.map e.toMonoidHom : Set H) :=
  (e.subgroupMap (Subgroup.normalizer (P : Set G))).trans
    (MulEquiv.subgroupCongr (P.map_equiv_normalizer_eq e))

private theorem subgroupOf_map_normalizerMapEquiv (e : G ≃* H) (P A : Subgroup G) :
    (A.subgroupOf (Subgroup.normalizer (P : Set G))).map
        (normalizerMapEquiv e P).toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf
        (Subgroup.normalizer (P.map e.toMonoidHom : Set H)) := by
  ext x
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  rfl

private theorem centralizer_map_equiv (e : G ≃* H) (P : Subgroup G) :
    (Subgroup.centralizer (P : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (P.map e.toMonoidHom : Set H) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    obtain ⟨g, hg, rfl⟩ := hy
    change e g * x = x * e g
    simpa only [map_mul, e.apply_symm_apply] using congrArg e (hx g hg)
  · intro hx y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      hx (e y) (Subgroup.mem_map_of_mem e.toMonoidHom hy)

private def normalizerActionMapEquiv (e : G ≃* H) (P : Subgroup G) :
    NormalizerAction P ≃* NormalizerAction (P.map e.toMonoidHom) :=
  QuotientGroup.congr _ _ (normalizerMapEquiv e P) (by
    change ((Subgroup.centralizer (P : Set G)).subgroupOf
      (Subgroup.normalizer (P : Set G))).map
        (normalizerMapEquiv e P).toMonoidHom = _
    rw [subgroupOf_map_normalizerMapEquiv, centralizer_map_equiv])

private theorem normalizerActionImage_map (e : G ≃* H) (P A : Subgroup G)
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hmap : A.map e.toMonoidHom ≤
      Subgroup.normalizer (P.map e.toMonoidHom : Set H)) :
    (NormalizerActionImage P A hAP).map (normalizerActionMapEquiv e P).toMonoidHom =
      NormalizerActionImage (P.map e.toMonoidHom) (A.map e.toMonoidHom) hmap := by
  change ((A.subgroupOf _).map _).map _ = _
  rw [Subgroup.map_map]
  have hcomp : (normalizerActionMapEquiv e P).toMonoidHom.comp
      (QuotientGroup.mk' ((Subgroup.centralizer (P : Set G)).subgroupOf
        (Subgroup.normalizer (P : Set G)))) =
    (QuotientGroup.mk'
      ((Subgroup.centralizer (P.map e.toMonoidHom : Set H)).subgroupOf
        (Subgroup.normalizer (P.map e.toMonoidHom : Set H)))).comp
      (normalizerMapEquiv e P).toMonoidHom := rfl
  rw [hcomp, ← Subgroup.map_map, subgroupOf_map_normalizerMapEquiv]
  rfl

/-- Ambient isomorphisms preserve the p-core bound on the exact normalizer-action image. -/
public theorem normalizerActionImage_le_pCore_map_iff (p : ℕ) (e : G ≃* H)
    (P A : Subgroup G) (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hmap : A.map e.toMonoidHom ≤
      Subgroup.normalizer (P.map e.toMonoidHom : Set H)) :
    NormalizerActionImage (P.map e.toMonoidHom) (A.map e.toMonoidHom) hmap ≤
        pCore p (NormalizerAction (P.map e.toMonoidHom)) ↔
      NormalizerActionImage P A hAP ≤ pCore p (NormalizerAction P) := by
  rw [← normalizerActionImage_map e P A hAP hmap,
    ← pCore_map_iso p (normalizerActionMapEquiv e P)]
  exact (Subgroup.map_le_map_iff_of_injective (normalizerActionMapEquiv e P).injective)

end ABG
