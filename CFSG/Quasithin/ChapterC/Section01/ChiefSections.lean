module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.NoncentralChiefRefinement.IntersectionEmbedding

/-!
# Chief-section maps into the actual block module

For an injective subgroup map J → E, pull U(E) back to J and project it by the
literal map U(E) → U(E)/C_U(E)(E). Its kernel is central in J and the projection
intertwines conjugation by J with conjugation by its image in E.

If the quotient of J by this intersection has only central binary chief
factors, every counted section survives equivariantly in the intersection
filtration. Products of representatives of two distinct sections then give an
injection into the actual block module. The quotient centrality remains an
explicit structural premise; it is not part of the definition of a short group.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), C.1.7 and
14.7.68(2), printed pp.123 and 1071--1072. Both ordinary and exceptional A7
blocks use the same maps, with no assertion that the subgroup actor is normal.
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.ChapterC
open NoncentralChiefRefinement
variable {E J : Type*} [Group E] [Group J]

/-- The literal intersection with the moving layer, normal in the subgroup actor. -/
def blockIntersection (ι : J →* E) : NormalNode J :=
  ⟨(blockU E).comap ι, inferInstanceAs ((blockU E).comap ι).Normal⟩

/-- Restrict the original inclusion to the moving layer. -/
def blockIntersectionHom (ι : J →* E) : (blockIntersection ι).val →* blockU E where
  toFun r := ⟨ι r.val, r.property⟩
  map_one' := Subtype.ext (map_one ι)
  map_mul' r t := Subtype.ext (map_mul ι r.val t.val)

/-- The original moving-layer projection, with the source intersection retained. -/
def blockIntersectionProjection (ι : J →* E) :
    (blockIntersection ι).val →* BlockModule E :=
  (QuotientGroup.mk' (blockFixed E)).comp (blockIntersectionHom ι)

/-- The fixed denominator is central for the actual subgroup action. -/
theorem blockIntersectionProjection_ker_central (ι : J →* E)
    (hι : Function.Injective ι) (r : (blockIntersection ι).val)
    (hr : blockIntersectionProjection ι r = 1) : (r : J) ∈ center J := by
  have hz : ι (r : J) ∈ center E :=
    (QuotientGroup.eq_one_iff (blockIntersectionHom ι r)).mp hr
  apply mem_center_iff.mpr
  intro j
  apply hι
  simpa only [map_mul] using mem_center_iff.mp hz (ι j)

/-- Conjugation is transported by the original embedding on every representative. -/
theorem blockIntersectionProjection_equivariant (ι : J →* E)
    (ρ : E →* MulAut (BlockModule E))
    (hρ : ∀ (e : E) (v : blockU E),
      ρ e (QuotientGroup.mk' (blockFixed E) v) =
        QuotientGroup.mk' (blockFixed E) (blockConjugate E e v))
    (j : J) (r : (blockIntersection ι).val) :
    blockIntersectionProjection ι (MulAut.conjNormal j r) =
      ρ (ι j) (blockIntersectionProjection ι r) := by
  change QuotientGroup.mk' (blockFixed E) (blockIntersectionHom ι (MulAut.conjNormal j r)) =
    ρ (ι j) (QuotientGroup.mk' (blockFixed E) (blockIntersectionHom ι r))
  rw [hρ]
  congr 1
  apply Subtype.ext
  change ι (j * (r : J) * j⁻¹) = ι j * ι (r : J) * (ι j)⁻¹
  simp only [map_mul, map_inv]

/-- The actual J-chief sections survive with their full J-actions. -/
noncomputable def chiefIntersectionEquiv (ι : J →* E)
    (hquot : HasCentralPChiefFactors 2 (J ⧸ (blockU E).comap ι))
    (s : ChiefSeries J) (i : Fin s.length)
    (hi : IsNoncentralTwo (s i.castSucc) (s i.succ)) :
    SectionEquiv ((s.intersectionFiltration (blockIntersection ι)).term i.castSucc)
      ((s.intersectionFiltration (blockIntersection ι)).term i.succ)
      (s i.castSucc) (s i.succ) :=
  s.intersectionFactorEquiv (blockIntersection ι) hquot i hi

/-- Multiply intersection representatives to embed any two distinct counted sections. -/
noncomputable def chiefPairEmbedding (ι : J →* E) (hι : Function.Injective ι)
    (hquot : HasCentralPChiefFactors 2 (J ⧸ (blockU E).comap ι))
    (s : ChiefSeries J) (i j : Fin s.length) (hij : i ≠ j)
    (hi : IsNoncentralTwo (s i.castSucc) (s i.succ))
    (hj : IsNoncentralTwo (s j.castSucc) (s j.succ)) :
    Section (s i.castSucc) (s i.succ) × Section (s j.castSucc) (s j.succ) ↪ BlockModule E :=
  s.intersectionPairEmbedding (blockIntersection ι) hquot
    (blockIntersectionProjection ι) (blockIntersectionProjection_ker_central ι hι)
    i j hij hi hj

end CFSG.Quasithin.ChapterC
