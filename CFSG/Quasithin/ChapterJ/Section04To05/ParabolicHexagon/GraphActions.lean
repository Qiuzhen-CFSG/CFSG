module

public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.Graph
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.CoreReflection
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.NormalizerSource

/-!
# The actual normalizer action on the six-parabolic graph

Conjugation by the normalizer of the original four-group preserves the literal
commuting-five incidence relation. The characteristic omega subgroup of the
marked sixteen-group supplies this normalizer condition for every source
reflection. Fixed-five labels are transported by the same ambient conjugation.

Source: Aschbacher–Smith, J.4.8–J.4.10, printed pp.443–445.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (B5:Sylow 5 d.toTypeRuSetup.H) (c:Choices d)
  (e:first≃*p.F₁ B5) (hz:(e modelZ:G)=c.z)

/-- The actual normalizer acts by graph automorphisms with literal conjugation. -/
def sourceGraphEquiv (n:G) (hn:n∈normalizer (pairSpan c.z (sourceU e):Set G)) :
    sourceGraph p B5 c.z (sourceU e) ≃g sourceGraph p B5 c.z (sourceU e) where
  toEquiv := {
    toFun E := ⟨E.val.conjBy n,global_conjugate_mem p B5 c e hz n hn E.property⟩
    invFun E := ⟨E.val.conjBy n⁻¹,global_conjugate_mem p B5 c e hz n⁻¹ (inv_mem hn) E.property⟩
    left_inv E := Subtype.ext (conjBy_inv E.val n)
    right_inv E := Subtype.ext (conjBy_inv' E.val n) }
  map_rel_iff' := by
    intro E F
    simpa only [sourceGraph_adj_iff, Subgroup.PrimeIncidence.adj_iff, Equiv.coe_fn_mk] using
      Subgroup.PrimeIncidence.conj_adj_iff (p:=5) (V:=pairSpan c.z (sourceU e))
      (E:=(E:Subgroup G)) (F:=(F:Subgroup G)) n hn

theorem sourceGraphEquiv_apply (n:G) (hn:n∈normalizer (pairSpan c.z (sourceU e):Set G))
    (E:globalFamily p B5 c.z (sourceU e)) :
    (sourceGraphEquiv p B5 c e hz n hn E:Subgroup G)=E.val.conjBy n := by rfl

include hz in
/-- Every original I-normalizer preserves the same four-group span. -/
theorem sourceI_normalizer_le_pairSpan_normalizer :
    normalizer (sourceI e:Set G)≤normalizer (pairSpan c.z (sourceU e):Set G) := by
  intro n hn
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (zpowers c.z ⊔ zpowers (sourceU e)).map (MulAut.conj n).toMonoidHom =
    zpowers c.z ⊔ zpowers (sourceU e)
  rw [←source_omega_plane c e hz]
  rw [←Stellmacher.omegaOneCenterAmbient_map_injective (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective]
  exact congrArg Stellmacher.omegaOneCenterAmbient
    (mem_normalizer_iff_map_conj_eq.mp hn)

/-- The original quaternion reflection sends the actual fixed-five u label to the zu label. -/
theorem fixedFive_conj_of_base_normalizer (n v:G)
    (hn:n∈normalizer (B5Image B5:Set G)) :
    (fixedFive B5 v).conjBy n=fixedFive B5 (n*v*n⁻¹) := by
  have hnP:=normalizer_B5Image_le_normalizer_fiveOddPart B5 hn
  change (fiveOddPart B5⊓centralizer ({v}:Set G)).map (MulAut.conj n).toMonoidHom=_
  rw [map_inf _ _ _ (MulAut.conj n).injective,Theory.GroupTheory.map_centralizer_singleton]
  have hfix:(fiveOddPart B5).map (MulAut.conj n).toMonoidHom=fiveOddPart B5 :=
    mem_normalizer_iff_map_conj_eq.mp hnP
  rw [hfix]
  rfl
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
