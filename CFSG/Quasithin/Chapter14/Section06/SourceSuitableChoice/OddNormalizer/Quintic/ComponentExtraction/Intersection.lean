module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExtraction
public import Theory.GroupTheory.ConjugateOrbitIndexTwoStabilizer
/-!
# The original intersection fixes the first factor

The stabilizer of K_2 in M_c has index two, hence is normal in M_c.
Conjugating by the original exchanging Sylow element shows that this
same stabilizer normalizes K_1. In particular the source intersection
B = <J^{Q_1}> ∩ M_c ∩ N_G(K_2) normalizes K_1, for the literal Q_1-span.

This is the marked-normalization step in Aschbacher--Smith 14.6.15,
printed p.1035. It uses the original index-two geometry; it does not
supply a version of the argument without that premise.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)


/-- The index-two stabilizer fixes both original exchanged factors. -/
theorem intersection_normalizes_first :
    Mc ⊓ normalizer (d.K2 : Set G) ≤ normalizer (d.K1 : Set G) := by
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [partner_eq_centralizer s]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  obtain ⟨t,ht,_,he⟩ := d.exchanged
  have hi : (normalizer (d.K2 : Set G)).relIndex Mc = 2 := by
    simpa only [inf_relIndex_left] using d.intersection_index
  have h := index_two_stabilizer_normalizes_conjugate d.K2 Mc hi (hTMc ht)
  have he' : d.K2.map (MulAut.conj t).toMonoidHom = d.K1 := by
    rw [←he,map_map]
    have hf : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
        MulAut.conj_apply,inv_inv,MonoidHom.id_apply]
      group
    rw [hf,map_id]
  rwa [he'] at h

/-- The literal B from the source therefore normalizes the same K_1. -/
theorem span_intersection_normalizes_first (J : Subgroup G) :
    conjugateSpanBy J (Mc.pCoreIn 2) ⊓ (Mc ⊓ normalizer (d.K2 : Set G)) ≤
      normalizer (d.K1 : Set G) :=
  inf_le_right.trans (intersection_normalizes_first s d)
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
