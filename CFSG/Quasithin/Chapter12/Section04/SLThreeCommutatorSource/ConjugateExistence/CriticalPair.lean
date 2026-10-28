module
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion

/-!
# The actual conjugator from an even critical pair

The critical endpoint in the first vertex orbit is a literal conjugate of
the original seed. F.7.11 supplies its nontrivial commutator and mutual
normalization. The second theorem applies F.7 parity to the weak closure
in a larger ambient group and transports this pair through the embedding;
its output uses exactly MulAut.conj of the mapped conjugating element.

Source: Aschbacher–Smith, 12.4.1, printed p.812, and F.7.9, F.7.11,
printed pp.313–314. This is a conditional geometric implication, not an
assertion that the original source setup has already been constructed.
-/

@[expose] public section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (exists_smul_base)
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open ChapterE ChapterF.Section07 ChapterF.Section07.Track ChapterF.Section07.CriticalPairs
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- An even critical pair produces the literal conjugate and both commutator
conditions, with no choice of a model action or abstract isomorphic module. -/
theorem exists_conjugate_of_even_track (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hb : Even (D.track hne)) :
    ∃ g : G, ⁅D.seed, D.seed.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅D.seed, D.seed.map (MulAut.conj g).toMonoidHom⁆ ≤
        D.seed ⊓ D.seed.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨v, hd, hcrit⟩ := (D.critical_witness hne).1
  have hv := even_endpoint_type F D hne hd hb
  obtain ⟨g, hg⟩ := exists_smul_base F v
  rw [hv] at hg
  have he : vertexModule F D.seed v = D.seed.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, vertexModule_translate_base F D.seed D.seed_normalized]
  exact ⟨g, he ▸ even_pair_commutator_ne_bot F D hne hd hb hcrit,
    he ▸ (even_pair_containments F D hne hd hb).2⟩

/-- F.7 applied inside the generated subgroup and transported to the original
ambient group. The weak closure is taken in that original ambient group. -/
theorem exists_ambient_conjugate_of_weakClosure_core
    (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {K : Type*} [Group K] (f : G →* K) (hf : Function.Injective f)
    (hW : indexedWeakClosure (D.seed.map f)
      (((D.sylow false : Subgroup (F false)).map (F false).subtype).map f) 0 ≤
        ((F true).map f).pCoreIn 2) :
    ∃ g : K, ⁅D.seed.map f, (D.seed.map f).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅D.seed.map f, (D.seed.map f).map (MulAut.conj g).toMonoidHom⁆ ≤
        D.seed.map f ⊓ (D.seed.map f).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hne', hle⟩ := exists_conjugate_of_even_track D hne
    (Completion.even_track_of_ambient_weakClosure_core F D hne f hf hW)
  have he : (D.seed.map (MulAut.conj g).toMonoidHom).map f =
      (D.seed.map f).map (MulAut.conj (f g)).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp
  refine ⟨f g, ?_, ?_⟩
  · intro hc
    apply hne'
    apply (map_eq_bot_iff_of_injective _ hf).mp
    rw [map_commutator, he]
    exact hc
  · have hm := map_mono (f := f) hle
    rwa [map_commutator, map_inf _ _ _ hf, he] at hm

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
