module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Inputs
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Transport
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Transport of the marked Sylow-center action

An actual group isomorphism carries the embedded Sylow center and its
normalizer to their counterparts. Its induced-action isomorphism transports
the cyclic image, while injectivity on subgroup images transports invariant
subgroups. Sylow conjugacy then reduces all markings to one calculation.

Source: the intrinsic Borel action used in Aschbacher–Smith E.6.8(1),
printed pp.247–248.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction
variable {G H : Type*} [Group G] [Group H]

/-- Center action transports through the actual group isomorphism, retaining
the marked Sylow subgroup and its embedded center. -/
theorem CenterAction.of_equiv [Finite G] (S : Sylow 2 G) (e : G ≃* H) (n : ℕ)
    (ha : CenterAction (S.mapSurjective (f := e.toMonoidHom) e.surjective) n) :
    CenterAction S n := by
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hZ : (sylowCenter S).map e.toMonoidHom = sylowCenter P :=
    map_embeddedCenter (S : Subgroup G) e.toMonoidHom e.injective
  have hN : (normalizer (S : Set G)).map e.toMonoidHom = normalizer (P : Set H) :=
    map_equiv_normalizer_eq (S : Subgroup G) e
  constructor
  · intro A hA hn
    have hA' : A.map e.toMonoidHom ≤ sylowCenter P := by
      rw [← hZ]
      exact map_mono hA
    have hn' : normalizer (P : Set H) ≤ normalizer (A.map e.toMonoidHom : Set H) := by
      rw [← hN, ← map_equiv_normalizer_eq]
      exact map_mono hn
    rcases ha.irreducible (A.map e.toMonoidHom) hA' hn' with h | h
    · left
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      simpa only [Subgroup.map_bot] using h
    · right
      exact Subgroup.map_injective e.injective (h.trans hZ.symm)
  · obtain ⟨f⟩ := exists_actionMapEquiv (sylowCenter S) (normalizer (S : Set G))
      (sylowCenter_normalized S) e.toMonoidHom e.injective
    rw [hZ, hN] at f
    exact ⟨f.trans ha.cyclic_image.some⟩

/-- One marked Sylow calculation supplies every Sylow calculation by conjugacy. -/
theorem CenterAction.all_sylows [Finite G] (P : Sylow 2 G) (n : ℕ)
    (ha : CenterAction P n) (S : Sylow 2 G) : CenterAction S n := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  apply CenterAction.of_equiv S (MulAut.conj g) n
  have hm : S.mapSurjective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).surjective = P := by
    apply Sylow.ext
    exact congrArg Sylow.toSubgroup hg
  rw [hm]
  exact ha

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction
