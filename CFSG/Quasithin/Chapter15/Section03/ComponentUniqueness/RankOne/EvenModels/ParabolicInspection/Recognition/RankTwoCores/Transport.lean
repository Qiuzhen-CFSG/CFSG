module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.Reduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.AmbientQuotient
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Intrinsic Borel-overgroup calculations and the component image

The model calculations concern every proper overgroup of a Sylow normalizer.
Conjugacy reduces this assertion to one specified Sylow subgroup, and actual
group isomorphisms transport it to the component image. Restricting ambient
subgroups to that image then gives precisely `ParabolicCores`.

A subgroup containing a Sylow subgroup inherits a self-centralizing two-core
from a larger subgroup. Thus containment in a full parabolic covers the Borel
case too; equality with a maximal parabolic is unnecessary here.

Source: Aschbacher--Smith, A.1.6 and the characteristic-two paragraph of
15.3.43, printed p.1140. These are transport lemmas, not model recognition.
-/

@[expose] public section

open Subgroup CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

/-- The intrinsic model calculation, quantified over the actual Sylow subgroups.
Its instances must be proved from the concrete model geometry. -/
def BorelOvergroupCores (H : Type*) [Group H] : Prop :=
  ∀ (T : Sylow 2 H) (Q : Subgroup H),
    normalizer (T : Set H) ≤ Q → Q < ⊤ →
      centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q

variable {H J : Type*} [Group H] [Group J]

/-- Transport the specified Sylow subgroup as well as the proper overgroup. -/
theorem borelOvergroupCores_of_mulEquiv [Finite H] (e : H ≃* J)
    (hc : BorelOvergroupCores J) : BorelOvergroupCores H := by
  intro T Q hBQ hQ
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hB : normalizer (T' : Set J) ≤ Q.map e.toMonoidHom := by
    change normalizer (((T : Subgroup H).map e.toMonoidHom : Subgroup J) : Set J) ≤ _
    rw [← map_equiv_normalizer_eq]
    exact map_mono hBQ
  have hproper : Q.map e.toMonoidHom < ⊤ := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using
      (map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr hQ
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap Q)).mpr
    (hc T' _ hB hproper)

/-- One standard Sylow calculation suffices, with conjugacy tracking its Borel. -/
theorem borelOvergroupCores_of_standard [Finite H] (T : Sylow 2 H)
    (hc : ∀ Q : Subgroup H, normalizer (T : Set H) ≤ Q → Q < ⊤ →
      centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q) : BorelOvergroupCores H := by
  intro P Q hBQ hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P T
  let e := MulAut.conj g
  have hPT : (P : Subgroup H).map e.toMonoidHom = T :=
    congrArg Sylow.toSubgroup hg
  have hB : normalizer (T : Set H) ≤ Q.map e.toMonoidHom := by
    change normalizer ((T : Subgroup H) : Set H) ≤ _
    rw [← hPT, ← map_equiv_normalizer_eq]
    exact map_mono hBQ
  have hproper : Q.map e.toMonoidHom < ⊤ := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using
      (map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr hQ
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap Q)).mpr
    (hc _ hB hproper)

/-- Containment in a characteristic-two parabolic suffices, including when
the subgroup in question is just the Borel. -/
theorem core_of_sylow_overgroup_le (T : Sylow 2 H) (Q P : Subgroup H)
    (hTQ : (T : Subgroup H) ≤ Q) (hQP : Q ≤ P)
    (hc : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q := by
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hQP)).mp
    (centralizer_pCore_le_of_sylow_le (T.subtype (hTQ.trans hQP))
      (Q.subgroupOf P) (fun _ hx => hTQ hx) hc)

/-- Restrict to the literal component image; the ambient normalization
hypothesis imposes no additional requirement on this intrinsic calculation. -/
theorem parabolicCores_of_borelOvergroupCores (K S : Subgroup H)
    (T : Sylow 2 K) (hT : (T : Subgroup K).map K.subtype = S ⊓ K)
    (hc : BorelOvergroupCores K) : ParabolicCores K S := by
  intro Q hBQ hQK _
  have hB : normalizer (T : Set K) ≤ Q.subgroupOf K := by
    change sylowNormalizer T ≤ Q.subgroupOf K
    rw [← borel_subgroupOf_eq_sylowNormalizer K S T hT]
    exact fun _ hx => hBQ hx
  have hproper : Q.subgroupOf K < ⊤ := by
    apply (map_lt_map_iff_of_injective K.subtype_injective).mp
    simpa only [map_subgroupOf_eq_of_le hQK.le, ← MonoidHom.range_eq_map,
      range_subtype] using hQK
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe hQK.le)).mp (hc T _ hB hproper)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
