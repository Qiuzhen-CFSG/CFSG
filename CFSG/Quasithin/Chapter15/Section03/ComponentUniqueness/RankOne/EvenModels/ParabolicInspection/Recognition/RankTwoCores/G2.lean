module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Transport
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.LongCore
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.ShortCore
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.BorelOvergroups

/-!
# Self-centralizing cores in even-field G₂

The concrete even-field G₂ calculation has two parts.  The normalizer of the
positive-root Sylow subgroup is the Borel, and each proper Borel overgroup is
placed in one of the two standard root parabolics. The concrete Bruhat
factorization and root descent prove this placement in `EvenLocal.BorelOvergroups`.
Then `core_of_sylow_overgroup_le` transports the
self-centralizing core of either full parabolic, including the Borel itself.
The existing normalizer cover also proves the assertion for any Sylow
overgroup with nonidentity two-core. Nonidentity of that core for an arbitrary
proper Borel overgroup is not assumed to follow from the normalizer cover.

The two full-parabolic core calculations are the licensed ATLAS port in
`Theory.AtlasPort.LinearGroups.G2.EvenLocal`; the normalizer calculation is
`Theory.AtlasPort.LinearGroups.G2.SylowNormalizer`.  Source: Aschbacher--Smith,
15.3.43, printed p.1140, and A.2.3--4, printed p.33. The coverage argument is
the concrete rank-two instance of GLS III, Theorem 2.6.5(b). The conditional
transport interfaces remain available, and the final G₂ branch discharges
their geometric premise over every finite field of characteristic two.
-/

public section

open Subgroup
open Atlas.G2 Atlas.G2.LieParabolicSetup

namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

namespace G2Cores

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem core_of_conjugate_parabolic (T : Sylow 2 (Atlas.G2.Model F))
    (Q : Subgroup (Atlas.G2.Model F))
    (hTQ : (T : Subgroup (Atlas.G2.Model F)) ≤ Q)
    (g : Atlas.G2.Model F)
    (hQ : Q.map (MulAut.conj g).toMonoidHom ≤ parabolic₁ ∨
      Q.map (MulAut.conj g).toMonoidHom ≤ parabolic₂) :
    centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q := by
  let e := MulAut.conj g
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hTQ' : (T' : Subgroup (Atlas.G2.Model F)) ≤ Q.map e.toMonoidHom :=
    map_mono hTQ
  apply (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap Q)).mpr
  rcases hQ with hQ | hQ
  · exact core_of_sylow_overgroup_le T' _ _ hTQ' hQ
      Atlas.G2.EvenLocal.parabolic₁_centralizer_pCore
  · exact core_of_sylow_overgroup_le T' _ _ hTQ' hQ
      Atlas.G2.EvenLocal.parabolic₂_centralizer_pCore

/-- Normalizer coverage suffices when the intrinsic core is already known to
be nonidentity. The ambient image is normal relative to `Q`; no ambient
normality of the core is asserted. -/
theorem core_of_nontrivial_pCore (T : Sylow 2 (Atlas.G2.Model F))
    (Q : Subgroup (Atlas.G2.Model F))
    (hTQ : (T : Subgroup (Atlas.G2.Model F)) ≤ Q)
    (hcore : pCore 2 Q ≠ ⊥) :
    centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q := by
  let R := (pCore 2 Q).map Q.subtype
  have hR : R ≠ ⊥ := fun h => hcore
    (((pCore 2 Q).map_eq_bot_iff_of_injective Q.subtype_injective).mp h)
  have hQN : Q ≤ normalizer (R : Set (Atlas.G2.Model F)) := by
    intro q hq
    apply (pCore 2 Q).le_normalizer_map Q.subtype
    exact ⟨⟨q, hq⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  obtain ⟨g, hg⟩ :=
    Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic
      R hR (pCore_isPGroup.map Q.subtype)
  exact core_of_conjugate_parabolic T Q hTQ g
    (hg.imp ((map_mono hQN).trans ·) ((map_mono hQN).trans ·))

/-- The Borel itself is covered by the short parabolic. -/
theorem borel_core :
    centralizer (pCore 2 (borel (K := F)) : Set (borel (K := F))) ≤
      pCore 2 (borel (K := F)) :=
  core_of_sylow_overgroup_le sylow borel parabolic₁ sylow_le_borel
    borel_le_parabolic₁ Atlas.G2.EvenLocal.parabolic₁_centralizer_pCore

/-- Once proper Borel overgroups have been placed in conjugate parabolics,
both the full-parabolic calculation and Sylow conjugacy are discharged. -/
theorem borelOvergroupCores_of_parabolic_cover
    (hcover : ∀ (Q : Subgroup (Atlas.G2.Model F)), borel ≤ Q → Q < ⊤ →
      ∃ g : Atlas.G2.Model F,
        Q.map (MulAut.conj g).toMonoidHom ≤ parabolic₁ ∨
          Q.map (MulAut.conj g).toMonoidHom ≤ parabolic₂) :
    BorelOvergroupCores (Atlas.G2.Model F) := by
  apply borelOvergroupCores_of_standard (LieParabolicSetup.sylow (F := F))
  intro Q hBQ hQ
  have hB : borel (K := F) ≤ Q := by
    change normalizer (unipotent (K := F) : Set (Atlas.G2.Model F)) ≤ Q at hBQ
    rw [Atlas.G2.SylowNormalizer.normalizer_unipotent] at hBQ
    exact hBQ
  obtain ⟨g, hg⟩ := hcover Q hB hQ
  exact core_of_conjugate_parabolic (LieParabolicSetup.sylow (F := F)) Q
    (sylow_le_borel.trans hB) g hg

/-- All proper Borel overgroups in the full even-field G₂ model have
self-centralizing two-core, with concrete parabolic coverage discharged. -/
theorem borelOvergroupCores : BorelOvergroupCores (Atlas.G2.Model F) :=
  borelOvergroupCores_of_parabolic_cover
    Atlas.G2.EvenLocal.BorelOvergroups.conjugate_le_parabolic

end G2Cores

/-- Conditional field-witness assembly. The independent model-geometry
theorem must supply `hcover` before this proves the requested G₂ branch. -/
theorem g2_borelOvergroupCores_of_parabolic_cover
    {H : Type*} [Group H] [Finite H] {n : ℕ}
    (hm : ClassificationModels.IsG2At H (2 ^ n))
    (hcover : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      Nat.card F = 2 ^ n →
      ∀ Q : Subgroup (Atlas.G2.Model F), borel ≤ Q → Q < ⊤ →
        ∃ g : Atlas.G2.Model F,
          Q.map (MulAut.conj g).toMonoidHom ≤ parabolic₁ ∨
            Q.map (MulAut.conj g).toMonoidHom ≤ parabolic₂) :
    BorelOvergroupCores H := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  exact borelOvergroupCores_of_mulEquiv e
    (G2Cores.borelOvergroupCores_of_parabolic_cover (hcover F hcard))

/-- The G₂ field-witness branch, including the full group at the binary
parameter, has self-centralizing cores in every proper Borel overgroup. -/
theorem g2_borelOvergroupCores
    {H : Type*} [Group H] [Finite H] {n : ℕ}
    (hm : ClassificationModels.IsG2At H (2 ^ n)) :
    BorelOvergroupCores H := by
  apply g2_borelOvergroupCores_of_parabolic_cover hm
  intro F _ _ _ _
  exact Atlas.G2.EvenLocal.BorelOvergroups.conjugate_le_parabolic

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
