module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Transport
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry

/-!
# Symplectic Borel-overgroup cores

Both full flag parabolics have self-centralizing two-cores. A subgroup
containing a Sylow two-subgroup inherits that property whenever a genuine
symplectic conjugation puts it inside either full parabolic. The specified
Sylow is transported along the same conjugation. Proper Sylow overgroups
lie in conjugate full parabolics by the intrinsic symplectic geometry,
so this covers every proper Borel overgroup, including the Borel itself.

The model adapter retains the actual field witness from `IsPSp`
and uses the characteristic-two equivalence between Sp₄ and its central
quotient. The final theorem supplies the geometric coverage premise and
needs neither simplicity nor nonabelianity.

Source: Aschbacher--Smith, A.1.6, A.2.3--4, printed p.33, and the
characteristic-two paragraph of 15.3.43, printed p.1140.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
namespace SymplecticCores
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

/-- Core inheritance through a genuine symplectic change of coordinates,
transporting the given Sylow subgroup at the same time. -/
theorem core_of_conjugate_parabolic (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (T : Sylow 2 (Sp F)) (Q : Subgroup (Sp F))
    (hTQ : (T : Subgroup (Sp F)) ≤ Q)
    (hpar : ∃ g : Sp F, Q.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      Q.map (MulAut.conj g).toMonoidHom ≤ planeParabolic) :
    centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q := by
  let _ : CharP F 2 := EvenProjective.charTwo_of_card hF
  obtain ⟨g, hg⟩ := hpar
  let e := MulAut.conj g
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT' : (T' : Subgroup (Sp F)) ≤ Q.map e.toMonoidHom := map_mono hTQ
  apply (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap Q)).mpr
  rcases hg with hp | hp
  · exact core_of_sylow_overgroup_le T' _ pointParabolic hT' hp
      (pointParabolic_selfCentralizing_core hF hn)
  · exact core_of_sylow_overgroup_le T' _ planeParabolic hT' hp
      (planeParabolic_selfCentralizing_core hF hn)

/-- The Borel itself is covered by the full point parabolic. -/
theorem borel_core (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    centralizer (pCore 2 (borel (F := F)) : Set (borel (F := F))) ≤
      pCore 2 (borel (F := F)) := by
  let _ : CharP F 2 := EvenProjective.charTwo_of_card hF
  exact core_of_sylow_overgroup_le (unipotentSylow hF hn.le) borel pointParabolic
    unipotent_le_borel inf_le_left (pointParabolic_selfCentralizing_core hF hn)

/-- Geometric coverage for the standard flag suffices for all Sylow normalizers. -/
theorem borelOvergroupCores_of_standard_cover
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hcover : ∀ Q : Subgroup (Sp F), borel ≤ Q → Q < ⊤ →
      ∃ g : Sp F, Q.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
        Q.map (MulAut.conj g).toMonoidHom ≤ planeParabolic) :
    BorelOvergroupCores (Sp F) := by
  apply borelOvergroupCores_of_standard (unipotentSylow hF hn.le)
  intro Q hBQ hQ
  have hB : borel ≤ Q := by
    change normalizer (unipotent (F := F) : Set (Sp F)) ≤ Q at hBQ
    simpa only [← borel_eq_normalizer_unipotent] using hBQ
  exact core_of_conjugate_parabolic hF hn (unipotentSylow hF hn.le) Q
    (unipotent_le_borel.trans hB) (hcover Q hB hQ)

end SymplecticCores

open Theory.SpecificGroups.SymplecticFour
/-- The complete model and Sylow transport, conditional only on the independent
proper-Sylow-overgroup coverage theorem. Final assembly must supply that theorem. -/
theorem symplecticFour_borelOvergroupCores_of_parabolic_cover
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp H 2 (2 ^ n))
    (hcover : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      2 < Nat.card F → ∀ (T : Sylow 2 (Sp F)) (Q : Subgroup (Sp F)),
        (T : Subgroup (Sp F)) ≤ Q → Q ≠ ⊤ →
        ∃ g : Sp F, Q.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
          Q.map (MulAut.conj g).toMonoidHom ≤ planeParabolic) :
    BorelOvergroupCores H := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ : CharP F 2 := EvenProjective.charTwo_of_card hF
  apply borelOvergroupCores_of_mulEquiv (e.trans EvenProjective.equiv.symm)
  apply SymplecticCores.borelOvergroupCores_of_standard_cover hF hn
  intro Q hBQ hQ
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ) ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  exact hcover F hlarge (unipotentSylow hF hn.le) Q
    (unipotent_le_borel.trans hBQ) hQ.ne

/-- Every proper overgroup of a Sylow two-normalizer in PSp₄(2ⁿ), for n > 1,
has self-centralizing intrinsic two-core. -/
theorem symplecticFour_borelOvergroupCores
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp H 2 (2 ^ n)) :
    BorelOvergroupCores H := by
  apply symplecticFour_borelOvergroupCores_of_parabolic_cover hn hm
  intro F _ _ _ hF T Q hTQ hQ
  exact ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover hF T Q hTQ hQ

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
