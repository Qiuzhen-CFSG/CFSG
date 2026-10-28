module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.Reduction
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.SpecificGroups.PSL3.LinearThreeSylow
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CentralBorelQuotient

/-!
# The original PSL₃ overlap and its central-cover Borel

The map from the component image in X/O₂(X) to the component image in X/J
is constructed using O₂(X) ≤ J. The source center identity makes its kernel
central. The marking identifies the full preimage of the projective Borel,
and the original overlap K ∩ M surjects onto it with two-group kernel.
Thus the intrinsic quotients by their two-cores are genuinely isomorphic.

The odd-index assertion on the original overlap is proved unconditionally:
a central surjection pulls a Sylow normalizer back to a Sylow normalizer.
The concrete central-cover calculation proves that the Borel preimage has
abelian quotient by its two-core, using the actual reversal matrix and the
odd-order torus generators. Transport gives the unconditional covered-Borel
and Hall-control applications on the original overlap and Sylow subgroup.

Source: Aschbacher--Smith, E.2.2(2b), printed pp.215--216, and the Borel
calculation in 4.4.13, printed pp.623--624, combined manuscript of 1 March 2004.
-/

@[expose] public section

noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall
open ChapterB
variable {X : Type*} [Group X]

/-- The restriction of the literal quotient map X/O₂(X) → X/J to K’s image. -/
def linearSourceComparison (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) :
    actorImage K →* sourceImage (minimalParabolicMax S hP) K :=
  ((QuotientGroup.map (pCore 2 X) (sourceKernel (minimalParabolicMax S hP))
    (MonoidHom.id X) (twoCore_le_sourceKernel S hP)).comp (actorImage K).subtype).codRestrict
      (sourceImage (minimalParabolicMax S hP) K) (by
        rintro ⟨x, k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩)

/-- Every source component element comes from the same representative in K. -/
theorem linearSourceComparison_surjective (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X) :
    Function.Surjective (linearSourceComparison S hP K) := by
  rintro ⟨x, k, hk, rfl⟩
  exact ⟨⟨QuotientGroup.mk' (pCore 2 X) k, k, hk, rfl⟩, rfl⟩

/-- E.2.2’s center identity makes the comparison kernel central in K’s actor image. -/
theorem linearSourceComparison_central (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hc : SingleClauses (minimalParabolicMax S hP) K S) :
    (linearSourceComparison S hP K).ker ≤ center (actorImage K) := by
  intro x hx
  have hx' : (x : X ⧸ pCore 2 X) ∈
      (sourceKernel (minimalParabolicMax S hP)).map (QuotientGroup.mk' (pCore 2 X)) := by
    have he := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    change QuotientGroup.map (pCore 2 X) (sourceKernel (minimalParabolicMax S hP))
      (MonoidHom.id X) (twoCore_le_sourceKernel S hP) x = 1 at he
    obtain ⟨k, hk, hkx⟩ := x.property
    refine ⟨k, ?_, hkx⟩
    apply (QuotientGroup.eq_one_iff _).mp
    rw [← hkx] at he
    exact he
  rw [hc.kernel_center] at hx'
  obtain ⟨z, hz, he⟩ := hx'
  exact (Subtype.ext he : z = x) ▸ hz

variable {F : Type*} [Field F]

/-- The marked Borel pulls back to membership in M, using J ≤ M. -/
theorem linearSourceComparison_preimage (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (e : sourceImage (minimalParabolicMax S hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F) (k : K) :
    e (linearSourceComparison S hP K
      ⟨QuotientGroup.mk' (pCore 2 X) k, k, k.property, rfl⟩) ∈
        Matrix.PSL3.LinearThree.borel F ↔ (k : X) ∈ minimalParabolicMax S hP := by
  rw [← he, mem_map_equiv, e.symm_apply_apply]
  change QuotientGroup.mk' (sourceKernel (minimalParabolicMax S hP)) k ∈
    sourceImage (minimalParabolicMax S hP) (minimalParabolicMax S hP ⊓ K) ↔ _
  constructor
  · rintro ⟨m, hm, hmk⟩
    have hd := QuotientGroup.eq_iff_div_mem.mp hmk
    have hdM := (minimalParabolicMax S hP).normalCore_le hd
    have hh := (minimalParabolicMax S hP).mul_mem
      ((minimalParabolicMax S hP).inv_mem hdM) hm.1
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
  · intro hk
    exact ⟨k, ⟨hk, k.property⟩, rfl⟩

/-- The original overlap maps to the full Borel preimage in the actual central cover. -/
def linearCoveredProjection (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (e : sourceImage (minimalParabolicMax S hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F) :
    K.subgroupOf (minimalParabolicMax S hP) →*
      (Matrix.PSL3.LinearThree.borel F).comap
        (e.toMonoidHom.comp (linearSourceComparison S hP K)) where
  toFun b := ⟨⟨QuotientGroup.mk' (pCore 2 X) b.val.val,
      b.val.val, b.property, rfl⟩,
    (linearSourceComparison_preimage S hP K e he ⟨b.val.val, b.property⟩).mpr b.val.property⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' _ _ := Subtype.ext (Subtype.ext (map_mul _ _ _))

/-- The overlap restriction is onto, rather than merely an inclusion in the Borel. -/
theorem linearCoveredProjection_surjective (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (e : sourceImage (minimalParabolicMax S hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F) :
    Function.Surjective (linearCoveredProjection S hP K e he) := by
  rintro ⟨⟨x, k, hk, rfl⟩, hb⟩
  have hkm := (linearSourceComparison_preimage S hP K e he ⟨k, hk⟩).mp hb
  exact ⟨⟨⟨k, hkm⟩, hk⟩, rfl⟩

/-- The restriction kernel embeds in the original ambient two-core. -/
theorem linearCoveredProjection_kernel_two (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (e : sourceImage (minimalParabolicMax S hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F) :
    IsPGroup 2 (linearCoveredProjection S hP K e he).ker := by
  let B := K.subgroupOf (minimalParabolicMax S hP)
  let f := linearCoveredProjection S hP K e he
  let j : f.ker →* X := (minimalParabolicMax S hP).subtype.comp
    (B.subtype.comp f.ker.subtype)
  have hj (b : f.ker) : j b ∈ pCore 2 X := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg (fun z => z.val.val) (MonoidHom.mem_ker.mp b.property)
  exact pCore_isPGroup.of_injective (j.codRestrict (pCore 2 X) hj) (by
    intro a b hab
    have hh : j a = j b := congrArg (fun z : pCore 2 X => (z : X)) hab
    exact Subtype.ext (Subtype.ext (Subtype.ext hh)))

variable [Finite X]

/-- The original covered Borel is two-closed, with no additional cover premise. -/
theorem linear_coveredBorel_odd_index [Finite F] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (e : sourceImage (minimalParabolicMax S hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F) :
    Odd (pCore 2 (K.subgroupOf (minimalParabolicMax S hP))).index := by
  let f := e.toMonoidHom.comp (linearSourceComparison S hP K)
  have hf : Function.Surjective f :=
    e.surjective.comp (linearSourceComparison_surjective S hP K)
  have hfc : f.ker ≤ center (actorImage K) := by
    intro x hx
    apply linearSourceComparison_central S hP K hc
    apply e.injective
    exact (MonoidHom.mem_ker.mp hx).trans (map_one e).symm
  let U := Matrix.PSL3.LinearThree.unipotentSylow F hn hF
  obtain ⟨P, hPu⟩ := Sylow.mapSurjective_surjective hf 2 U
  have hB : (Matrix.PSL3.LinearThree.borel F).comap f = normalizer (P : Set _) := by
    rw [← Matrix.PSL3.LinearThree.normalizer_unipotent F hn hF]
    have hh := P.normalizer_comap_of_central_kernel f hf hfc
    rw [hPu] at hh
    exact hh
  have hi : Odd (pCore 2 ((Matrix.PSL3.LinearThree.borel F).comap f)).index := by
    rw [hB]
    let Q : Sylow 2 (normalizer (P : Set (actorImage K))) :=
      P.subtype (P : Subgroup (actorImage K)).le_normalizer
    have hQ : (Q : Subgroup (normalizer (P : Set (actorImage K)))).Normal := by
      change ((P : Subgroup (actorImage K)).subgroupOf
        (normalizer (P : Set (actorImage K)))).Normal
      exact (normal_subgroupOf_iff_le_normalizer
        (P : Subgroup (actorImage K)).le_normalizer).mpr le_rfl
    let := hQ
    have hcore : pCore 2 (normalizer (P : Set (actorImage K))) =
        (Q : Subgroup (normalizer (P : Set (actorImage K)))) :=
      le_antisymm (pCore_isPGroup.le_sylow_of_normal Q)
        (le_sSup ⟨hQ, Q.isPGroup'⟩)
    rw [hcore]
    exact Nat.not_even_iff_odd.mp (Q.not_dvd_index ∘ even_iff_two_dvd.mp)
  let q := linearCoveredProjection S hP K e he
  let iq := q.quotientPCoreEquivOfSurjective
    (linearCoveredProjection_surjective S hP K e he)
    (linearCoveredProjection_kernel_two S hP K e he)
  rw [index_eq_card, Nat.card_congr iq.toEquiv, ← index_eq_card]
  exact hi

/-- Transport a concrete abelian-quotient calculation back to K ∩ M.
The unconditional assembly below supplies this model premise. -/
theorem linear_coveredBorel_of_centralBorel [Finite F] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (e : sourceImage (minimalParabolicMax S hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F)
    (hmodel : ∀ (f : actorImage K →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F),
      Function.Surjective f → f.ker ≤ center (actorImage K) →
      IsMulCommutative (((Matrix.PSL3.LinearThree.borel F).comap f) ⧸
        pCore 2 ((Matrix.PSL3.LinearThree.borel F).comap f))) :
    CoveredBorelControl S hP K := by
  let f := e.toMonoidHom.comp (linearSourceComparison S hP K)
  have hf : Function.Surjective f :=
    e.surjective.comp (linearSourceComparison_surjective S hP K)
  have hfc : f.ker ≤ center (actorImage K) := by
    intro x hx
    apply linearSourceComparison_central S hP K hc
    apply e.injective
    exact (MonoidHom.mem_ker.mp hx).trans (map_one e).symm
  have hb := hmodel f hf hfc
  let q := linearCoveredProjection S hP K e he
  let iq := q.quotientPCoreEquivOfSurjective
    (linearCoveredProjection_surjective S hP K e he)
    (linearCoveredProjection_kernel_two S hP K e he)
  refine ⟨?_, ?_⟩
  · exact linear_coveredBorel_odd_index hn hF S hP K hc e he
  · let := hb
    exact IsMulCommutative.of_comm fun a b => iq.injective (by
      simp only [map_mul]
      exact mul_comm' _ _)

/-- Actual application of the conditional covered-Borel calculation to the original
Sylow and maximal subgroup. The concrete model premise is retained explicitly. -/
theorem linear_hallControl_of_centralBorel [Finite F] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X) (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (e : sourceImage (minimalParabolicMax S hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F)
    (hmodel : ∀ (f : actorImage K →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F),
      Function.Surjective f → f.ker ≤ center (actorImage K) →
      IsMulCommutative (((Matrix.PSL3.LinearThree.borel F).comap f) ⧸
        pCore 2 ((Matrix.PSL3.LinearThree.borel F).comap f))) :
    HallControl S hP :=
  hallControl_of_coveredBorel S hP hK hc
    (linear_coveredBorel_of_centralBorel hn hF S hP K hc e he hmodel)

/-- The original PSL₃ component overlap is two-closed with abelian odd quotient.
The central-cover calculation discharges the model premise on `actorImage K`;
the quotient transport retains the distinct source kernel and ambient two-core. -/
theorem linear_coveredBorel [Finite F] {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (e : sourceImage (minimalParabolicMax S hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F) :
    CoveredBorelControl S hP K :=
  linear_coveredBorel_of_centralBorel (by omega) hF S hP K hc e he
    (fun f hf hk =>
      Matrix.PSL3.LinearThree.CentralBorelQuotient.quotient_isMulCommutative F hn hF f hf hk)

/-- The PSL₃ source data supply Hall control on the original maximal subgroup,
with no additional covered-Borel or commutativity premise. -/
theorem linear_hallControl [Finite F] {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X) (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (e : sourceImage (minimalParabolicMax S hP) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F) :
    HallControl S hP :=
  hallControl_of_coveredBorel S hP hK hc
    (linear_coveredBorel hn hF S hP K hc e he)

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall
