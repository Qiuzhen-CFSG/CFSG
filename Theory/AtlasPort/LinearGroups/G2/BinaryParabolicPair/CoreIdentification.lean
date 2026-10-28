module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure

/-!
# The two-core, center, and overlap of the binary G₂ parabolics

The sixth root coordinate detects failure to remain positive after reflection.
Normality and the common Sylow subgroup therefore identify the five-root
subgroup with the first parabolic’s two-core. Central coordinates identify
Ω₁(Z(T)); the second parabolic has index three over T, giving the exact overlap.
Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988.
-/

@[expose] public section

namespace Atlas.G2.BinaryParabolicPair
open Atlas.G2.Explicit BinaryCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Atlas.SplitOctonion

/-- Conjugating a positive-root element by the other simple reflection keeps
it positive only when its sixth coordinate vanishes. -/
theorem mem_core_of_reflection_mem_unipotent {g : Model (ZMod 2)}
    (hg : g ∈ unipotent) (hs : weylS*g*weylS⁻¹ ∈ unipotent) : g ∈ core := by
  rw [unipotent_eq_range] at hg hs
  obtain ⟨t,rfl⟩ := hg
  obtain ⟨u,hu⟩ := hs
  have he := congrArg (fun g : Model (ZMod 2) => g.val (basisVector 0) 1) hu
  have hleft : (unipotentProduct u).val (basisVector 0) 1 = 0 := by
    have hh := unipotent_le_fixingFirstVector (unipotentProduct_mem u)
    change (unipotentProduct u).val (basisVector 0) = basisVector 0 at hh
    rw [hh]
    rfl
  have hright : (weylS*unipotentProduct t*weylS⁻¹).val (basisVector 0) 1 = t 5 := by
    exact (by decide +kernel : ∀ t : Fin 6 → ZMod 2,
      (weylS*unipotentProduct t*weylS⁻¹).val (basisVector 0) 1 = t 5) t
  rw [hleft, hright] at he
  refine ⟨⟨t 0,t 1,t 2,t 3,t 4⟩, ?_⟩
  simp [embedding, parameters, unipotentProduct, ← he]

theorem firstParabolic_pCore : firstParabolic.pCoreIn 2 = core := by
  apply le_antisymm
  · have hle : pCore 2 firstParabolic ≤
        (commonSylow.subtype commonSylow_le_first : Subgroup firstParabolic) :=
      pCore_isPGroup.le_sylow_of_normal _
    rintro _ ⟨g,hg,rfl⟩
    apply mem_core_of_reflection_mem_unipotent (hle hg)
    let s : firstParabolic := ⟨weylS, weylS_mem_firstParabolic⟩
    exact hle ((inferInstance : (pCore 2 firstParabolic).Normal).conj_mem g hg s)
  · exact Subgroup.le_pCoreIn_of_normalizes
      (IsPGroup.of_card (show Nat.card core = 2^5 from card_core))
      core_le_firstParabolic firstParabolic_normalizes_core

/-- The first parabolic centralizes the marked involution. -/
theorem firstParabolic_centralizes_z (g : Model (ZMod 2)) (hg : g ∈ firstParabolic) :
    g*z = z*g := by
  have hZ : firstParabolic ≤ Subgroup.centralizer ({z} : Set (Model (ZMod 2))) := by
    apply sup_le
    · rw [unipotent_eq_core_sup]
      apply sup_le
      · intro x hx
        exact Subgroup.mem_centralizer_iff.mpr (by
          rintro y (rfl : y=z)
          exact (z_centralizes_core x hx).symm)
      · apply (Subgroup.closure_le _).mpr
        rintro x (rfl : x=shortRoot)
        apply Subgroup.mem_centralizer_iff.mpr
        rintro y (rfl : y=z)
        have hh := short_conjugate involution
        have hf : shortConjugate involution = involution := by decide +kernel
        rw [hf, embedding_involution] at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · apply (Subgroup.closure_le _).mpr
      rintro x (rfl : x=weylS)
      apply Subgroup.mem_centralizer_iff.mpr
      rintro y (rfl : y=z)
      have hh := reflection_conjugate involution
      have hf : reflectionConjugate involution = involution := by decide +kernel
      rw [hf, embedding_involution] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  exact (Subgroup.mem_centralizer_iff.mp (hZ hg) z (Set.mem_singleton z)).symm

private theorem central_parameters (t : Fin 6 → ZMod 2)
    (ht : ∀ j : Fin 6,
      unipotentProductParameters (Pi.single j 1) t =
      unipotentProductParameters t (Pi.single j 1)) :
    t = ![t 0,0,0,0,0,0] := by
  have hh : ∀ t : Fin 6 → ZMod 2, (∀ j : Fin 6,
      unipotentProductParameters (Pi.single j 1) t =
      unipotentProductParameters t (Pi.single j 1)) →
      t = ![t 0,0,0,0,0,0] := by decide +kernel
  exact hh t ht

theorem commonSylow_center :
    (Subgroup.center (unipotent (K := ZMod 2))).map unipotent.subtype = distinguished := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    obtain ⟨t,ht⟩ := (show g.val ∈ unipotentRange from (unipotent_eq_range (K := ZMod 2)) ▸ g.prop)
    have hp : t = ![t 0,0,0,0,0,0] := by
      apply central_parameters
      intro j
      apply unipotentProduct_injective
      rw [← unipotentProduct_mul, ← unipotentProduct_mul, ht]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hg
        ⟨unipotentProduct (Pi.single j 1),unipotentProduct_mem _⟩)
    change g.val ∈ distinguished
    rw [← ht, hp]
    have hb : ∀ a : ZMod 2, a=0 ∨ a=1 := by decide +kernel
    rcases hb (t 0) with h | h
    · simp [h, unipotentProduct]
    · simpa [h, unipotentProduct] using
        (show rootA 1 ∈ distinguished from Subgroup.mem_zpowers z)
  · apply Subgroup.zpowers_le.mpr
    refine ⟨⟨z, core_le_unipotent (elementary_le_core z_mem_elementary)⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply Subtype.ext
    exact firstParabolic_centralizes_z g.val (unipotent_le_firstParabolic g.prop)

/-- The involution picked by the root calculation is exactly Ω₁(Z(T)),
viewed in the ambient group. -/
theorem commonSylow_omega_center :
    ((omega₁ (Subgroup.center (unipotent (K := ZMod 2))) (p := 2)).map
      (Subgroup.center (unipotent (K := ZMod 2))).subtype).map unipotent.subtype =
      distinguished := by
  apply le_antisymm
  · exact (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans commonSylow_center.le
  · apply Subgroup.zpowers_le.mpr
    have hz := (show distinguished ≤
      (Subgroup.center (unipotent (K := ZMod 2))).map unipotent.subtype from
        commonSylow_center.ge) (Subgroup.mem_zpowers z)
    obtain ⟨c,hc,hcz⟩ := hz
    refine ⟨c, ⟨⟨c,hc⟩, ?_, rfl⟩, hcz⟩
    apply Subgroup.subset_closure
    change (⟨c,hc⟩ : Subgroup.center (unipotent (K := ZMod 2))) ^ (2^1) = 1
    apply Subtype.ext
    apply Subtype.ext
    change c.val ^ (2^1) = 1
    change c.val = z at hcz
    rw [hcz, pow_one]
    rw [z, ← embedding_involution, ← map_pow, involution_sq, map_one]

theorem unipotent_index_in_second :
    (unipotent.subgroupOf secondParabolic).index = 3 := by
  have hc := (unipotent.subgroupOf secondParabolic).card_mul_index
  have he := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show unipotent (K := ZMod 2) ≤ secondParabolic from unipotent_le_parabolic)).toEquiv
  rw [he, card_unipotent_binary, secondParabolic_card] at hc
  omega

/-- The actual two root-defined parabolics intersect in the positive roots. -/
theorem parabolic_intersection : firstParabolic ⊓ secondParabolic = unipotent := by
  let C := (Subgroup.centralizer ({z} : Set (Model (ZMod 2)))).subgroupOf secondParabolic
  have hUC : unipotent.subgroupOf secondParabolic ≤ C := by
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    rintro y (rfl : y=z)
    exact (firstParabolic_centralizes_z x.val (unipotent_le_firstParabolic hx)).symm
  have hmax := Subgroup.isCoatom_of_index_three
    (unipotent.subgroupOf secondParabolic) unipotent_index_in_second
  have hC : C = unipotent.subgroupOf secondParabolic := by
    rcases hmax.le_iff.mp hUC with h | h
    · exfalso
      have hm : (⟨movingActor,movingActor_mem⟩ : secondParabolic) ∈ C := by rw [h]; trivial
      have he := Subgroup.mem_centralizer_iff.mp hm z (Set.mem_singleton z)
      change z * movingActor = movingActor * z at he
      exact movingActor_moves (by rw [← he]; group)
    · exact h
  apply le_antisymm
  · intro g hg
    have hm : (⟨g,hg.2⟩ : secondParabolic) ∈ C := by
      apply Subgroup.mem_centralizer_iff.mpr
      rintro y (rfl : y=z)
      exact (firstParabolic_centralizes_z g hg.1).symm
    rw [hC] at hm
    exact hm
  · exact le_inf unipotent_le_firstParabolic unipotent_le_parabolic

end Atlas.G2.BinaryParabolicPair
