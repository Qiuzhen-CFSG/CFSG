module

public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.CoreCentralizers
public import Theory.GroupTheory.CentralExtensionGeneratedP
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

set_option linter.style.haveILetI false

/-!
# The radical of the source three-space

For the literal action of the source join `K` on its three-space, the kernel
is `R = K ∩ C_G(Z)`. The core-centralizer argument gives centrality of this
kernel after factoring out `O₂(K)`. The abelianization of that quotient is a
2-group because `K` is the join of its seven original extraspecial point
cores. The checked central-cover argument for `SL₃(2)` then identifies `R`
with `O₂(K)`.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), proof of (4.4), pp.597–598,
DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement

namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

/-- A finite central extension of `SL₃(2)` whose abelianization is a
2-group has a 2-group kernel. -/
theorem sl3Two_central_kernel_isTwoGroup {E : Type*} [Group E] [Finite E]
    (f : E →* Matrix.PSL3Two.SL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (ha : IsPGroup 2 (E ⧸ commutator E)) :
    IsPGroup 2 f.ker := by
  let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  apply CentralExtension.kernel_isPGroup_of_derived_kernel f hf hc ?_ ha
  apply (isPGroup_iff_primeFactors_card_subset (p := 2) (by decide)).mpr
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_refl _, by decide⟩
  · obtain ⟨hpprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    let : Fact p.Prime := ⟨hpprime⟩
    let d := CentralExtension.derivedCover f hf hc
    exact False.elim (d.not_dvd_card_multiplier_of_isCyclic_sylow
      (Matrix.PSL3Two.odd_sylow_isCyclic hpprime hp2) hpdvd)

/-- A central two-kernel over `SL₃(2)` vanishes when the source has trivial
2-core and its abelianization is a 2-group. -/
theorem injective_of_twoCore_eq_bot_of_abelianization
    {E : Type*} [Group E] [Finite E]
    (f : E →* Matrix.PSL3Two.SL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (ha : IsPGroup 2 (E ⧸ commutator E))
    (hcore : pCore 2 E = ⊥) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  rw [← hcore]
  exact le_sSup ⟨inferInstance, sl3Two_central_kernel_isTwoGroup f hf hc ha⟩

namespace ThreeSpaceData

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)

private def pointIndex := {t : G // t ∈ d.space ∧ t ≠ 1}

private def pointCoreInK (t : d.pointIndex) : Subgroup d.K :=
  (ambientCore t.val).subgroupOf d.K

private theorem pointCoreInK_le (t : d.pointIndex) : ambientCore t.val ≤ d.K :=
  le_iSup_of_le t le_rfl

private theorem pointCores_generate_K :
    (⨆ t : d.pointIndex, d.pointCoreInK t) = ⊤ := by
  apply Subgroup.map_injective (f := d.K.subtype) d.K.subtype_injective
  rw [Subgroup.map_iSup]
  simp_rw [pointCoreInK, Subgroup.map_subgroupOf_eq_of_le (d.pointCoreInK_le _)]
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  change (⨆ t : d.pointIndex, ambientCore t.val) = d.K
  rfl

private theorem abelianization_isTwoGroup (h : IsTypeJ4 z) :
    IsPGroup 2 ((d.K ⧸ pCore 2 d.K) ⧸
      commutator (d.K ⧸ pCore 2 d.K)) := by
  let E := d.K ⧸ pCore 2 d.K
  let A := E ⧸ commutator E
  let q₁ : d.K →* E := QuotientGroup.mk' (pCore 2 d.K)
  let q₂ : E →* A := QuotientGroup.mk' (commutator E)
  let f : d.K →* A := q₂.comp q₁
  have hq₁ : Function.Surjective q₁ := QuotientGroup.mk'_surjective _
  have hq₂ : Function.Surjective q₂ := QuotientGroup.mk'_surjective _
  have hf : Function.Surjective f := hq₂.comp hq₁
  classical
  haveI : Finite d.pointIndex := by
    dsimp [pointIndex]
    infer_instance
  haveI : IsMulCommutative A :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  have hgen : (⨆ t : d.pointIndex, d.pointCoreInK t).map f = ⊤ := by
    rw [d.pointCores_generate_K, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hf
  have hp : ∀ t : d.pointIndex, IsPGroup 2 ((d.pointCoreInK t).map f) := by
    intro t
    haveI : IsExtraspecial 2 (ambientCore t.val) :=
      IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient t.val)
        (d.point_type h t.property.1 t.property.2).extraspecial
    have hpQ : IsPGroup 2 (ambientCore t.val) := IsExtraspecial.isPGroup 2 (ambientCore t.val)
    have hpK : IsPGroup 2 (d.pointCoreInK t) :=
      hpQ.of_equiv (Subgroup.subgroupOfEquivOfLe (d.pointCoreInK_le t)).symm
    exact hpK.map f
  have hn : ∀ t u : d.pointIndex,
      (d.pointCoreInK t).map f ≤ normalizer ((d.pointCoreInK u).map f : Set A) := by
    intro t u
    exact (le_centralizer_iff.mpr (by
      intro a ha b hb
      exact mul_comm b a)).trans (centralizer_le_normalizer _)
  have hA0 := Theory.GroupTheory.isPGroup_iSup_of_normalizes
      (fun t : d.pointIndex => (d.pointCoreInK t).map f) hp hn
  have hA : IsPGroup 2 (⊤ : Subgroup A) := by
    rw [← hgen, Subgroup.map_iSup]
    exact hA0
  have hA' : IsPGroup 2 A := hA.of_equiv Subgroup.topEquiv
  exact hA'

/-- The literal source kernel is exactly the 2-core of the source join.
The proof factors its action on the original three-space through `O₂(K)`;
the quotient action is a central extension of `SL₃(2)`. -/
theorem R_eq_K_twoCore (h : IsTypeJ4 z) : d.R = d.K.pCoreIn 2 := by
  haveI : IsElementaryAbelian 2 d.space := d.elementary
  obtain ⟨a⟩ := MulAut.elementaryEight_equiv_PSL3 (show Nat.card d.space = 8 from d.card)
  let f₀ : d.K →* Matrix.PSL3Two.SL :=
    (Matrix.PSL3Two.equiv.symm.toMonoidHom).comp
      (a.toMonoidHom.comp d.KAction)
  have hcoreK : pCore 2 d.K ≤ d.KAction.ker := by
    intro k hk
    rw [d.KAction_ker]
    have hk' : (k : G) ∈ d.K.pCoreIn 2 := mem_map_of_mem d.K.subtype hk
    exact (d.K_twoCore_le_R h) hk'
  haveI : ((pCore 2 d.K) : Subgroup d.K).Normal := inferInstance
  let f : (d.K ⧸ pCore 2 d.K) →* Matrix.PSL3Two.SL :=
    QuotientGroup.lift (pCore 2 d.K) f₀ (fun k hk => by
      have hk' : d.KAction k = 1 := hcoreK hk
      simp [f₀, hk'])
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨k, hk⟩ := d.KAction_surjective h (a.symm (Matrix.PSL3Two.equiv y))
    refine ⟨QuotientGroup.mk' (pCore 2 d.K) k, ?_⟩
    change Matrix.PSL3Two.equiv.symm (a (d.KAction k)) = y
    rw [hk, a.apply_symm_apply, Matrix.PSL3Two.equiv.symm_apply_apply]
  have hc : f.ker ≤ center (d.K ⧸ pCore 2 d.K) := by
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 d.K) x
    have hk0 : d.KAction k = 1 := by
      have hfk : f (QuotientGroup.mk' (pCore 2 d.K) k) = 1 := hx
      have hfeq := congrArg Matrix.PSL3Two.equiv.toMonoidHom hfk
      simpa [f, f₀] using hfeq
    have hkR : k ∈ d.R.subgroupOf d.K := by
      have hkKer : k ∈ d.KAction.ker := by
        change d.KAction k = 1
        exact hk0
      rw [d.KAction_ker] at hkKer
      exact hkKer
    apply mem_center_iff.mpr
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 d.K) y
    let lG : G := l
    let kG : G := k
    have hlK : lG ∈ d.K := l.property
    have hkG : kG ∈ d.R := hkR
    have hcomm₀ : ⁅lG, kG⁆ ∈ ⁅d.K, d.S⁆ :=
      commutator_mem_commutator hlK hkG.2
    have hcomm₁R : ⁅lG, kG⁆ ∈ d.R.pCoreIn 2 :=
      d.commutator_K_S_le_R_twoCore h hcomm₀
    have hcomm₁ : ⁅lG, kG⁆ ∈ d.K.pCoreIn 2 := by
      rw [d.K_twoCore_eq_R_twoCore h]
      exact hcomm₁R
    have hcomm₂ : ⁅l, (⟨kG, hkG.1⟩ : d.K)⁆ ∈ pCore 2 d.K := by
      change ⁅(l : G), (kG : G)⁆ ∈ (pCore 2 d.K).map d.K.subtype at hcomm₁
      rw [Subgroup.mem_map] at hcomm₁
      obtain ⟨u, hu, hval⟩ := hcomm₁
      have heq : u = ⁅l, (⟨kG, hkG.1⟩ : d.K)⁆ := by
        apply d.K.subtype_injective
        simpa using hval
      exact heq ▸ hu
    let q : d.K →* (d.K ⧸ pCore 2 d.K) := QuotientGroup.mk' (pCore 2 d.K)
    have hcommq : ⁅QuotientGroup.mk' (pCore 2 d.K) l,
        QuotientGroup.mk' (pCore 2 d.K) (⟨kG, hkG.1⟩ : d.K)⁆ = 1 := by
      have hq : q ⁅l, (⟨kG, hkG.1⟩ : d.K)⁆ = 1 :=
        (QuotientGroup.eq_one_iff (G := d.K) (N := pCore 2 d.K) _).mpr hcomm₂
      simpa only [map_commutatorElement] using hq
    have hcommute := commutatorElement_eq_one_iff_mul_comm.mp hcommq
    exact hcommute
  have hinj : Function.Injective f :=
    injective_of_twoCore_eq_bot_of_abelianization f hf hc
      (d.abelianization_isTwoGroup h) (pCore_quotient_pCore_eq_bot 2)
  have hR : d.R ≤ d.K.pCoreIn 2 := by
    intro x hx
    let k : d.K := ⟨x, hx.1⟩
    have hk0 : d.KAction k = 1 := by
      have hkKer : k ∈ d.KAction.ker := by
        rw [d.KAction_ker]
        exact hx
      exact MonoidHom.mem_ker.mp hkKer
    have hq0 : QuotientGroup.mk' (pCore 2 d.K) k = 1 := by
      apply hinj
      simp [f, f₀, hk0]
    have hkcore : k ∈ pCore 2 d.K :=
      (QuotientGroup.eq_one_iff (G := d.K) (N := pCore 2 d.K) _).mp hq0
    exact mem_map_of_mem d.K.subtype hkcore
  exact le_antisymm hR (d.K_twoCore_le_R h)

end ThreeSpaceData
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

end
