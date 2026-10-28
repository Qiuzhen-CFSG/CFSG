module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.CoreQuotient

/-!
# Faithfulness and the component-module centralizer

Weight-two vectors determine unordered pairs in the natural binary module
of degree eight: their classes cannot differ by the all-one vector. An
actor fixing the natural module therefore fixes all pairs and all points.
This proves faithfulness of the concrete module used by `NaturalEightAction`.

Compatibility identifies the actor kernel with the ambient centralizer.
If the actor is the supplied star marking, the core-quotient theorem gives
`C_I(U_L) = O₂(I) = C_S(U_L)`. The natural coordinates are still an explicit
input here; constructing them from the FF-module alternatives is separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.1 and
the paragraph preceding 15.3.32, printed pp.83 and 1132.
-/

@[expose] public section

open BinaryPermutation
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule
private def pair (i j : Fin 8) : Full (Fin 8) := Pi.single i 1 + Pi.single j 1
private theorem pair_core (i j : Fin 8) : pair i j ∈ core (Fin 8) := by
  simp [pair, mem_core, Finset.sum_add_distrib]
  decide
private theorem permute_pair (g : Equiv.Perm (Fin 8)) (i j : Fin 8) :
    representation (Fin 8) g (pair i j) = pair (g i) (g j) := by
  ext k
  simp [pair, Pi.single_apply, Equiv.symm_apply_eq]

private theorem pair_eq_of_quotient (i j a b : Fin 8) (hij : i ≠ j) (hab : a ≠ b)
    (h : (constants (Fin 8)).mkQ (pair i j) = (constants (Fin 8)).mkQ (pair a b)) :
    i = a ∨ i = b := by
  have hc : pair i j - pair a b ∈ constants (Fin 8) :=
    (Submodule.Quotient.eq (p := constants (Fin 8))).mp h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  have hcalc : ∀ (i j a b : Fin 8) (c : ZMod 2), i ≠ j → a ≠ b →
      (∀ k, c = (pair i j - pair a b) k) → i = a ∨ i = b := by
    decide +kernel
  apply hcalc i j a b c hij hab
  intro k
  have hh := congrFun hc k
  simpa [allOne] using hh

private theorem natural_faithful : Function.Injective (naturalRepresentation (Fin 8)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hp (i j : Fin 8) :
      (constants (Fin 8)).mkQ (pair (g i) (g j)) = (constants (Fin 8)).mkQ (pair i j) := by
    let v : natural (Fin 8) := ⟨(constants (Fin 8)).mkQ (pair i j),
      ⟨pair i j, pair_core i j, rfl⟩⟩
    have h := LinearMap.congr_fun hg v
    have h' := congrArg Subtype.val h
    change (constants (Fin 8)).mkQ (representation (Fin 8) g (pair i j)) =
      (constants (Fin 8)).mkQ (pair i j) at h'
    rwa [permute_pair] at h'
  have hpair (i j : Fin 8) (hij : i ≠ j) : g i = i ∨ g i = j :=
    pair_eq_of_quotient (g i) (g j) i j (g.injective.ne hij) hij (hp i j)
  apply Equiv.ext
  intro i
  have hcalc : ∀ (i x : Fin 8), (∀ j, i ≠ j → x = i ∨ x = j) → x = i := by
    decide +kernel
  exact hcalc i (g i) (hpair i)

open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo Subgroup
universe u
variable {G : Type u} [Group G] {I U : Subgroup G}
/-- The concrete natural representation is faithful, so compatibility
identifies the actor kernel with the actual relative centralizer. -/
theorem naturalActor_ker (a : NaturalEightAction I U) :
    a.actor.ker = (centralizer (U : Set G)).subgroupOf I := by
  ext i
  constructor
  · intro hi u hu
    have hc := a.compatible i ⟨u, hu⟩
    rw [show a.actor i = 1 from hi, map_one] at hc
    have hh : U.normalizerMonoidHom ⟨i, a.normalizes i.property⟩ ⟨u, hu⟩ = ⟨u, hu⟩ :=
      a.coordinates.injective hc
    have h := congrArg Subtype.val hh
    change (i : G) * u * (i : G)⁻¹ = u at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro hi
    change a.actor i = 1
    apply natural_faithful
    rw [map_one]
    apply LinearMap.ext
    intro v
    obtain ⟨u, hu⟩ := a.coordinates.surjective (Multiplicative.ofAdd v)
    have hc := a.compatible i u
    have hh : U.normalizerMonoidHom ⟨i, a.normalizes i.property⟩ u = u := by
      apply Subtype.ext
      change (i : G) * (u : G) * (i : G)⁻¹ = u
      exact mul_inv_eq_iff_eq_mul.mpr ((hi u u.property).symm)
    rw [hh, hu] at hc
    exact (congrArg Multiplicative.toAdd hc).symm


/-- The local centralizer equalities, derived using the original marking.
The action must be constructed separately; these equalities are not its fields. -/
theorem centralizer_componentModule_eq_core [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hcover : EightCoverKernelTwo.{u})
    (a : NaturalEightAction I (d.componentModule I c.L))
    (hactor : a.actor = e.toMonoidHom.comp (d.starMap I)) :
    I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2 ∧
      d.S ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2 := by
  have hk : a.actor.ker = (d.starMap I).ker := by
    ext i
    change a.actor i = 1 ↔ d.starMap I i = 1
    rw [hactor]
    exact e.map_eq_one_iff
  have hCI : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2 := by
    have hm := congrArg (Subgroup.map I.subtype) (naturalActor_ker a)
    rw [hk, starMap_ker d c hnormal hI P hP e hmark hcover, subgroupOf_map_subtype] at hm
    exact (hm.trans (inf_comm _ _)).symm
  refine ⟨hCI, le_antisymm ?_ ?_⟩
  · exact (inf_le_inf_right _ (show d.S ≤ I from hI ▸ le_sup_right)).trans hCI.le
  · exact le_inf (hP ▸ pCoreIn_le_sylow I P) (hCI.ge.trans inf_le_right)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule

end
