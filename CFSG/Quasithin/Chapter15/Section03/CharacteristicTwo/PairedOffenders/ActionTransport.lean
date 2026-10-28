module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Quotient
public import Theory.Representation.BinaryPermutation.Faithful

/-!
Transport the natural eight-letter module through ambient conjugation and
identify restricted action kernels with the actual module centralizers.
Faithfulness of the deleted permutation action supplies the kernel equality.
These are the action identifications used in the paired configuration in the
proof of [AS, 15.3.25], after 15.3.32(5–6).
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.NaturalEightAction
variable {G : Type*} [Group G] {I U : Subgroup G} (a : NaturalEightAction I U)

include a

/-- Natural coordinates force the actual module to be elementary abelian. -/
theorem elementary : IsElementaryAbelian 2 U where
  toIsMulCommutative := ⟨⟨fun x y => a.coordinates.injective (by simp only [map_mul,mul_comm])⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro u
    apply a.coordinates.injective
    rw [map_pow,map_one]
    change (2 : ℕ) • (a.coordinates u).toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
    exact zero_smul (ZMod 2) _)

/-- Transport the actual natural action through simultaneous ambient conjugation. -/
def conjugate (t : G) : NaturalEightAction (I.conjBy t) (U.conjBy t) := by
  let eI : I ≃* I.conjBy t := (MulAut.conj t).subgroupMap I
  let eU : U ≃* U.conjBy t := (MulAut.conj t).subgroupMap U
  have hn : I.conjBy t ≤ normalizer (U.conjBy t : Set G) := by
    change I.map (MulAut.conj t).toMonoidHom ≤ normalizer (U.map (MulAut.conj t).toMonoidHom : Set G)
    rw [← map_equiv_normalizer_eq]
    exact map_mono a.normalizes
  refine {
    normalizes := hn
    coordinates := eU.symm.trans a.coordinates
    actor := a.actor.comp eI.symm.toMonoidHom
    onto := a.onto.comp eI.symm.surjective
    compatible := ?_ }
  intro i u
  obtain ⟨i,rfl⟩ := eI.surjective i
  obtain ⟨u,rfl⟩ := eU.surjective u
  change a.coordinates (eU.symm ((U.conjBy t).normalizerMonoidHom ⟨eI i,hn (eI i).property⟩ (eU u))) =
    Multiplicative.ofAdd (BinaryPermutation.naturalRepresentation (Fin 8)
      (a.actor (eI.symm (eI i))) (a.coordinates (eU.symm (eU u))).toAdd)
  rw [eI.symm_apply_apply,eU.symm_apply_apply,← a.compatible]
  apply congrArg a.coordinates
  apply eU.injective
  rw [eU.apply_symm_apply]
  apply Subtype.ext
  change (t * (i : G) * t⁻¹) * (t * (u : G) * t⁻¹) * (t * (i : G) * t⁻¹)⁻¹ =
    t * ((i : G) * (u : G) * (i : G)⁻¹) * t⁻¹
  group

/-- Faithfulness identifies every restricted actor kernel with the literal centralizer. -/
theorem restrictActor_kernel (J : Subgroup G) (hJI : J ≤ I) (hUJ : U ≤ J) :
    (a.restrictActor J hJI).ker = centralizer (U.subgroupOf J : Set J) := by
  ext j
  constructor
  · intro hj
    apply mem_centralizer_iff.mpr
    intro u hu
    apply Subtype.ext
    exact a.ker_le_centralizer (mem_map_of_mem I.subtype
      (show inclusion hJI j ∈ a.actor.ker from hj)) u hu
  · intro hj
    apply BinaryPermutation.naturalRepresentation_injective (Fin 8) (by decide)
    rw [map_one]
    apply LinearMap.ext
    intro v
    obtain ⟨u,hu⟩ := a.coordinates.surjective (Multiplicative.ofAdd v)
    have he := a.compatible (inclusion hJI j) u
    have hc : U.normalizerMonoidHom ⟨inclusion hJI j,a.normalizes (hJI j.property)⟩ u = u := by
      apply Subtype.ext
      change (j : G) * (u : G) * (j : G)⁻¹ = u
      have hcomm := congrArg Subtype.val
        (mem_centralizer_iff.mp hj (⟨u,hUJ u.property⟩ : J) u.property)
      change (u : G) * (j : G) = (j : G) * (u : G) at hcomm
      rw [←hcomm,mul_inv_cancel_right]
    rw [hc,hu] at he
    exact (congrArg Multiplicative.toAdd he).symm

omit a in
/-- Intrinsic and ambient centralizer conventions agree on a contained module. -/
theorem restricted_centralizer (J : Subgroup G) (hUJ : U ≤ J) :
    centralizer (U.subgroupOf J : Set J) = (centralizer (U : Set G)).subgroupOf J := by
  ext j
  rw [mem_centralizer_iff]
  constructor
  · intro h u hu
    exact congrArg Subtype.val (h ⟨u,hUJ hu⟩ hu)
  · intro h u hu
    exact Subtype.ext (h u hu)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.NaturalEightAction
