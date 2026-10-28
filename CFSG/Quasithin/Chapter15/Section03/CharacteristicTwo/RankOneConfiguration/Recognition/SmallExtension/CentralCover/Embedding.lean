module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.Bridge

/-!
# Faithful cocycle coordinates on the actual plus image

The commutator cocycles form a homomorphism on every subgroup centralizing Q.
Its kernel is exactly the relative centralizer of L: perfectness kills the
central error after passing from Z(Q) to its noncentral quotient. Consequently
the actual image in I/C_I(L) embeds in the universal dual-cover coordinates.
The lift equation relates this embedding to the original ambient commutator.

Source: Aschbacher--Smith, proof of 15.3.31, printed p.1132, and I.1.5.
-/

@[expose] public section
open Subgroup Representation Representation.OneCohomology
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover

variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {L D I : Subgroup G} {ρ : Representation (ZMod 2) A V}

/-- The actual commutator coordinates are additive in the centralizing actor. -/
def commutatorCocycleHom (m : CenterModel L ρ) (hDZ : ⁅D,L⁆ ≤ coreCenter L)
    (hDQ : D ≤ centralizer (extensionCore L : Set G)) :
    D →* Multiplicative (cocycles (ρ.comp m.actorMap)) where
  toFun x := Multiplicative.ofAdd (commutatorCocycle m hDZ x)
  map_one' := by
    apply Subtype.ext
    funext l
    have hc : centralCommutator hDZ 1 l = 1 := by
      apply Subtype.ext
      simp [centralCommutator]
    change Multiplicative.toAdd (m.coordinates (centralCommutator hDZ 1 l)) = 0
    rw [hc,map_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    funext l
    have hxy : Commute (x : G) ⁅(y : G),(l : G)⁆ :=
      (mem_centralizer_iff.mp (hDQ x.property) _
        (hDZ (commutator_mem_commutator y.property l.property)).1).symm
    have hc : centralCommutator hDZ (x*y) l =
        centralCommutator hDZ y l * centralCommutator hDZ x l := by
      apply Subtype.ext
      change ⁅(x : G) * (y : G),(l : G)⁆ = _
      rw [commutatorElement_mul_left_eq_conj_mul,hxy.eq,mul_inv_cancel_right]
      rfl
    change Multiplicative.toAdd (m.coordinates (centralCommutator hDZ (x*y) l)) = _
    rw [hc,map_mul]
    exact add_comm _ _

/-- The central coefficient quotient loses no nontrivial action on a perfect L. -/
theorem commutatorCocycleHom_ker (m : CenterModel L ρ)
    (hperfect : Group.IsPerfect L) (hDZ : ⁅D,L⁆ ≤ coreCenter L)
    (hDQ : D ≤ centralizer (extensionCore L : Set G)) :
    (commutatorCocycleHom m hDZ hDQ).ker = actionKernel D L := by
  let f := commutatorCocycleHom m hDZ hDQ
  have hc : f.ker.map D.subtype ≤ centralizer (L : Set G) := by
    apply centralizes_of_commutator_centralizes hperfect
    apply commutator_le.mpr
    rintro _ ⟨x,hx,rfl⟩ l hl
    have he := congrArg (fun a : Multiplicative (cocycles (ρ.comp m.actorMap)) =>
      (Multiplicative.toAdd a).val ⟨l,hl⟩) (show f x = 1 from hx)
    apply (m.coordinates_eq_one_iff (centralCommutator hDZ x ⟨l,hl⟩)).mp
    exact Multiplicative.toAdd.injective he
  ext x
  constructor
  · intro hx
    exact hc (mem_map_of_mem D.subtype hx)
  · intro hx
    apply Subtype.ext
    funext l
    have hcomm : centralCommutator hDZ x l = 1 := by
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_iff.mp hx l l.property).symm
    change Multiplicative.toAdd (m.coordinates (centralCommutator hDZ x l)) = 0
    rw [hcomm,map_one]
    rfl

/-- The actual map of a contained subgroup onto its image in I⁺. -/
def subgroupPlusMap [(actionKernel I L).Normal] (hDI : D ≤ I) :
    D →* plusImage I L D where
  toFun x := ⟨plusMap I L ⟨x,hDI x.property⟩,
    mem_map.mpr ⟨⟨x,hDI x.property⟩,x.property,rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext ((plusMap I L).map_mul
    (⟨x,hDI x.property⟩ : I) (⟨y,hDI y.property⟩ : I))

theorem subgroupPlusMap_surjective [(actionKernel I L).Normal] (hDI : D ≤ I) :
    Function.Surjective (subgroupPlusMap (L := L) hDI) := by
  rintro ⟨q,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

theorem subgroupPlusMap_ker [(actionKernel I L).Normal] (hDI : D ≤ I) :
    (subgroupPlusMap (L := L) hDI).ker = actionKernel D L := by
  ext x
  change subgroupPlusMap hDI x = 1 ↔ (x : G) ∈ centralizer (L : Set G)
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff (N := actionKernel I L) (⟨x,hDI x.property⟩ : I)

/-- The actual D⁺ embeds faithfully into cocycles, with its original
commutator formula. Together with `detectedOn_iff_universal_fixed`, this
identifies the precise dual-cover fixed-vector calculation needed by 15.3.31. -/
theorem exists_faithful_cocycle_map [(actionKernel I L).Normal]
    (hDI : D ≤ I) (hIL : I ≤ normalizer (L : Set G))
    (m : CenterModel L ρ) (hperfect : Group.IsPerfect L)
    (hDZ : ⁅D,L⁆ ≤ coreCenter L)
    (hDQ : D ≤ centralizer (extensionCore L : Set G)) :
    ∃ j : plusImage I L D →* Multiplicative (cocycles (ρ.comp m.actorMap)),
      Function.Injective j ∧ ∀ x : D,
        j (subgroupPlusMap hDI x) = Multiplicative.ofAdd (commutatorCocycle m hDZ x) := by
  let : (actionKernel D L).Normal := actionKernel_normal (hDI.trans hIL)
  let e := QuotientGroup.liftEquiv (actionKernel D L)
    (subgroupPlusMap_surjective (L := L) hDI) (subgroupPlusMap_ker hDI).symm
  let f := QuotientGroup.lift (actionKernel D L) (commutatorCocycleHom m hDZ hDQ)
    (commutatorCocycleHom_ker m hperfect hDZ hDQ).ge
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_lift,commutatorCocycleHom_ker m hperfect,
      QuotientGroup.map_mk'_self]
  refine ⟨f.comp e.symm.toMonoidHom, hf.comp e.symm.injective, ?_⟩
  intro x
  have he : e.symm (subgroupPlusMap hDI x) = QuotientGroup.mk' (actionKernel D L) x := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (QuotientGroup.liftEquiv_mk _ _ _ x).symm
  change f (e.symm (subgroupPlusMap hDI x)) = _
  rw [he]
  rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover
