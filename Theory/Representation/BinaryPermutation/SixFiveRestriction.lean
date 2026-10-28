module
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Mathlib.Algebra.BigOperators.Fin
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair.Coordinates

/-!
# Restricting the six-letter natural module to the marked five-letter subgroup

Extend an even five-letter vector by zero at the sixth letter, then take
its class in the six-letter natural module. A vector in the kernel is
constant and has last coordinate zero, so vanishes. Both modules have
dimension four. This constructs the equivalence and proves equivariance
under the literal FivePair.fiveEquiv. Conjugating both the actor and the
module gives the same identification for the source's chosen pair.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), §B.3 and
13.5.14(3–4), printed p.919. No normalization by the original Sylow is
required to restrict to this five-letter subgroup.
-/

@[expose] public section
namespace BinaryPermutation.SixFiveRestriction

/-- Extend the five-letter even core by zero in the sixth coordinate. -/
def extendZero : core (Fin 5) →ₗ[ZMod 2] core (Fin 6) where
  toFun v := ⟨Fin.lastCases 0 v.val, by
    rw [mem_core, Fin.sum_univ_castSucc]
    simpa only [Fin.lastCases_castSucc, Fin.lastCases_last, add_zero] using
      (show (∑ i, v.val i) = 0 from v.property)⟩
  map_add' v w := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Submodule.coe_add,
      Pi.add_apply, add_zero]
  map_smul' c v := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Submodule.coe_smul,
      Pi.smul_apply, RingHom.id_apply, smul_zero]

@[simp] theorem extendZero_castSucc (v : core (Fin 5)) (i : Fin 5) :
    (extendZero v).val i.castSucc = v.val i := by simp only [extendZero, LinearMap.coe_mk, AddHom.coe_mk, Fin.lastCases_castSucc]

@[simp] theorem extendZero_last (v : core (Fin 5)) :
    (extendZero v).val (Fin.last 5) = 0 := by simp only [extendZero, LinearMap.coe_mk, AddHom.coe_mk, Fin.lastCases_last]

/-- Zero extension followed by the actual six-letter natural quotient. -/
def toNatural : core (Fin 5) →ₗ[ZMod 2] natural (Fin 6) :=
  (coreToNatural (Fin 6)).comp extendZero

theorem toNatural_injective : Function.Injective toNatural := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hc : (extendZero v).val ∈ constants (Fin 6) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrArg Subtype.val hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  have hz : c = 0 := by
    have h := congrFun hc (Fin.last 5)
    simpa only [Pi.smul_apply, allOne, smul_eq_mul, mul_one, extendZero_last] using h
  apply Subtype.ext
  funext i
  have h := congrFun hc i.castSucc
  simpa [hz] using h.symm

theorem toNatural_bijective : Function.Bijective toNatural := by
  refine ⟨toNatural_injective, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp toNatural_injective
  rw [finrank_core, finrank_natural_even (Fin 6) (by decide)]
  rfl

/-- The four-dimensional six-letter natural module, restricted at its fixed
last letter, is the five-letter even core. -/
noncomputable def coreEquivNaturalSix : core (Fin 5) ≃ₗ[ZMod 2] natural (Fin 6) :=
  LinearEquiv.ofBijective toNatural toNatural_bijective

theorem extendZero_equivariant (g : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 5))
    (hg : ∀ i : Fin 5, g i.castSucc = (q i).castSucc) (hl : g (Fin.last 5) = Fin.last 5)
    (v : core (Fin 5)) :
    extendZero (coreRepresentation (Fin 5) q v) = coreRepresentation (Fin 6) g (extendZero v) := by
  apply Subtype.ext
  funext i
  obtain ⟨i,rfl⟩ := g.surjective i
  change (extendZero (coreRepresentation (Fin 5) q v)).val (g i) =
    (extendZero v).val (g.symm (g i))
  rw [g.symm_apply_apply]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [hl, extendZero_last, extendZero_last]
  · rw [hg, extendZero_castSucc, extendZero_castSucc]
    change v.val (q.symm (q j)) = v.val j
    rw [q.symm_apply_apply]

theorem coreEquivNaturalSix_equivariant (g : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 5))
    (hg : ∀ i : Fin 5, g i.castSucc = (q i).castSucc) (hl : g (Fin.last 5) = Fin.last 5)
    (v : core (Fin 5)) :
    coreEquivNaturalSix (coreRepresentation (Fin 5) q v) =
      naturalRepresentation (Fin 6) g (coreEquivNaturalSix v) := by
  change coreToNatural (Fin 6) (extendZero (coreRepresentation (Fin 5) q v)) = _
  rw [extendZero_equivariant g q hg hl, coreToNatural_equivariant]
  rfl

open Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-- The restriction in the direction used by a marked source module. -/
noncomputable def naturalSixEquivCoreFive : natural (Fin 6) ≃ₗ[ZMod 2] core (Fin 5) :=
  coreEquivNaturalSix.symm

theorem naturalSixEquivCoreFive_equivariant (g : FivePair.five) (v : natural (Fin 6)) :
    naturalSixEquivCoreFive (naturalRepresentation (Fin 6) g.val v) =
      alternatingCoreRepresentation (Fin 5) (FivePair.fiveEquiv g)
        (naturalSixEquivCoreFive v) := by
  obtain ⟨u,rfl⟩ := coreEquivNaturalSix.surjective v
  have he := coreEquivNaturalSix_equivariant g.val (FivePair.fiveEquiv g).val
    (FivePair.fiveEquiv_apply g) g.property.1 u
  change coreEquivNaturalSix.symm _ = _
  rw [← he, coreEquivNaturalSix.symm_apply_apply]
  simp only [naturalSixEquivCoreFive, coreEquivNaturalSix.symm_apply_apply]
  rfl

/-- Undo the source's chosen conjugation before restricting the module. -/
noncomputable def conjugateModuleEquiv (a : Equiv.Perm (Fin 6)) :
    natural (Fin 6) ≃ₗ[ZMod 2] core (Fin 5) :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv
    ((naturalRepresentation (Fin 6)).asGroupHom a⁻¹)).trans naturalSixEquivCoreFive

/-- The same conjugate is undone in the actual actor subgroup. -/
noncomputable def conjugateActorEquiv (a : Equiv.Perm (Fin 6)) :
    FivePair.five.map (MulAut.conj a).toMonoidHom ≃* alternatingGroup (Fin 5) :=
  ((MulAut.conj a).subgroupMap FivePair.five).symm.trans FivePair.fiveEquiv

theorem conjugateModuleEquiv_equivariant (a : Equiv.Perm (Fin 6))
    (g : FivePair.five.map (MulAut.conj a).toMonoidHom) (v : natural (Fin 6)) :
    conjugateModuleEquiv a (naturalRepresentation (Fin 6) g.val v) =
      alternatingCoreRepresentation (Fin 5) (conjugateActorEquiv a g)
        (conjugateModuleEquiv a v) := by
  obtain ⟨g,rfl⟩ := ((MulAut.conj a).subgroupMap FivePair.five).surjective g
  change naturalSixEquivCoreFive
      (naturalRepresentation (Fin 6) a⁻¹ (naturalRepresentation (Fin 6) (a*g.val*a⁻¹) v)) = _
  have he : naturalRepresentation (Fin 6) a⁻¹
      (naturalRepresentation (Fin 6) (a*g.val*a⁻¹) v) =
      naturalRepresentation (Fin 6) g.val (naturalRepresentation (Fin 6) a⁻¹ v) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  rw [he,naturalSixEquivCoreFive_equivariant]
  change _ = alternatingCoreRepresentation (Fin 5)
    (FivePair.fiveEquiv (((MulAut.conj a).subgroupMap FivePair.five).symm
      (((MulAut.conj a).subgroupMap FivePair.five) g)))
    (naturalSixEquivCoreFive (naturalRepresentation (Fin 6) a⁻¹ v))
  rw [MulEquiv.symm_apply_apply]
end BinaryPermutation.SixFiveRestriction
