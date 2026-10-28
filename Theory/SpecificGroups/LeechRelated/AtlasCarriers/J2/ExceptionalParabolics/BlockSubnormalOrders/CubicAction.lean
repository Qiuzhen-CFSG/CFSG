module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockSubnormalOrders.CubicCertificates
import Mathlib.Tactic.FinCases

/-!
# Cubic commutator bounds in the actual second Hall--Janko normalizer

The nine odd representatives form a subgroup of order nine. Since the full
normalizer has order 1152, this subgroup is Sylow at three. Every cubic element
is therefore conjugate inside the normalizer to one of the eight nonidentity
representatives. For each representative the imported point checks give
thirteen distinct commutators with the literal nonabelian radical of order 64.
Normality of that radical transports the bound along Sylow conjugacy.

All subgroups and conjugations are inside `Seed.p₂` in the exact ATLAS carrier.
No abelian replacement of the radical or abstract replacement of its action is
used. Source application: Aschbacher--Smith 2.3.9(7), printed p.526; local group
GLS3 Table 5.3g. Witness provenance is recorded in `CubicCertificates`.
-/

public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockSubnormalOrders
open Subgroup Theory.GroupTheory Seed PairNormalizer
open PairNormalizer.CandidateQuotient PairNormalizer.RadicalData
open GeneratorPair.SecondOrbitCertificate
open scoped commutatorElement Pointwise

private def pInclusion : p₂ →* Equiv.Perm (Fin 100) := inclusion.comp p₂.subtype

private theorem generator_inclusion (i : Fin 3) :
    inclusion (normalizerGenerator i) =
      ![SylowData.tTable, QuotientData.oddTable 0, QuotientData.oddTable 1] i := by
  fin_cases i
  · exact (sGenerator_inclusion 3).trans (by decide +kernel)
  · exact oddGenerator_inclusion 0
  · exact oddGenerator_inclusion 1

private def nineRep (i : Fin 9) : p₂ :=
  ⟨evalWord normalizerGenerator (repWord (i.castLE (by decide))), by
    have hw (w : List (Fin 3)) : evalWord normalizerGenerator w ∈ p₂ := by
      induction w with
      | nil => exact p₂.one_mem
      | cons j w ih => exact p₂.mul_mem (normalizerGenerator_mem_p₂ j) ih
    exact hw _⟩

private theorem nineRep_inclusion (i : Fin 9) :
    pInclusion (nineRep i) = repTable (i.castLE (by decide)) := by
  have hw (w : List (Fin 3)) : inclusion (evalWord normalizerGenerator w) =
      evalWord ![SylowData.tTable, QuotientData.oddTable 0, QuotientData.oddTable 1] w := by
    induction w with
    | nil => exact map_one inclusion
    | cons j w ih => rw [evalWord, map_mul, generator_inclusion, ih, evalWord]
  exact hw (repWord (i.castLE (by decide)))

private theorem nineRep_mul (i j : Fin 9) : nineRep i * nineRep j = nineRep (nineMul i j) := by
  apply Subtype.ext
  apply inclusion_injective
  change pInclusion (nineRep i * nineRep j) = pInclusion (nineRep (nineMul i j))
  rw [map_mul, nineRep_inclusion, nineRep_inclusion, nineRep_inclusion,
    repTable_mul, nine_mulIndex, nine_radicalFactor]
  have hq : qTable 0 = 1 := (qElement_inclusion 0).symm
  rw [hq, one_mul]

private theorem nineRep_inv (i : Fin 9) : nineRep (nineInv i) = (nineRep i)⁻¹ := by
  apply mul_left_cancel (a := nineRep i)
  rw [mul_inv_cancel, nineRep_mul, nineMul_inv]
  rfl

private theorem nineRep_injective : Function.Injective nineRep := by
  intro i j h
  apply nine_key_injective
  have he := congrArg pInclusion h
  rw [nineRep_inclusion, nineRep_inclusion] at he
  exact congrArg (fun p : Equiv.Perm (Fin 100) => (p 0, p 1, p 2)) he

private def nineGroup : Subgroup p₂ where
  carrier := Set.range nineRep
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨nineMul i j, (nineRep_mul i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨nineInv i, nineRep_inv i⟩

private theorem card_nineGroup : Nat.card nineGroup = 9 := by
  let e : Fin 9 ≃ nineGroup := Equiv.ofBijective (fun i => ⟨nineRep i, ⟨i, rfl⟩⟩)
    ⟨fun i j h => nineRep_injective (congrArg Subtype.val h), by
      rintro ⟨x, i, rfl⟩
      exact ⟨i, rfl⟩⟩
  exact (Nat.card_congr e.symm).trans (Nat.card_fin 9)

private def threeSylow : Sylow 3 p₂ :=
  (IsPGroup.of_card (n := 2) card_nineGroup).toSylow (by
    have h := nineGroup.card_mul_index
    rw [card_nineGroup, card_p₂] at h
    have hi : nineGroup.index = 128 := by omega
    rw [hi]
    decide)

private def qRep (i : Fin 64) : p₂ := ⟨qElement i, q₂.le_normalizer (qElement_mem i)⟩

private theorem nineRep_commutator_card (r : Fin 9) (hr : r ≠ 0) :
    12 < Nat.card (⁅q₂.subgroupOf p₂, zpowers (nineRep r)⁆ : Subgroup p₂) := by
  let f : Fin 13 → (⁅q₂.subgroupOf p₂, zpowers (nineRep r)⁆ : Subgroup p₂) :=
    fun i => ⟨⁅qRep (cubicInput r i), nineRep r⁆,
      commutator_mem_commutator (qElement_mem _) (mem_zpowers _)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply cubicCommKey_injective r hr
    have h := congrArg (fun c : (⁅q₂.subgroupOf p₂, zpowers (nineRep r)⁆ : Subgroup p₂) =>
      pInclusion c.val) hij
    change pInclusion ⁅qRep (cubicInput r i), nineRep r⁆ =
      pInclusion ⁅qRep (cubicInput r j), nineRep r⁆ at h
    rw [map_commutatorElement, map_commutatorElement, nineRep_inclusion] at h
    have hq (k : Fin 64) : pInclusion (qRep k) = qTable k := qElement_inclusion k
    rw [hq, hq] at h
    exact congrArg (fun p : Equiv.Perm (Fin 100) => (p 0, p 1)) h
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at h
  omega

/-- Every cubic element of the literal full normalizer moves at least thirteen
radical elements to distinct commutators. -/
theorem cubic_commutator_card (x : p₂) (hx : orderOf x = 3) :
    12 < Nat.card (⁅q₂.subgroupOf p₂, zpowers x⁆ : Subgroup p₂) := by
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx]; rfl)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq p₂ T threeSylow
  have hm : MulAut.conj g x ∈ (threeSylow : Subgroup p₂) := by
    rw [← hg]
    change MulAut.conj g x ∈ (MulAut.conj g • (T : Subgroup p₂))
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) T (hT (mem_zpowers x))
  obtain ⟨i, hi⟩ := hm
  have hi0 : i ≠ 0 := by
    intro he
    subst i
    have hx1 : MulAut.conj g x = 1 := hi.symm
    have : x = 1 := (MulAut.conj g).injective (hx1.trans (map_one (MulAut.conj g)).symm)
    rw [this, orderOf_one] at hx
    norm_num at hx
  have he : (⁅q₂.subgroupOf p₂, zpowers x⁆ : Subgroup p₂).map (MulAut.conj g) =
      ⁅q₂.subgroupOf p₂, zpowers (nineRep i)⁆ := by
    rw [map_commutator, Subgroup.Normal.map_conj_eq, MonoidHom.map_zpowers]
    change ⁅q₂.subgroupOf p₂, zpowers (MulAut.conj g x)⁆ = _
    rw [← hi]
  calc
    12 < Nat.card (⁅q₂.subgroupOf p₂, zpowers (nineRep i)⁆ : Subgroup p₂) :=
      nineRep_commutator_card i hi0
    _ = Nat.card ((⁅q₂.subgroupOf p₂, zpowers x⁆ : Subgroup p₂).map (MulAut.conj g)) :=
      congrArg (fun U : Subgroup p₂ => Nat.card U) he.symm
    _ = _ := Subgroup.card_map_of_injective (MulAut.conj g).injective

end Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockSubnormalOrders
