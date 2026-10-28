module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Transport
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Binary point centralizers and their five-letter Borel preimages

Conjugation transports the literal column-vector stabilizer. Given an actual
surjection from that stabilizer to S₅ with intrinsic two-core kernel, its
Sylow image fixes a letter because five is odd. Pulling back this letter's
stabilizer and embedding in the matrix group constructs an overgroup of the
original Sylow with relative index three. Its two-residual fixes the same
binary vector.

The centralizer quotient is explicitly conditional here. The reference
vector 1327 matches the separately published parabolic module coordinates;
its stabilizer comparison and the uniform Sylow-fixed orbit are separate
native calculations. No F₄-line stabilizer replaces the binary stabilizer.

Source: Aschbacher--Smith, 14.4.2(6) and 14.4.12, printed pp.1006 and
1011--1012; H.12.1(5,9), printed pp.393--394 (1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native

/-- Reference vector shared with the native parabolic module coordinates. -/
def referenceVector : Space := fun i => if (1327 : ℕ).testBit i.val then 1 else 0

theorem referenceVector_ne_zero : referenceVector ≠ 0 := by decide +kernel

@[simp] theorem mem_pointCentralizer (v : Space) (g : Model) :
    g ∈ pointCentralizer v ↔ action g v = v := Iff.rfl

theorem sylow_le_pointCentralizer (S : Sylow 2 Model) (v : Space)
    (hv : ∀ s : S, action s.val v = v) : (S : Subgroup Model) ≤ pointCentralizer v :=
  fun g hg => hv ⟨g, hg⟩

private theorem action_mul (g h : Model) (v : Space) :
    action (g * h) v = action g (action h v) := by rw [map_mul, Module.End.mul_apply]

private theorem action_inv_cancel (g : Model) (v : Space) :
    action g⁻¹ (action g v) = v := by
  rw [← action_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- Conjugation carries the literal vector stabilizer to the stabilizer of the
transported vector, with the column action retained. -/
theorem pointCentralizer_map_conj (g : Model) (v : Space) :
    (pointCentralizer v).map (MulAut.conj g).toMonoidHom =
      pointCentralizer (action g v) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change action (g * y * g⁻¹) (action g v) = action g v
    rw [action_mul, action_inv_cancel, action_mul, (mem_pointCentralizer v y).mp hy]
  · intro hx
    refine mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · change action (g⁻¹ * x * g) v = v
      rw [action_mul, action_mul, (mem_pointCentralizer (action g v) x).mp hx, action_inv_cancel]
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

noncomputable def pointCentralizerConjEquiv (g : Model) (v : Space) :
    pointCentralizer v ≃* pointCentralizer (action g v) :=
  ((MulAut.conj g).subgroupMap (pointCentralizer v)).trans
    (MulEquiv.subgroupCongr (pointCentralizer_map_conj g v))

/-- The quotient map is retained in the construction of the Borel. -/
noncomputable def pointQuotient (v : Space)
    (e : coreQuotient (pointCentralizer v) ≃* Equiv.Perm (Fin 5)) :
    pointCentralizer v →* Equiv.Perm (Fin 5) := starProjection (pointCentralizer v) e

theorem pointQuotient_surjective (v : Space)
    (e : coreQuotient (pointCentralizer v) ≃* Equiv.Perm (Fin 5)) :
    Function.Surjective (pointQuotient v e) := starProjection_surjective _ e

theorem pointQuotient_ker (v : Space)
    (e : coreQuotient (pointCentralizer v) ≃* Equiv.Perm (Fin 5)) :
    (pointQuotient v e).ker = pCore 2 (pointCentralizer v) := starProjection_ker _ e

/-- Pull back a point stabilizer in the five-letter quotient, then use the
literal embedding of the vector centralizer into the native matrix group. -/
noncomputable def pointBorel (v : Space) (q : pointCentralizer v →* Equiv.Perm (Fin 5))
    (i : Fin 5) : Subgroup Model :=
  ((MulAction.stabilizer (Equiv.Perm (Fin 5)) i).comap q).map
    (pointCentralizer v).subtype

theorem pointBorel_le (v : Space) (q : pointCentralizer v →* Equiv.Perm (Fin 5))
    (i : Fin 5) : pointBorel v q i ≤ pointCentralizer v := map_subtype_le _

/-- In particular the actual Borel residual fixes the original binary vector. -/
theorem borelActor_fixes (v : Space) (q : pointCentralizer v →* Equiv.Perm (Fin 5))
    (i : Fin 5) (x : borelActor (pointBorel v q i)) : action x.val v = v :=
  pointBorel_le v q i (map_subtype_le _ x.property)

private theorem perm_five_sylow_card (P : Sylow 2 (Equiv.Perm (Fin 5))) :
    Nat.card P = 8 := by
  rw [P.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]
  rw [show 120 = 2 ^ 3 * 15 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
  rfl

private theorem perm_five_sylow_borel_index (P : Sylow 2 (Equiv.Perm (Fin 5)))
    (i : Fin 5) (hi : (P : Subgroup (Equiv.Perm (Fin 5))) ≤ MulAction.stabilizer (Equiv.Perm (Fin 5)) i) :
    (P : Subgroup (Equiv.Perm (Fin 5))).relIndex (MulAction.stabilizer (Equiv.Perm (Fin 5)) i) = 3 := by
  have hp := (P : Subgroup (Equiv.Perm (Fin 5))).card_mul_index
  rw [perm_five_sylow_card, Nat.card_perm, Nat.card_fin] at hp
  have hpi : (P : Subgroup (Equiv.Perm (Fin 5))).index = 15 := by norm_num [Nat.factorial] at hp; omega
  have hh := relIndex_mul_index hi
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_fin, hpi] at hh
  omega

/-- Every Sylow image fixes a letter, and the full preimage of its letter
stabilizer has relative index three over the original Sylow. The centralizer
quotient is an explicit premise here, to be discharged by the native calculation. -/
theorem exists_pointBorel_of_quotient (S : Sylow 2 Model) (v : Space)
    (hv : ∀ s : S, action s.val v = v)
    (q : pointCentralizer v →* Equiv.Perm (Fin 5))
    (hq : Function.Surjective q) (hk : q.ker = pCore 2 (pointCentralizer v)) :
    ∃ i : Fin 5, (S : Subgroup Model) ≤ pointBorel v q i ∧
      pointBorel v q i ≤ pointCentralizer v ∧
      (S : Subgroup Model).relIndex (pointBorel v q i) = 3 := by
  let T := S.subtype (sylow_le_pointCentralizer S v hv)
  let P := T.mapSurjective hq
  obtain ⟨i, hi⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card
    (Fin 5) (by simp)
  have hPi : (P : Subgroup _) ≤ MulAction.stabilizer (Equiv.Perm (Fin 5)) i := by
    intro x hx
    exact hi ⟨x, hx⟩
  let K := (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).comap q
  have hTK : (T : Subgroup _) ≤ K := by
    intro x hx
    exact hPi (mem_map_of_mem q hx)
  have hST : (T : Subgroup (pointCentralizer v)).map (pointCentralizer v).subtype = S :=
    map_subgroupOf_eq_of_le (sylow_le_pointCentralizer S v hv)
  refine ⟨i, ?_, pointBorel_le v q i, ?_⟩
  · rw [← hST]
    exact map_mono hTK
  · have hkerT : q.ker ≤ T := by
      rw [hk]
      exact pCore_isPGroup.le_sylow_of_normal T
    have hkerK : q.ker ≤ K := hkerT.trans hTK
    have hm := relIndex_map_map q (T : Subgroup _) K
    rw [sup_of_le_left hkerT, sup_of_le_left hkerK,
      map_comap_eq_self_of_surjective hq] at hm
    have he : (T : Subgroup _).relIndex K = 3 :=
      hm.symm.trans (perm_five_sylow_borel_index P i hPi)
    rw [← hST, pointBorel, relIndex_map_map_of_injective _ _
      (pointCentralizer v).subtype_injective]
    exact he

/-- Application with the literal intrinsic two-core projection. -/
theorem exists_pointBorel_of_equiv (S : Sylow 2 Model) (v : Space)
    (hv : ∀ s : S, action s.val v = v)
    (e : coreQuotient (pointCentralizer v) ≃* Equiv.Perm (Fin 5)) :
    ∃ i : Fin 5, (S : Subgroup Model) ≤ pointBorel v (pointQuotient v e) i ∧
      pointBorel v (pointQuotient v e) i ≤ pointCentralizer v ∧
      (S : Subgroup Model).relIndex (pointBorel v (pointQuotient v e) i) = 3 :=
  exists_pointBorel_of_quotient S v hv _ (pointQuotient_surjective v e)
    (pointQuotient_ker v e)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
