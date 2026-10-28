module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.CoreIdentification
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.Group.Conj

/-!
# The six-element Levi complement of the first binary G₂ parabolic

The short-root involution and its product with the Weyl reflection give an
explicit copy of the dihedral group of order six. The five-root core fixes the
coordinate plane pointwise, whereas this Levi group acts faithfully on it.
Together they generate the first parabolic and intersect trivially. Thus the
parabolic has order 192 and its quotient by the two-core is the actual Levi
quotient.

The homomorphism calculation uses the dihedral relations, and the plane checks
use the root maps from the licensed ATLAS port. Source: Aschbacher–Smith,
Lemma 14.2.21, printed p.988 (combined 1 March 2004 manuscript).
-/

@[expose] public section

namespace Atlas.G2.BinaryParabolicPair
open Atlas.G2.Explicit BinaryCore Atlas.SplitOctonion
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def leviWord : DihedralGroup 3 → Model (ZMod 2)
  | .r i => cubicActor ^ i.val
  | .sr i => shortRoot * cubicActor ^ i.val

private def leviRotation : Multiplicative (ZMod 3) →* Model (ZMod 2) where
  toFun i := cubicActor ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change cubicActor ^ (i.toAdd + j.toAdd).val =
      cubicActor ^ i.toAdd.val * cubicActor ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ cubicActor_cube).symm

private theorem leviWord_mul (x y : DihedralGroup 3) :
    leviWord (x * y) = leviWord x * leviWord y := by
  have dd : shortRoot * shortRoot = 1 := by simpa [pow_two] using shortRoot_sq
  have di : shortRoot⁻¹ = shortRoot := inv_eq_of_mul_eq_one_right dd
  have wi : (weylS : Model (ZMod 2))⁻¹ = weylS :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using (weylS_sq (K := ZMod 2)))
  have hc : shortRoot * cubicActor * shortRoot⁻¹ = cubicActor⁻¹ := by
    simp only [cubicActor, mul_inv_rev, wi, di, ← mul_assoc, dd, one_mul]
  have hswap (i : Multiplicative (ZMod 3)) :
      leviRotation i * shortRoot = shortRoot * (leviRotation i)⁻¹ := by
    have hh : shortRoot * leviRotation i * shortRoot⁻¹ = (leviRotation i)⁻¹ := by
      change shortRoot * cubicActor ^ i.toAdd.val * shortRoot⁻¹ =
        (cubicActor ^ i.toAdd.val)⁻¹
      rw [← conj_pow, hc, inv_pow]
    calc
      _ = (shortRoot * shortRoot) * leviRotation i * shortRoot := by rw [dd, one_mul]
      _ = shortRoot * (shortRoot * leviRotation i * shortRoot⁻¹) := by
        rw [di]; simp only [mul_assoc]
      _ = _ := by rw [hh]
  cases x with
  | r i =>
    cases y with
    | r j => exact leviRotation.map_mul (.ofAdd i) (.ofAdd j)
    | sr j =>
      change shortRoot * leviRotation (.ofAdd (j - i)) =
        leviRotation (.ofAdd i) * (shortRoot * leviRotation (.ofAdd j))
      rw [← mul_assoc, hswap, mul_assoc, sub_eq_add_neg]
      change shortRoot * leviRotation ((.ofAdd j) * (.ofAdd i)⁻¹) =
        shortRoot * ((leviRotation (.ofAdd i))⁻¹ * leviRotation (.ofAdd j))
      rw [map_mul, map_inv]
      congr 1
      simpa only [map_inv] using
        (Commute.map (Commute.all (.ofAdd j) ((.ofAdd i)⁻¹)) leviRotation).eq
  | sr i =>
    cases y with
    | r j =>
      change shortRoot * leviRotation ((.ofAdd i) * (.ofAdd j)) =
        shortRoot * leviRotation (.ofAdd i) * leviRotation (.ofAdd j)
      rw [map_mul, mul_assoc]
    | sr j =>
      change leviRotation (.ofAdd (j - i)) =
        (shortRoot * leviRotation (.ofAdd i)) * (shortRoot * leviRotation (.ofAdd j))
      rw [mul_assoc shortRoot, ← mul_assoc (leviRotation (.ofAdd i)), hswap,
        ← mul_assoc shortRoot, ← mul_assoc shortRoot shortRoot, dd, one_mul,
        sub_eq_add_neg]
      change leviRotation ((.ofAdd j) * (.ofAdd i)⁻¹) =
        (leviRotation (.ofAdd i))⁻¹ * leviRotation (.ofAdd j)
      rw [map_mul, map_inv]
      simpa only [map_inv] using
        (Commute.map (Commute.all (.ofAdd j) ((.ofAdd i)⁻¹)) leviRotation).eq

/-- The explicit six-element Levi group, in the original octonion model. -/
def leviHom : DihedralGroup 3 →* Model (ZMod 2) where
  toFun := leviWord
  map_one' := by change cubicActor ^ 0 = 1; exact pow_zero _
  map_mul' := by exact leviWord_mul

theorem leviHom_mem_first (x : DihedralGroup 3) : leviHom x ∈ firstParabolic := by
  cases x with
  | r i => exact firstParabolic.pow_mem cubicActor_mem _
  | sr i =>
    exact firstParabolic.mul_mem
      (unipotent_le_firstParabolic shortRoot_mem_unipotent)
      (firstParabolic.pow_mem cubicActor_mem _)

private theorem embedding_fixes_plane (x : Coordinates) (i : Fin 2) :
    (embedding x).val (basisVector (i.castLE (by decide))) = basisVector (i.castLE (by decide)) := by
  have hA : ∀ (a : ZMod 2) (j : Fin 2), rootAApply a (basisVector (j.castLE (by decide))) = basisVector (j.castLE (by decide)) := by
    decide +kernel
  have hB : ∀ (a : ZMod 2) (j : Fin 2), rootBApply a (basisVector (j.castLE (by decide))) = basisVector (j.castLE (by decide)) := by
    decide +kernel
  have hC : ∀ (a : ZMod 2) (j : Fin 2), rootCApply a (basisVector (j.castLE (by decide))) = basisVector (j.castLE (by decide)) := by
    decide +kernel
  have hD : ∀ (a : ZMod 2) (j : Fin 2), rootDApply a (basisVector (j.castLE (by decide))) = basisVector (j.castLE (by decide)) := by
    decide +kernel
  have hE : ∀ (a : ZMod 2) (j : Fin 2), rootEApply a (basisVector (j.castLE (by decide))) = basisVector (j.castLE (by decide)) := by
    decide +kernel
  change (rootA x.a * rootB x.b * rootC x.c * rootD x.d * rootE x.e * rootF 0).val _ = _
  rw [rootF_zero, mul_one]
  change rootAApply x.a (rootBApply x.b (rootCApply x.c
    (rootDApply x.d (rootEApply x.e (basisVector (i.castLE (by decide))))))) = _
  rw [hE, hD, hC, hB, hA]

private theorem leviWord_faithful_plane (x : DihedralGroup 3)
    (hx : ∀ i : Fin 2, (leviWord x).val (basisVector (i.castLE (by decide))) = basisVector (i.castLE (by decide))) :
    x = 1 := by
  have he : ∀ x : DihedralGroup 3, (∀ i : Fin 2, ∀ j : Fin 8,
      (leviWord x).val (basisVector (i.castLE (by decide))) j = basisVector (i.castLE (by decide)) j) → x=1 := by
    decide +kernel
  exact he x (fun i j => congrFun (hx i) j)

theorem leviHom_injective : Function.Injective leviHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply leviWord_faithful_plane
  intro i
  have he := MonoidHom.mem_ker.mp hx
  change leviWord x = 1 at he
  rw [he]
  rfl

theorem leviHom_mem_core_iff (x : DihedralGroup 3) : leviHom x ∈ core ↔ x=1 := by
  constructor
  · rintro ⟨c,hc⟩
    apply leviWord_faithful_plane
    intro i
    rw [show leviWord x = embedding c from hc.symm]
    exact embedding_fixes_plane c i
  · rintro rfl
    rw [map_one]
    exact core.one_mem

theorem leviHom_short : leviHom (.sr 0) = shortRoot := by
  change shortRoot * cubicActor ^ 0 = shortRoot
  simp

theorem leviHom_reflection : leviHom (.sr 1) = (weylS : Model (ZMod 2)) := by
  change shortRoot * cubicActor ^ 1 = weylS
  rw [pow_one, cubicActor, ← mul_assoc, ← pow_two, shortRoot_sq, one_mul]

theorem firstParabolic_eq_core_sup_levi : firstParabolic = core ⊔ leviHom.range := by
  apply le_antisymm
  · apply sup_le
    · rw [unipotent_eq_core_sup]
      apply sup_le le_sup_left
      apply (Subgroup.closure_le _).mpr
      rintro g (rfl : g=shortRoot)
      exact Subgroup.mem_sup_right ⟨.sr 0,leviHom_short⟩
    · apply (Subgroup.closure_le _).mpr
      rintro g (rfl : g=weylS)
      exact Subgroup.mem_sup_right ⟨.sr 1,leviHom_reflection⟩
  · apply sup_le core_le_firstParabolic
    rintro g ⟨x,rfl⟩
    exact leviHom_mem_first x

theorem levi_le_first : leviHom.range ≤ firstParabolic := by
  rintro g ⟨x,rfl⟩
  exact leviHom_mem_first x

theorem core_levi_complement :
    (core.subgroupOf firstParabolic).IsComplement' (leviHom.range.subgroupOf firstParabolic) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.mpr
    intro g hg hL
    obtain ⟨x,hx⟩ := hL
    have hxc : leviHom x ∈ core := hx ▸ hg
    have he := (leviHom_mem_core_iff x).mp hxc
    apply Subtype.ext
    change firstParabolic.subtype g = 1
    rw [← hx,he,map_one]
  · rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ Subgroup.le_normalizer_of_normal,
      ← Subgroup.subgroupOf_sup core_le_firstParabolic levi_le_first,
      ← firstParabolic_eq_core_sup_levi, Subgroup.subgroupOf_self]
    rfl

theorem card_firstParabolic : Nat.card firstParabolic = 192 := by
  have hc := core_levi_complement.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe core_le_firstParabolic).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe levi_le_first).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective leviHom_injective).toEquiv,
    card_core] at hc
  have hd : Nat.card (DihedralGroup 3) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hd] at hc
  omega

/-- The quotient by the five-root two-core is the actual six-element Levi group. -/
noncomputable def firstParabolicQuotientEquiv :
    firstParabolic ⧸ core.subgroupOf firstParabolic ≃* DihedralGroup 3 :=
  core_levi_complement.symm.QuotientMulEquiv.trans
    ((Subgroup.subgroupOfEquivOfLe levi_le_first).trans
      (MonoidHom.ofInjective leviHom_injective).symm)

/-- The intrinsic two-core has the same embedding as the five-root core. -/
theorem firstParabolic_intrinsic_pCore :
    pCore 2 firstParabolic = core.subgroupOf firstParabolic := by
  apply Subgroup.map_injective firstParabolic.subtype_injective
  change firstParabolic.pCoreIn 2 = _
  rw [firstParabolic_pCore, Subgroup.map_subgroupOf_eq_of_le core_le_firstParabolic]

noncomputable def firstParabolicTwoCoreQuotientEquiv :
    firstParabolic ⧸ pCore 2 firstParabolic ≃* DihedralGroup 3 :=
  (QuotientGroup.quotientMulEquivOfEq firstParabolic_intrinsic_pCore).trans
    firstParabolicQuotientEquiv

end Atlas.G2.BinaryParabolicPair
