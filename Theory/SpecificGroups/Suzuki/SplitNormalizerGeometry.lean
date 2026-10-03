module

public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry
public import Theory.GroupTheory.DihedralPresentation
public import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# The split torus normalizer in the Suzuki group

The two points fixed by a nonidentity split-torus element determine the torus.
The Weyl involution swaps these points and inverts the torus, so the setwise
stabilizer of the pair is the dihedral normalizer. The two cosets give its order,
and a cyclic generator of the torus together with the Weyl element gives the
dihedral presentation.

Source: Huppert--Blackburn III, XI.3.10(e) and XI.3.12(e).
-/

namespace BenderSuzuki.MatrixGroups

open PFAppendixIII
open scoped Pointwise LinearAlgebra.Projectivization

/-- The Weyl involution, viewed as an element of the concrete Suzuki group. -/
@[expose] public noncomputable def suzukiWeyl (m : ℕ) : SuzukiMatrixGroup m :=
  ⟨SuzukiWeylGL m, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

public theorem suzukiWeyl_sq (m : ℕ) : suzukiWeyl m * suzukiWeyl m = 1 := by
  apply Subtype.ext
  exact External.suzukiWeylGL_mul_self m

public theorem suzukiWeyl_ne_one (m : ℕ) : suzukiWeyl m ≠ 1 := by
  intro h
  have hh := congrArg (fun x : SuzukiMatrixGroup m =>
      (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))) h
  have h00 := congrArg (fun x : GL (Fin 4) (BinaryGaloisField (2 * m + 1)) =>
      (x : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) 0 0) hh
  simp [suzukiWeyl, SuzukiWeylGL, SuzukiWeylMatrix] at h00

public theorem suzukiWeyl_conj_splitTorus (m : ℕ) (t : SuzukiSplitTorus m) :
    suzukiWeyl m * (t : SuzukiMatrixGroup m) * suzukiWeyl m =
      (t : SuzukiMatrixGroup m)⁻¹ := by
  obtain ⟨u, hu⟩ := (mem_suzukiSplitTorus_iff m t).mp t.property
  apply Subtype.ext
  change SuzukiWeylGL m * (t : GL (Fin 4) _) * SuzukiWeylGL m = _
  rw [hu, External.suzukiWeylGL_conj_torus]
  simpa [hu] using (External.suzukiTorusGL_inv m u).symm

public theorem suzukiWeyl_smul_infinity (m : ℕ) :
    suzukiWeyl m • suzukiOvoidInfinity m = suzukiOvoidZero m := by
  apply Subtype.ext
  change (Matrix.GeneralLinearGroup.toLin (suzukiWeyl m).val).toLinearEquiv •
      (suzukiOvoidInfinity m).val = (suzukiOvoidZero m).val
  dsimp [suzukiOvoidInfinity, suzukiOvoidZero]
  simp [suzukiWeyl, SuzukiWeylGL, SuzukiWeylMatrix]
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  simp
  funext i
  fin_cases i <;> rfl

public theorem suzukiWeyl_smul_zero (m : ℕ) :
    suzukiWeyl m • suzukiOvoidZero m = suzukiOvoidInfinity m := by
  apply Subtype.ext
  change (Matrix.GeneralLinearGroup.toLin (suzukiWeyl m).val).toLinearEquiv •
      (suzukiOvoidZero m).val = (suzukiOvoidInfinity m).val
  dsimp [suzukiOvoidInfinity, suzukiOvoidZero]
  simp [suzukiWeyl, SuzukiWeylGL, SuzukiWeylMatrix]
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  simp
  funext i
  fin_cases i <;> rfl

@[expose] public noncomputable def suzukiOvoidPair (m : ℕ) : Set (SuzukiOvoid m) :=
  {suzukiOvoidInfinity m, suzukiOvoidZero m}

private theorem suzukiOvoidPair_mem (m : ℕ) (a : SuzukiOvoid m) :
    a ∈ suzukiOvoidPair m ↔ a = suzukiOvoidInfinity m ∨ a = suzukiOvoidZero m := by
  simp [suzukiOvoidPair]

public theorem suzukiSplitTorus_fixed_pair (m : ℕ) (hm : 0 < m)
    (t : SuzukiMatrixGroup m) (ht : t ∈ SuzukiSplitTorus m)
    (htne : t ≠ 1) (a : SuzukiOvoid m) :
    t • a = a ↔ a ∈ suzukiOvoidPair m := by
  have hpair := (mem_suzukiSplitTorus_iff_fix_pair m t).mp ht
  constructor
  · intro ha
    by_cases hai : a = suzukiOvoidInfinity m
    · exact (suzukiOvoidPair_mem m a).2 (Or.inl hai)
    by_cases haz : a = suzukiOvoidZero m
    · exact (suzukiOvoidPair_mem m a).2 (Or.inr haz)
    exfalso
    exact (suzukiOvoid_at_most_two_fixed m hm t htne _ _ _
      (suzukiOvoidInfinity_ne_zero m) (Ne.symm hai) (Ne.symm haz) hpair.1 hpair.2 ha)
  · intro ha
    rcases (suzukiOvoidPair_mem m a).1 ha with rfl | rfl
    · exact hpair.1
    · exact hpair.2

private theorem suzukiSplitTorus_map_fixed_pair (m : ℕ)
    (g : SuzukiMatrixGroup m) (x : SuzukiMatrixGroup m)
    (hx : x ∈ (SuzukiSplitTorus m).map (MulAut.conj g).toMonoidHom)
    :
    x • (g • suzukiOvoidInfinity m) = g • suzukiOvoidInfinity m ∧
    x • (g • suzukiOvoidZero m) = g • suzukiOvoidZero m := by
  obtain ⟨t, ht, rfl⟩ := hx
  constructor
  · change (g * (t : SuzukiMatrixGroup m) * g⁻¹) •
      (g • suzukiOvoidInfinity m) = g • suzukiOvoidInfinity m
    simpa only [mul_smul, inv_smul_smul] using
      congrArg (g • ·) ((mem_suzukiSplitTorus_iff_fix_pair m t).mp ht).1
  · change (g * (t : SuzukiMatrixGroup m) * g⁻¹) •
      (g • suzukiOvoidZero m) = g • suzukiOvoidZero m
    simpa only [mul_smul, inv_smul_smul] using
      congrArg (g • ·) ((mem_suzukiSplitTorus_iff_fix_pair m t).mp ht).2

/-- The explicit Weyl element has order two. -/
public theorem suzukiWeyl_orderOf (m : ℕ) : orderOf (suzukiWeyl m) = 2 := by
  exact orderOf_eq_prime (by simpa [pow_two] using suzukiWeyl_sq m)
    (suzukiWeyl_ne_one m)

public theorem suzukiWeyl_inv (m : ℕ) : (suzukiWeyl m)⁻¹ = suzukiWeyl m :=
  inv_eq_of_mul_eq_one_right (suzukiWeyl_sq m)

public theorem suzukiWeyl_not_mem_splitTorus (m : ℕ) :
    suzukiWeyl m ∉ SuzukiSplitTorus m := by
  intro h
  have hi := ((mem_suzukiSplitTorus_iff_fix_pair m _).mp h).1
  rw [suzukiWeyl_smul_infinity] at hi
  exact suzukiOvoidInfinity_ne_zero m hi.symm

/-- A permutation of the standard pair either fixes or swaps its two points. -/
public theorem mem_suzukiOvoidPair_stabilizer_iff (m : ℕ) (g : SuzukiMatrixGroup m) :
    g ∈ MulAction.stabilizer (SuzukiMatrixGroup m) (suzukiOvoidPair m) ↔
      (g • suzukiOvoidInfinity m = suzukiOvoidInfinity m ∧
       g • suzukiOvoidZero m = suzukiOvoidZero m) ∨
      (g • suzukiOvoidInfinity m = suzukiOvoidZero m ∧
       g • suzukiOvoidZero m = suzukiOvoidInfinity m) := by
  rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
  constructor
  · intro h
    have hi := (suzukiOvoidPair_mem m _).mp (h (b := suzukiOvoidInfinity m) (by simp [suzukiOvoidPair]))
    have hz := (suzukiOvoidPair_mem m _).mp (h (b := suzukiOvoidZero m) (by simp [suzukiOvoidPair]))
    have hne : g • suzukiOvoidInfinity m ≠ g • suzukiOvoidZero m :=
      (MulAction.injective g).ne (suzukiOvoidInfinity_ne_zero m)
    rcases hi with hi | hi <;> rcases hz with hz | hz
    · exact False.elim (hne (hi.trans hz.symm))
    · exact Or.inl ⟨hi, hz⟩
    · exact Or.inr ⟨hi, hz⟩
    · exact False.elim (hne (hi.trans hz.symm))
  · intro h b hb
    rcases (suzukiOvoidPair_mem m b).mp hb with rfl | rfl <;>
      rcases h with h | h <;> simp [suzukiOvoidPair, h.1, h.2]

/-- The pair stabilizer consists of the torus and its right Weyl coset. -/
public theorem suzukiOvoidPair_stabilizer_forms (m : ℕ) (g : SuzukiMatrixGroup m) :
    g ∈ MulAction.stabilizer (SuzukiMatrixGroup m) (suzukiOvoidPair m) ↔
      g ∈ SuzukiSplitTorus m ∨
      ∃ t : SuzukiSplitTorus m, g = (t : SuzukiMatrixGroup m) * suzukiWeyl m := by
  rw [mem_suzukiOvoidPair_stabilizer_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ((mem_suzukiSplitTorus_iff_fix_pair m g).mpr h)
    · have ht : g * suzukiWeyl m ∈ SuzukiSplitTorus m := by
        rw [mem_suzukiSplitTorus_iff_fix_pair]
        simp only [mul_smul, suzukiWeyl_smul_infinity, suzukiWeyl_smul_zero, h.1, h.2,
          and_self]
      exact Or.inr ⟨⟨g * suzukiWeyl m, ht⟩, by
        simp only [mul_assoc, suzukiWeyl_sq, mul_one]⟩
  · rintro (h | ⟨t, rfl⟩)
    · exact Or.inl ((mem_suzukiSplitTorus_iff_fix_pair m g).mp h)
    · have ht := (mem_suzukiSplitTorus_iff_fix_pair m t).mp t.property
      exact Or.inr (by simpa only [mul_smul, suzukiWeyl_smul_infinity,
        suzukiWeyl_smul_zero] using And.intro ht.2 ht.1)

public theorem suzukiWeyl_mem_splitTorus_normalizer (m : ℕ) :
    suzukiWeyl m ∈ (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have hinv := suzukiWeyl_inv m
  have hforward (t : SuzukiMatrixGroup m) (ht : t ∈ SuzukiSplitTorus m) :
      suzukiWeyl m * t * (suzukiWeyl m)⁻¹ ∈ SuzukiSplitTorus m := by
    rw [hinv, suzukiWeyl_conj_splitTorus m ⟨t, ht⟩]
    exact (SuzukiSplitTorus m).inv_mem ht
  constructor
  · exact hforward t
  · intro h
    have hh := hforward _ h
    simpa only [hinv, mul_assoc, suzukiWeyl_sq, mul_one,
      ← mul_assoc (suzukiWeyl m) (suzukiWeyl m), one_mul] using hh

/-- The split torus normalizer is exactly the setwise stabilizer of its fixed pair.
See Huppert--Blackburn III, XI.3.10(e) and XI.3.12(e). -/
public theorem suzukiSplitTorus_normalizer (m : ℕ) (hm : 0 < m) :
    (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))) =
      MulAction.stabilizer (SuzukiMatrixGroup m) (suzukiOvoidPair m) := by
  apply le_antisymm
  · intro g hg
    have hn : Nontrivial (SuzukiSplitTorus m) := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [suzukiSplitTorus_card m hm]
      have hp : 2 ^ 1 < 2 ^ (2 * m + 1) :=
        Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    obtain ⟨t, ht⟩ := exists_ne (1 : SuzukiSplitTorus m)
    have htne : (t : SuzukiMatrixGroup m) ≠ 1 := fun h => ht (Subtype.ext h)
    have hc : g⁻¹ * (t : SuzukiMatrixGroup m) * g ∈ SuzukiSplitTorus m :=
      (Subgroup.mem_normalizer_iff''.mp hg _).mp t.property
    have hf := (mem_suzukiSplitTorus_iff_fix_pair m _).mp hc
    have hi : (t : SuzukiMatrixGroup m) • (g • suzukiOvoidInfinity m) =
        g • suzukiOvoidInfinity m := by
      simpa only [mul_smul, smul_inv_smul] using congrArg (g • ·) hf.1
    have hz : (t : SuzukiMatrixGroup m) • (g • suzukiOvoidZero m) =
        g • suzukiOvoidZero m := by
      simpa only [mul_smul, smul_inv_smul] using congrArg (g • ·) hf.2
    rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
    intro b hb
    rcases (suzukiOvoidPair_mem m b).mp hb with rfl | rfl
    · exact (suzukiSplitTorus_fixed_pair m hm t t.property htne _).mp hi
    · exact (suzukiSplitTorus_fixed_pair m hm t t.property htne _).mp hz
  · intro g hg
    rcases (suzukiOvoidPair_stabilizer_forms m g).mp hg with ht | ⟨t, rfl⟩
    · exact Subgroup.le_normalizer ht
    · exact (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))).mul_mem
        ((SuzukiSplitTorus m).le_normalizer t.property) (suzukiWeyl_mem_splitTorus_normalizer m)

public theorem suzukiSplitTorus_normalizer_forms (m : ℕ) (hm : 0 < m)
    (g : SuzukiMatrixGroup m) :
    g ∈ (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))) ↔ g ∈ SuzukiSplitTorus m ∨
      ∃ t : SuzukiSplitTorus m, g = (t : SuzukiMatrixGroup m) * suzukiWeyl m := by
  rw [suzukiSplitTorus_normalizer m hm, suzukiOvoidPair_stabilizer_forms]

/-- Conjugating outside the normalizer gives a trivial intersection. -/
public theorem suzukiSplitTorus_disjoint_conjugate (m : ℕ) (hm : 0 < m)
    (g : SuzukiMatrixGroup m) (hg : g ∉ (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m)))) :
    Disjoint (SuzukiSplitTorus m)
      ((SuzukiSplitTorus m).map (MulAut.conj g).toMonoidHom) := by
  apply disjoint_iff.mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  by_contra hxne
  have hf := suzukiSplitTorus_map_fixed_pair m g x hx.2
  apply hg
  rw [suzukiSplitTorus_normalizer m hm,
    MulAction.mem_stabilizer_set' (Set.toFinite _)]
  intro b hb
  rcases (suzukiOvoidPair_mem m b).mp hb with rfl | rfl
  · exact (suzukiSplitTorus_fixed_pair m hm x hx.1 hxne _).mp hf.1
  · exact (suzukiSplitTorus_fixed_pair m hm x hx.1 hxne _).mp hf.2

/-- Any two distinct conjugates of the split torus intersect trivially. -/
public theorem suzukiSplitTorus_conjugates_disjoint (m : ℕ) (hm : 0 < m)
    (g h : SuzukiMatrixGroup m)
    (hne : (SuzukiSplitTorus m).map (MulAut.conj g).toMonoidHom ≠
      (SuzukiSplitTorus m).map (MulAut.conj h).toMonoidHom) :
    Disjoint ((SuzukiSplitTorus m).map (MulAut.conj g).toMonoidHom)
      ((SuzukiSplitTorus m).map (MulAut.conj h).toMonoidHom) := by
  have hcomp : (MulAut.conj g).toMonoidHom.comp
      (MulAut.conj (g⁻¹ * h)).toMonoidHom = (MulAut.conj h).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hout : g⁻¹ * h ∉ (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))) := by
    intro hmem
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hmem
    apply hne
    calc
      _ = ((SuzukiSplitTorus m).map
          (MulAut.conj (g⁻¹ * h)).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
        congrArg (fun H : Subgroup (SuzukiMatrixGroup m) =>
          H.map (MulAut.conj g).toMonoidHom) hmem.symm
      _ = _ := by rw [Subgroup.map_map, hcomp]
  have hd := Subgroup.disjoint_map (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective
    (suzukiSplitTorus_disjoint_conjugate m hm (g⁻¹ * h) hout)
  rw [Subgroup.map_map, hcomp] at hd
  exact hd

private noncomputable def splitNormalizerFormsMap (m : ℕ) :
    SuzukiSplitTorus m ⊕ SuzukiSplitTorus m →
      Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))
  | .inl t => ⟨t, (SuzukiSplitTorus m).le_normalizer t.property⟩
  | .inr t => ⟨(t : SuzukiMatrixGroup m) * suzukiWeyl m,
      (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))).mul_mem
        ((SuzukiSplitTorus m).le_normalizer t.property)
        (suzukiWeyl_mem_splitTorus_normalizer m)⟩

private theorem splitNormalizerFormsMap_bijective (m : ℕ) (hm : 0 < m) :
    Function.Bijective (splitNormalizerFormsMap m) := by
  constructor
  · intro a b hab
    have he := congrArg Subtype.val hab
    cases a with
    | inl t =>
      cases b with
      | inl s => exact congrArg Sum.inl (Subtype.ext he)
      | inr s =>
        change (t : SuzukiMatrixGroup m) = (s : SuzukiMatrixGroup m) * suzukiWeyl m at he
        have hh : (s : SuzukiMatrixGroup m) * suzukiWeyl m ∈ SuzukiSplitTorus m :=
          he ▸ t.property
        exact False.elim (suzukiWeyl_not_mem_splitTorus m
          (((SuzukiSplitTorus m).mul_mem_cancel_left s.property).mp hh))
    | inr t =>
      cases b with
      | inl s =>
        change (t : SuzukiMatrixGroup m) * suzukiWeyl m = (s : SuzukiMatrixGroup m) at he
        have hh : (t : SuzukiMatrixGroup m) * suzukiWeyl m ∈ SuzukiSplitTorus m :=
          he.symm ▸ s.property
        exact False.elim (suzukiWeyl_not_mem_splitTorus m
          (((SuzukiSplitTorus m).mul_mem_cancel_left t.property).mp hh))
      | inr s => exact congrArg Sum.inr (Subtype.ext (mul_right_cancel he))
  · intro g
    rcases (suzukiSplitTorus_normalizer_forms m hm g).mp g.property with ht | ⟨t, ht⟩
    · exact ⟨.inl ⟨g, ht⟩, rfl⟩
    · exact ⟨.inr t, Subtype.ext ht.symm⟩

/-- The split torus normalizer has order `2(q - 1)`. -/
public theorem suzukiSplitTorus_normalizer_card (m : ℕ) (hm : 0 < m) :
    Nat.card (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))) =
      2 * (2 ^ (2 * m + 1) - 1) := by
  rw [← Nat.card_congr (Equiv.ofBijective (splitNormalizerFormsMap m)
    (splitNormalizerFormsMap_bijective m hm)), Nat.card_sum, suzukiSplitTorus_card m hm]
  omega

/-- The normalizer of the split torus is dihedral, with `q - 1` rotations. -/
public theorem suzukiSplitTorus_normalizer_dihedral (m : ℕ) (hm : 0 < m) :
    Nonempty (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m)) ≃*
      DihedralGroup (2 ^ (2 * m + 1) - 1)) := by
  let N := Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))
  let i : SuzukiSplitTorus m →* N :=
    Subgroup.inclusion (SuzukiSplitTorus m).le_normalizer
  let := suzukiSplitTorus_isCyclic m hm
  obtain ⟨t, ht⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (SuzukiSplitTorus m))
  let c : N := i t
  let d : N := ⟨suzukiWeyl m, suzukiWeyl_mem_splitTorus_normalizer m⟩
  have hc : c ^ (2 ^ (2 * m + 1) - 1) = 1 := by
    have htorder : orderOf t = 2 ^ (2 * m + 1) - 1 :=
      (orderOf_eq_card_of_zpowers_eq_top ht).trans (suzukiSplitTorus_card m hm)
    change i t ^ _ = 1
    rw [← map_pow, ← htorder, pow_orderOf_eq_one, map_one]
  have hd : d ^ 2 = 1 := by
    apply Subtype.ext
    exact (show suzukiWeyl m ^ 2 = 1 by simpa [pow_two] using suzukiWeyl_sq m)
  have hconj : d * c * d⁻¹ = c⁻¹ := by
    apply Subtype.ext
    change suzukiWeyl m * (t : SuzukiMatrixGroup m) * (suzukiWeyl m)⁻¹ =
      (t : SuzukiMatrixGroup m)⁻¹
    rw [suzukiWeyl_inv, suzukiWeyl_conj_splitTorus]
  have hgen : Subgroup.closure ({c, d} : Set N) = ⊤ := by
    apply top_unique
    intro x _
    have hc_mem : c ∈ Subgroup.closure ({c, d} : Set N) :=
      Subgroup.subset_closure (by simp)
    have hd_mem : d ∈ Subgroup.closure ({c, d} : Set N) :=
      Subgroup.subset_closure (by simp)
    have htorus (s : SuzukiSplitTorus m) :
        i s ∈ Subgroup.closure ({c, d} : Set N) := by
      have hs : s ∈ Subgroup.zpowers t := by rw [ht]; trivial
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      rw [map_zpow]
      exact (Subgroup.closure ({c, d} : Set N)).zpow_mem hc_mem z
    rcases (suzukiSplitTorus_normalizer_forms m hm x).mp x.property with hx | ⟨s, hs⟩
    · exact htorus ⟨x, hx⟩
    · have heq : x = i s * d := Subtype.ext hs
      rw [heq]
      exact (Subgroup.closure ({c, d} : Set N)).mul_mem (htorus s) hd_mem
  have hq : 0 < 2 ^ (2 * m + 1) - 1 := by
    have h := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : 2 * m + 1 ≠ 0)
    omega
  exact dihedralGroup_equiv_of_relations hq c d hc hd hconj hgen
    (suzukiSplitTorus_normalizer_card m hm)

end BenderSuzuki.MatrixGroups
