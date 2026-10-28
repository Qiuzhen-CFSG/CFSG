module

public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport

/-!
# The diagonal generates the moved space

For distinct Irr⁺ members I and Iᵃ, put D = [I,a], U = [D,X], and
Z = C_V(X). If A fixes D and [X,A] = X, then U is both X- and A-invariant.
The irreducible quotients of I and Iᵃ have no fixed vectors, giving D ≤ U + Z.
If I is not contained in U, irreducible separation gives U ≤ D + Z. Hence
D + Z is X-invariant. On the quotient by Z the commutator identity makes X
fix D; the absence of fixed vectors then gives D ≤ Z. This contradicts the
noninvariance of the diagonal. Thus I ≤ U, and A-invariance gives Iᵃ ≤ U.

The supporting lemmas work with literal invariant subspaces and quotients;
no residual, chief-factor, or best-offender conclusion is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.7.2(1), printed p. 119 (PDF p. 130).
-/

public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The commutator span is invariant even if the original subspace is not. -/
theorem subspaceCommutator_invariant (D : Submodule (ZMod 2) V) (X : Subgroup G) :
    X ≤ subspaceStabilizer ρ (subspaceCommutator ρ D X) := by
  apply le_subspaceStabilizer
  intro x hx
  change subspaceCommutator ρ D X ≤ (subspaceCommutator ρ D X).comap (ρ x)
  apply Submodule.span_le.mpr
  rintro _ ⟨y, hy, d, hd, rfl⟩
  change ρ x (ρ y d - d) ∈ subspaceCommutator ρ D X
  have hxy : ρ (x * y) d - d ∈ subspaceCommutator ρ D X :=
    Submodule.subset_span ⟨x * y, X.mul_mem hx hy, d, hd, rfl⟩
  have hxv : ρ x d - d ∈ subspaceCommutator ρ D X :=
    Submodule.subset_span ⟨x, hx, d, hd, rfl⟩
  have he : ρ x (ρ y d - d) = (ρ (x * y) d - d) - (ρ x d - d) := by
    rw [map_sub, map_mul, Module.End.mul_apply]
    abel
  rw [he]
  exact Submodule.sub_mem _ hxy hxv

/-- Normalizers preserve the fixed space of the subgroup. -/
theorem fixedSpace_invariant_normalizer {X A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer X) : A ≤ subspaceStabilizer ρ (fixedSpace ρ X) := by
  apply le_subspaceStabilizer
  intro a ha z hz x
  have hx : a⁻¹ * x * a ∈ X := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (hA (A.inv_mem ha)) x).mp x.property
  have hfix : ρ (a⁻¹ * x * a) z = z := hz ⟨_, hx⟩
  change ρ x (ρ a z) = ρ a z
  calc
    _ = ρ a (ρ (a⁻¹ * x * a) z) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    _ = _ := congrArg (ρ a) hfix

/-- No new fixed vectors arise from an Irr⁺ member except in the given kernel. -/
theorem IsIrrPlus.mem_or_fixed_of_differences_mem {X : Subgroup G}
    {I K : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) {v : V} (hv : v ∈ I)
    (hd : ∀ x ∈ X, ρ x v - v ∈ K) : v ∈ K ∨ v ∈ fixedSpace ρ X := by
  let T : Submodule (ZMod 2) V :=
    { carrier := {v | v ∈ I ∧ ∀ x ∈ X, ρ x v - v ∈ K}
      zero_mem' := ⟨I.zero_mem, by simp⟩
      add_mem' := by
        intro u v hu hv
        refine ⟨I.add_mem hu.1 hv.1, ?_⟩
        intro x hx
        have he : ρ x (u + v) - (u + v) = (ρ x u - u) + (ρ x v - v) := by
          rw [map_add]
          abel
        rw [he]
        exact K.add_mem (hu.2 x hx) (hv.2 x hx)
      smul_mem' := by
        intro c v hv
        refine ⟨I.smul_mem c hv.1, ?_⟩
        intro x hx
        rw [map_smul, ← smul_sub]
        exact K.smul_mem c (hv.2 x hx) }
  have hTs : X ≤ subspaceStabilizer ρ T := by
    apply le_subspaceStabilizer
    intro x hx u hu
    refine ⟨(hI.choose hx u).2 hu.1, ?_⟩
    intro y hy
    have he : ρ y (ρ x u) - ρ x u = (ρ (y * x) u - u) - (ρ x u - u) := by
      rw [map_mul, Module.End.mul_apply]
      abel
    rw [he]
    exact K.sub_mem (hu.2 (y * x) (X.mul_mem hy hx)) (hu.2 x hx)
  rcases hI.eq_or_le_fixedSpace ρ hTs (fun _ hu => hu.1) with he | hfix
  · left
    have hIK : subspaceCommutator ρ I X ≤ K := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, u, hu, rfl⟩
      exact (show u ∈ T from he.symm ▸ hu).2 x hx
    rw [hI.choose_spec.1] at hIK
    exact hIK hv
  · exact Or.inr (hfix ⟨hv, hd⟩)

/-- The sum of two Irr⁺ members has no fixed vectors in any invariant quotient
whose kernel contains the original fixed space. -/
theorem IsIrrPlus.sup_mem_of_differences_mem {X : Subgroup G}
    {I J K : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) (hJ : IsIrrPlus ρ X J)
    (hK : X ≤ subspaceStabilizer ρ K) (hZ : fixedSpace ρ X ≤ K)
    {v : V} (hv : v ∈ I ⊔ J) (hd : ∀ x ∈ X, ρ x v - v ∈ K) : v ∈ K := by
  have hkill {L : Submodule (ZMod 2) V} (hL : IsIrrPlus ρ X L) {u : V}
      (hu : u ∈ L) (hd : ∀ x ∈ X, ρ x u - u ∈ K) : u ∈ K :=
    (hL.mem_or_fixed_of_differences_mem ρ hu hd).elim id (fun hu => hZ hu)
  rcases hI.le_or_inf_sup_fixedSpace_le ρ (subspaceStabilizer_sup ρ hJ.choose hK)
    with h | h
  · have hvJK : v ∈ J ⊔ K := (sup_le h (le_sup_left : J ≤ J ⊔ K)) hv
    obtain ⟨j, hj, k, hk, rfl⟩ := Submodule.mem_sup.mp hvJK
    have hdj : ∀ x ∈ X, ρ x j - j ∈ K := by
      intro x hx
      have hdk : ρ x k - k ∈ K := K.sub_mem ((hK hx k).2 hk) hk
      have he : ρ x j - j = (ρ x (j + k) - (j + k)) - (ρ x k - k) := by
        rw [map_add]
        abel
      rw [he]
      exact K.sub_mem (hd x hx) hdk
    exact K.add_mem (hkill hJ hj hdj) hk
  · obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp hv
    have hdi : ∀ x ∈ X, ρ x i - i ∈ K := by
      intro x hx
      apply hZ
      apply h
      refine ⟨I.sub_mem ((hI.choose hx i).2 hi) hi, Submodule.mem_sup_left ?_⟩
      apply Submodule.mem_sup.mpr
      refine ⟨-(ρ x j - j), J.neg_mem (J.sub_mem ((hJ.choose hx j).2 hj) hj),
        ρ x (i + j) - (i + j), hd x hx, ?_⟩
      rw [map_add]
      abel
    have hdj : ∀ x ∈ X, ρ x j - j ∈ K := by
      intro x hx
      have he : ρ x j - j = (ρ x (i + j) - (i + j)) - (ρ x i - i) := by
        rw [map_add]
        abel
      rw [he]
      exact K.sub_mem (hd x hx) (hdi x hx)
    exact K.add_mem (hkill hI hi hdi) (hkill hJ hj hdj)

/-- Commutator fixation can be checked in the literal quotient by an invariant subspace. -/
theorem differences_mem_of_invariant_mod_fixed {X A : Subgroup G}
    {D Z : Submodule (ZMod 2) V}
    (hXZ : X ≤ subspaceStabilizer ρ Z) (hAZ : A ≤ subspaceStabilizer ρ Z)
    (hDX : X ≤ subspaceStabilizer ρ (D ⊔ Z))
    (hDA : D ≤ fixedSpace ρ A) (hXA : ⁅X, A⁆ = X) :
    ∀ d ∈ D, ∀ x ∈ X, ρ x d - d ∈ Z := by
  let N := subspaceStabilizer ρ Z
  let Zs := invariantSubspace ρ N Z le_rfl
  let τ := Zs.quotientRepresentation
  let Xn := X.subgroupOf N
  let An := A.subgroupOf N
  have hcomm : ⁅Xn, An⁆ = Xn := by
    apply Subgroup.map_injective N.subtype_injective
    change (⁅X.subgroupOf N, A.subgroupOf N⁆).map N.subtype = (X.subgroupOf N).map N.subtype
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXZ,
      Subgroup.map_subgroupOf_eq_of_le hAZ, hXA]
  have hstab : Xn ≤ subspaceStabilizer τ (D.map Z.mkQ) := by
    apply le_subspaceStabilizer
    rintro x hx _ ⟨d, hd, rfl⟩
    have hv : ρ x d ∈ D ⊔ Z := (hDX hx d).2 (Submodule.mem_sup_left hd)
    obtain ⟨d', hd', z, hz, he⟩ := Submodule.mem_sup.mp hv
    refine ⟨d', hd', ?_⟩
    change Z.mkQ d' = Z.mkQ (ρ x d)
    have hz0 : Z.mkQ z = 0 := (Submodule.Quotient.mk_eq_zero Z).mpr hz
    rw [← he, map_add, hz0, add_zero]
  have hfix : D.map Z.mkQ ≤ fixedSpace τ An := by
    rintro _ ⟨d, hd, rfl⟩ a
    change Z.mkQ (ρ a d) = Z.mkQ d
    exact congrArg Z.mkQ (hDA hd ⟨a, a.property⟩)
  have h := le_fixedSpace_commutator_of_invariant τ hstab hfix
  rw [hcomm] at h
  intro d hd x hx
  have he := h ⟨d, hd, rfl⟩ ⟨⟨x, hXZ hx⟩, hx⟩
  change Z.mkQ (ρ x d) = Z.mkQ d at he
  apply (Submodule.Quotient.mk_eq_zero Z).mp
  change Z.mkQ (ρ x d - d) = 0
  rw [map_sub, he, sub_self]

/-- The diagonal commutators generate the whole moved space. -/
theorem IsIrrPlus.diagonal_generation {X A : Subgroup G}
    {I : Submodule (ZMod 2) V} {a : G}
    (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (ha : a ∈ A) (hXA : ⁅X, A⁆ = X)
    (hq : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v) :
    subspaceCommutator ρ (diagonalSubspace ρ I a) X = I ⊔ I.map (ρ a) := by
  let J := I.map (ρ a)
  let D := diagonalSubspace ρ I a
  let U := subspaceCommutator ρ D X
  let Z := fixedSpace ρ X
  have hAN : A ≤ Subgroup.normalizer X :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hXA.le
  have hZX : X ≤ subspaceStabilizer ρ Z := by
    apply le_subspaceStabilizer
    intro x hx z hz
    have he : ρ x z = z := hz ⟨x, hx⟩
    rw [he]
    exact hz
  have hZA : A ≤ subspaceStabilizer ρ Z := fixedSpace_invariant_normalizer ρ hAN
  have hDW : D ≤ I ⊔ J := by
    rintro _ ⟨i, hi, rfl⟩
    exact (I ⊔ J).sub_mem (Submodule.mem_sup_right ⟨i, hi, rfl⟩)
      (Submodule.mem_sup_left hi)
  have hUX : X ≤ subspaceStabilizer ρ U := subspaceCommutator_invariant ρ D X
  have hDA : D ≤ fixedSpace ρ A := diagonalSubspace_le_fixedSpace ρ hq
  have hUA : A ≤ subspaceStabilizer ρ U := by
    apply subspaceCommutator_invariant_normalizer ρ _ hAN
    apply le_subspaceStabilizer
    intro b hb d hd
    have he : ρ b d = d := hDA hd ⟨b, hb⟩
    rw [he]
    exact hd
  have hUW : U ≤ I ⊔ J :=
    (subspaceCommutator_mono_left ρ hDW X).trans (hI.sup_commutator ρ hIa).le
  have hDUZ : D ≤ U ⊔ Z := by
    intro d hd
    apply hI.sup_mem_of_differences_mem ρ hIa (subspaceStabilizer_sup ρ hUX hZX)
      le_sup_right (hDW hd)
    intro x hx
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨x, hx, d, hd, rfl⟩)
  apply le_antisymm hUW
  by_cases hIU : I ≤ U
  · apply sup_le hIU
    rintro _ ⟨i, hi, rfl⟩
    exact (hUA ha i).2 (hIU hi)
  have hJU : ¬ J ≤ U := by
    intro h
    apply hIU
    intro i hi
    exact (hUA ha i).1 (h ⟨i, hi, rfl⟩)
  have hJUZ : J ⊓ (U ⊔ Z) ≤ Z :=
    (hIa.le_or_inf_sup_fixedSpace_le ρ hUX).resolve_left hJU
  have hUDZ : U ≤ D ⊔ Z := by
    intro u hu
    obtain ⟨i, hi, j, hj, he⟩ := Submodule.mem_sup.mp (hUW hu)
    have hdi : ρ a i - i ∈ D := ⟨i, hi, rfl⟩
    have hz : j + ρ a i ∈ Z := by
      apply hJUZ
      refine ⟨J.add_mem hj ⟨i, hi, rfl⟩, ?_⟩
      have hh := (U ⊔ Z).add_mem (Submodule.mem_sup_left hu) (hDUZ hdi)
      have heq : u + (ρ a i - i) = j + ρ a i := by rw [← he]; abel
      rwa [heq] at hh
    refine Submodule.mem_sup.mpr ⟨-(ρ a i - i), D.neg_mem hdi, j + ρ a i, hz, ?_⟩
    rw [← he]
    abel
  have hDZ : D ⊔ Z = U ⊔ Z := le_antisymm (sup_le hDUZ le_sup_right)
    (sup_le hUDZ le_sup_right)
  have hDX : X ≤ subspaceStabilizer ρ (D ⊔ Z) := by
    rw [hDZ]
    exact subspaceStabilizer_sup ρ hUX hZX
  have hdif := differences_mem_of_invariant_mod_fixed ρ hZX hZA hDX hDA hXA
  have hDZ' : D ≤ Z := by
    intro d hd
    exact hI.sup_mem_of_differences_mem ρ hIa hZX le_rfl (hDW hd) (hdif d hd)
  exfalso
  apply hI.diagonal_not_invariant ρ hIa hne hXA hq
  apply le_subspaceStabilizer
  intro x hx d hd
  have he : ρ x d = d := hDZ' hd ⟨x, hx⟩
  rw [he]
  exact hd

end Representation.BinaryOffender
