module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagData
public import Theory.AlgebraicGroup.Representations.Solvable

/-! Linear flags associated with triangular bases, and extension of a prescribed
line by a flag in its quotient. These are the linear steps of Borel §11.1. -/

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy

universe u v
variable {k : Type u} [Field k] {V : Type v}
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A linear automorphism fixes a full flag exactly when it preserves every member. -/
public theorem FullFlag.map_eq_iff (F : FullFlag k V) (e : V ≃ₗ[k] V) :
    F.map e = F ↔ ∀ i, ∀ x ∈ F.subspace i, e x ∈ F.subspace i := by
  constructor
  · intro h i x hx
    have hi := congrArg (fun F : FullFlag k V => F.subspace i) h
    change (F.subspace i).map e.toLinearMap = F.subspace i at hi
    rw [← hi]
    exact ⟨x, hx, rfl⟩
  · intro h
    apply FullFlag.ext
    intro i
    exact Submodule.eq_of_le_of_finrank_eq
      (by rintro _ ⟨x, hx, rfl⟩; exact h i x hx) (e.finrank_map_eq _)

/-- Initial spans of an ordered basis form a full flag. -/
@[expose]
public noncomputable def FullFlag.ofBasis
    (b : Module.Basis (Fin (Module.finrank k V)) k V) : FullFlag k V where
  subspace i := Submodule.span k
    (Set.range fun j : Fin (min i (Module.finrank k V)) => b (Fin.castLE (min_le_right _ _) j))
  monotone := by
    intro i j hij
    apply Submodule.span_mono
    rintro x ⟨l, rfl⟩
    refine ⟨⟨l, lt_of_lt_of_le l.isLt (min_le_min_right _ hij)⟩, ?_⟩
    rfl
  finrank_eq i := by
    have hli : LinearIndependent k (fun j : Fin (min i (Module.finrank k V)) =>
      b (Fin.castLE (min_le_right _ _) j)) :=
      b.linearIndependent.comp _ (Fin.castLE_injective _)
    rw [finrank_span_eq_card hli, Fintype.card_fin]

/-- Every upper-triangular operator preserves the initial-span flag. -/
public theorem FullFlag.ofBasis_invariant
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (A : Module.End k V)
    (hA : tTriangular (Module.finrank k V) (LinearMap.toMatrix b b A)) :
    ∀ i, ∀ x ∈ (FullFlag.ofBasis b).subspace i,
      A x ∈ (FullFlag.ofBasis b).subspace i := by
  intro i x hx
  let r := min i (Module.finrank k V)
  have hr : r ≤ Module.finrank k V := min_le_right _ _
  change x ∈ Submodule.span k (Set.range fun j : Fin r => b (Fin.castLE hr j)) at hx
  change A x ∈ Submodule.span k (Set.range fun j : Fin r => b (Fin.castLE hr j))
  refine Submodule.span_induction (p := fun x _ => A x ∈
    Submodule.span k (Set.range fun j : Fin r => b (Fin.castLE hr j)))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    simpa using (basisSpanCoord V (Module.finrank k V) b r hr
      (b.equivFun (A (b (Fin.castLE hr j))))).mpr (by
        intro l hl
        rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_apply]
        exact hA (j.isLt.trans_le hl))
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [map_smul]; exact Submodule.smul_mem _ a hx

private theorem finrank_comap_mkQ (L : Submodule k V) (W : Submodule k (V ⧸ L)) :
    Module.finrank k (W.comap L.mkQ) = Module.finrank k W + Module.finrank k L := by
  let P := W.comap L.mkQ
  let f : P →ₗ[k] (V ⧸ L) := L.mkQ.comp P.subtype
  have hrange : LinearMap.range f = W := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact x.property
    · intro x hx
      obtain ⟨v, hv⟩ := L.mkQ_surjective x
      exact ⟨⟨v, by change L.mkQ v ∈ W; rwa [hv]⟩, hv⟩
  have hLP : L ≤ P := by
    intro x hx
    change L.mkQ x ∈ W
    rw [show L.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero L).mpr hx]
    exact W.zero_mem
  have hker : LinearMap.ker f = L.comap P.subtype := by
    ext x
    exact Submodule.Quotient.mk_eq_zero L
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe hLP).finrank_eq] at hdim
  exact hdim.symm

/-- Extend a specified one-dimensional subspace using a full flag of its quotient.
The first nonzero member is the specified line, including when the quotient is zero. -/
@[expose]
public def FullFlag.extendLine (L : Submodule k V) (hL : Module.finrank k L = 1)
    (F : FullFlag k (V ⧸ L)) : FullFlag k V where
  subspace
    | 0 => ⊥
    | i + 1 => (F.subspace i).comap L.mkQ
  monotone := by
    intro i j hij
    cases i with
    | zero => exact bot_le
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact Submodule.comap_mono (F.monotone (by omega))
  finrank_eq i := by
    cases i with
    | zero => simp
    | succ i =>
      rw [finrank_comap_mkQ, F.finrank_eq, hL]
      have hd := Submodule.finrank_quotient_add_finrank L
      rw [hL] at hd
      omega

@[simp]
public theorem FullFlag.extendLine_one (L : Submodule k V)
    (hL : Module.finrank k L = 1) (F : FullFlag k (V ⧸ L)) :
    (F.extendLine L hL).subspace 1 = L := by
  have hzero : F.subspace 0 = ⊥ := Submodule.finrank_eq_zero.mp (by
    rw [F.finrank_eq]; simp)
  change (F.subspace 0).comap L.mkQ = L
  rw [hzero, Submodule.comap_bot, Submodule.ker_mkQ]

/-- Lie--Kolchin on the quotient extends any prescribed invariant line to a
full invariant flag; the line is retained as the flag's first member. -/
public theorem exists_invariant_fullFlag_extending_line [IsAlgClosed k]
    {G : Variety k} [AlgebraicGroup G]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (L : Submodule k V) (hL : Module.finrank k L = 1)
    (hstable : IsInvariantSubmodule ρ L) :
    ∃ F : FullFlag k V, F.subspace 1 = L ∧
      ∀ g, (flagAction ρ).smul g F = F := by
  obtain ⟨σ, hσ, hσrat⟩ := rationalRepresentation_quotient_exists ρ hρ L hstable
  obtain ⟨b, hb⟩ := σ.exists_basis_tTriangular_of_isSolvable_isConnected
    hσrat hsolvable hconnected
  let F := (FullFlag.ofBasis b).extendLine L hL
  refine ⟨F, FullFlag.extendLine_one L hL _, ?_⟩
  intro g
  change F.map (ρ.action g).toLinearEquiv = F
  rw [FullFlag.map_eq_iff]
  intro i x hx
  cases i with
  | zero =>
    change x ∈ (⊥ : Submodule k V) at hx
    change (ρ.action g).toLinearEquiv x ∈ (⊥ : Submodule k V)
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]
  | succ i =>
    change L.mkQ ((ρ.action g : Module.End k V) x) ∈ (FullFlag.ofBasis b).subspace i
    rw [show L.mkQ ((ρ.action g : Module.End k V) x) =
      (σ.action g : Module.End k (V ⧸ L)) (L.mkQ x) from (hσ g x).symm]
    exact FullFlag.ofBasis_invariant b _ (hb g) i (L.mkQ x) hx

end Theory.AlgebraicGroup.BorelGeometricConjugacy
