module

public import Mathlib.Algebra.Lie.LieTheorem
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.Algebra.Lie.CartanCriterion
public import Theory.AlgebraicGroup.Bor1.GeneralLinearSubspaceStabilizerTangent
public import Theory.AlgebraicGroup.Instance.Triangular
public import Theory.AlgebraicGroup.Instance.U
public import Theory.AlgebraicGroup.Instance.Stabilizer
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Reductive.Basic
public import Theory.AlgebraicGroup.Representations.Unipotent.Flag
public import Theory.AlgebraicGroup.RightTranslation.Representation
public import Theory.AlgebraicGroup.RootSystems.NormalCoreTangent
public import Theory.AlgebraicGroup.RootSubgroups.TangentLieIdeal
public import Theory.AlgebraicGroup.RootSubgroups.CenterTangent

/-!
# Solvable Lie ideals and the algebraic radical

Over an algebraically closed field of characteristic zero, this module proves
that every solvable ideal in the canonical identity tangent Lie algebra of a
reductive algebraic group lies in the embedded tangent of its algebraic-group
radical.  This is the geometric integration bridge used to compare the
group-theoretic radical with the Lie-algebra radical.

The proof applies Lie's theorem to the faithful coordinate-translation
representation.  A complete invariant flag is constructed one dimension at a
time from common weight vectors, and its closed general-linear stabilizer is
shown solvable by embedding it into the upper-triangular group.  Exact
characteristic-zero tangent formulas place the ideal in the tangent of the
flag-stabilizer preimage.  Conjugation invariance of Lie ideals and the
tangent-preserving normal-core theorem then produce a connected normal
solvable closed subgroup with the same tangent containment.  Maximality of the
radical and functoriality of identity differentials finish the inclusion.

This is the standard characteristic-zero integration argument for solvable
Lie ideals of linear algebraic groups.  It uses the repository's canonical
tangent Lie structure and faithful coordinate representation, and is
independent of root-subgroup existence, uniqueness, rescaling, and the clauses
of GLS3 Theorem 1.9.5.
-/

open scoped LieRing

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

private def lieSubmoduleSubtypeEquivToSubmodule
    {L : Type v} [LieRing L]
    {V : Type w} [AddCommGroup V] [Module k V] [LieRingModule L V]
    (W : LieSubmodule k L V) : W ≃ₗ[k] W.toSubmodule where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨x, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsAlgClosed k] [CharZero k] in
private lemma lieSubmodule_finrank_toSubmodule
    {L : Type v} [LieRing L]
    {V : Type w} [AddCommGroup V] [Module k V] [LieRingModule L V]
    (W : LieSubmodule k L V) :
    Module.finrank k W = Module.finrank k W.toSubmodule :=
  (lieSubmoduleSubtypeEquivToSubmodule W).finrank_eq

private lemma exists_lieSubmodule_extension_finrank_succ
    {L : Type v} [LieRing L] [LieAlgebra k L]
    [LieAlgebra.IsSolvable L]
    {V : Type w} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [LieRingModule L V] [LieModule k L V]
    (W : LieSubmodule k L V)
    (hW : Module.finrank k W.toSubmodule < Module.finrank k V) :
    ∃ U : LieSubmodule k L V,
      W ≤ U ∧ Module.finrank k U.toSubmodule =
        Module.finrank k W.toSubmodule + 1 := by
  let q := LieSubmodule.Quotient.mk' W
  have hqfin : 0 < Module.finrank k (V ⧸ W) := by
    have hsum : Module.finrank k (V ⧸ W.toSubmodule) +
        Module.finrank k W.toSubmodule =
        Module.finrank k V := by
      exact Submodule.finrank_quotient_add_finrank W.toSubmodule
    change 0 < Module.finrank k (V ⧸ W.toSubmodule)
    omega
  let : Nontrivial (V ⧸ W) := Module.finrank_pos_iff.mp hqfin
  obtain ⟨chi, hchi⟩ :=
    LieModule.exists_nontrivial_weightSpace_of_isSolvable
      k L (V ⧸ W)
  obtain ⟨z, hz⟩ := exists_ne (0 : LieModule.weightSpace
    (V ⧸ W) chi)
  have hzmem : ∀ x : L, ⁅x, (z : V ⧸ W)⁆ =
      chi x • (z : V ⧸ W) := by
    have hzprop := z.property
    rw [LieModule.mem_weightSpace] at hzprop
    exact hzprop
  let Z : LieSubmodule k L (V ⧸ W) :=
    { toSubmodule := k ∙ (z : V ⧸ W)
      lie_mem := by
        intro x y hy
        change y ∈ k ∙ (z : V ⧸ W) at hy
        change ⁅x, y⁆ ∈ k ∙ (z : V ⧸ W)
        rw [Submodule.mem_span_singleton] at hy ⊢
        obtain ⟨a, rfl⟩ := hy
        rw [lie_smul, hzmem]
        exact ⟨a * chi x, by rw [mul_smul]⟩ }
  let U := Z.comap q
  have hWU : W ≤ U := by
    intro x hx
    change q x ∈ Z
    have hqx : q x = 0 := (LieSubmodule.Quotient.mk_eq_zero W).2 hx
    rw [hqx]
    exact Z.zero_mem
  have hZdimSubmodule : Module.finrank k Z.toSubmodule = 1 := by
    change Module.finrank k (k ∙ (z : V ⧸ W)) = 1
    rw [finrank_span_singleton]
    intro hz0
    apply hz
    apply Subtype.ext
    exact hz0
  have hZdim : Module.finrank k (↥Z) = 1 := by
    rw [lieSubmodule_finrank_toSubmodule]
    exact hZdimSubmodule
  let f : U →ₗ[k] Z :=
    LinearMap.codRestrict Z.toSubmodule
      (q.toLinearMap.domRestrict U.toSubmodule) (fun x => x.property)
  have hfrange : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨x, hx⟩ := LieSubmodule.Quotient.surjective_mk' W y.1
    have hxU : x ∈ U := by
      change q x ∈ Z
      rw [hx]
      exact y.2
    refine ⟨⟨x, hxU⟩, ?_⟩
    apply Subtype.ext
    exact hx
  have hfker : LinearMap.ker f = W.toSubmodule.comap U.toSubmodule.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap]
    change (⟨q x.1, x.property⟩ : Z) = 0 ↔ x.1 ∈ W
    rw [Subtype.ext_iff]
    exact LieSubmodule.Quotient.mk_eq_zero W
  have hkerdim : Module.finrank k (LinearMap.ker f) =
      Module.finrank k W.toSubmodule := by
    rw [hfker]
    exact (Submodule.comapSubtypeEquivOfLe hWU).finrank_eq
  have hranknull := LinearMap.finrank_range_add_finrank_ker f
  rw [hfrange, finrank_top, hZdim, hkerdim] at hranknull
  refine ⟨U, hWU, ?_⟩
  rw [← lieSubmodule_finrank_toSubmodule]
  omega

private lemma exists_full_invariant_lieSubmodule_chain
    {L : Type v} [LieRing L] [LieAlgebra k L]
    [LieAlgebra.IsSolvable L]
    {V : Type w} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [LieRingModule L V] [LieModule k L V] :
    ∃ F : ℕ → LieSubmodule k L V, Monotone F ∧
      ∀ i, Module.finrank k (F i).toSubmodule =
        min i (Module.finrank k V) := by
  let n := Module.finrank k V
  have hexists (W : LieSubmodule k L V) :
      ∃ U : LieSubmodule k L V, W ≤ U ∧
        Module.finrank k U.toSubmodule =
          if Module.finrank k W.toSubmodule < n then
            Module.finrank k W.toSubmodule + 1
          else Module.finrank k W.toSubmodule := by
    by_cases hlt : Module.finrank k W.toSubmodule < n
    · obtain ⟨U, hWU, hUdim⟩ :=
        exists_lieSubmodule_extension_finrank_succ W hlt
      exact ⟨U, hWU, by rw [if_pos hlt]; exact hUdim⟩
    · exact ⟨W, le_rfl, by rw [if_neg hlt]⟩
  let next : LieSubmodule k L V → LieSubmodule k L V := fun W =>
    (hexists W).choose
  have hnext_le (W : LieSubmodule k L V) : W ≤ next W := by
    exact (hexists W).choose_spec.1
  have hnext_finrank (W : LieSubmodule k L V) :
      Module.finrank k (next W).toSubmodule =
        if Module.finrank k W.toSubmodule < n then
          Module.finrank k W.toSubmodule + 1
        else Module.finrank k W.toSubmodule := by
    exact (hexists W).choose_spec.2
  let F : ℕ → LieSubmodule k L V := fun i => next^[i] ⊥
  have hFdim : ∀ i, Module.finrank k (F i).toSubmodule = min i n := by
    intro i
    induction i with
    | zero =>
        change Module.finrank k (⊥ : Submodule k V) = 0
        simp
    | succ i ih =>
        rw [show F (i + 1) = next (F i) by
          simp [F, Function.iterate_succ_apply']]
        rw [hnext_finrank, ih]
        by_cases hi : i < n
        · rw [if_pos (by omega)]
          omega
        · rw [if_neg (by omega)]
          omega
  have hFmono : Monotone F := by
    apply monotone_nat_of_le_succ
    intro i
    change next^[i] (⊥ : LieSubmodule k L V) ≤
      next^[i + 1] (⊥ : LieSubmodule k L V)
    rw [Function.iterate_succ_apply']
    exact hnext_le _
  exact ⟨F, hFmono, hFdim⟩

private lemma exists_basis_lie_action_tTriangular
    {L : Type v} [LieRing L] [LieAlgebra k L]
    [LieAlgebra.IsSolvable L]
    {V : Type w} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [LieRingModule L V] [LieModule k L V] :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V,
      ∀ x : L, tTriangular (Module.finrank k V)
        (LinearMap.toMatrix b b (LieModule.toEnd k L V x)) := by
  obtain ⟨F, hFmono, hFdim⟩ :=
    exists_full_invariant_lieSubmodule_chain (k := k) (L := L) (V := V)
  obtain ⟨b, hb⟩ := exists_basis_adapted_to_full_submodule_chain
    (fun i => (F i).toSubmodule) hFmono hFdim
  refine ⟨b, ?_⟩
  intro x i j hji
  rw [LinearMap.toMatrix_apply]
  have hjle : (j : ℕ) + 1 ≤ Module.finrank k V := j.isLt
  have hbj : b j ∈ (F (j + 1)).toSubmodule := by
    rw [hb (j + 1) hjle]
    apply Submodule.subset_span
    refine ⟨⟨j, by omega⟩, ?_⟩
    congr 1
  have hmap : LieModule.toEnd k L V x (b j) ∈ (F (j + 1)).toSubmodule :=
    (F (j + 1)).lie_mem hbj
  rw [hb (j + 1) hjle] at hmap
  have hcoords := (basisSpanCoord V (Module.finrank k V) b
    ((j : ℕ) + 1) hjle
    (b.equivFun (LieModule.toEnd k L V x (b j)))).mp (by
      simpa using hmap)
  exact hcoords i (by omega)

private noncomputable def basisInitialSpan
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (r : ℕ) :
    Submodule k V :=
  Submodule.span k (Set.range fun j :
    {i : Fin (Module.finrank k V) // (i : ℕ) < r} => b j.1)

omit [IsAlgClosed k] [CharZero k] in
private lemma basisInitialSpan_eq
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (r : ℕ) (hr : r ≤ Module.finrank k V) :
    basisInitialSpan b r =
      Submodule.span k (Set.range fun j : Fin r => b (Fin.castLE hr j)) := by
  apply congrArg (Submodule.span k)
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j.1, j.2⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨Fin.castLE hr j, j.2⟩, rfl⟩

omit [IsAlgClosed k] [CharZero k] in
private lemma tTriangular_preserves_basisInitialSpan
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (A : Module.End k V)
    (hA : tTriangular (Module.finrank k V) (LinearMap.toMatrix b b A))
    (r : ℕ) (hr : r ≤ Module.finrank k V) :
    ∀ w : V, w ∈ basisInitialSpan b r → A w ∈ basisInitialSpan b r := by
  rw [basisInitialSpan_eq b r hr]
  intro w hw
  exact Submodule.span_induction
    (p := fun w _ => A w ∈ Submodule.span k
      (Set.range fun j : Fin r => b (Fin.castLE hr j)))
    (fun _ h => by
      rcases h with ⟨j, rfl⟩
      simpa using (basisSpanCoord V (Module.finrank k V) b r hr
        (b.equivFun (A (b (Fin.castLE hr j))))).mpr (by
          intro i hi
          rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_apply]
          exact hA (j.isLt.trans_le hi)))
    (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun x y _ _ hx hy => by
      rw [map_add]
      exact Submodule.add_mem _ hx hy)
    (fun a x _ hx => by
      rw [map_smul]
      exact Submodule.smul_mem _ a hx)
    hw

private noncomputable def fullFlagPiece
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e b : Module.Basis (Fin (Module.finrank k V)) k V) (r : ℕ) :
    ClosedSubgroup (glVarietyOf k V) :=
  Bor1.generalLinearSubspaceStabilizer e
    (if r = 0 then ⊥ else basisInitialSpan b r)

private noncomputable def fullFlagStabilizerAux
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e b : Module.Basis (Fin (Module.finrank k V)) k V) :
    ℕ → ClosedSubgroup (glVarietyOf k V)
  | 0 => fullFlagPiece e b 0
  | m + 1 =>
      (fullFlagStabilizerAux e b m).inter (fullFlagPiece e b (m + 1))

private noncomputable def fullFlagStabilizer
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e b : Module.Basis (Fin (Module.finrank k V)) k V) :
    ClosedSubgroup (glVarietyOf k V) :=
  fullFlagStabilizerAux e b (Module.finrank k V)

omit [CharZero k] in
private lemma fullFlagStabilizerAux_le_piece
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e b : Module.Basis (Fin (Module.finrank k V)) k V)
    {r m : ℕ} (hrm : r ≤ m) :
    fullFlagStabilizerAux e b m ≤ fullFlagPiece e b r := by
  induction m with
  | zero =>
      have hr : r = 0 := by omega
      subst r
      exact fun _ hx => hx
  | succ m ih =>
      by_cases hr : r = m + 1
      · subst r
        intro x hx
        exact (ClosedSubgroup.mem_inter_iff _ _ x).mp hx |>.2
      · intro x hx
        exact ih (by omega) ((ClosedSubgroup.mem_inter_iff _ _ x).mp hx |>.1)

omit [CharZero k] in
private lemma fullFlagStabilizer_point_tTriangular
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (fullFlagStabilizer e b).carrierVariety) :
    tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b
        ((glPointEquivOf k V e
          ((fullFlagStabilizer e b).inclusion.onPoints x)).1)) := by
  intro i j hji
  rw [LinearMap.toMatrix_apply]
  let r := (j : ℕ) + 1
  have hr : r ≤ Module.finrank k V := j.isLt
  have hxPiece : (fullFlagStabilizer e b).inclusion.onPoints x ∈
      fullFlagPiece e b r :=
    fullFlagStabilizerAux_le_piece e b hr
      ((fullFlagStabilizer e b).pointEquiv x).property
  have hxStabilizer : (fullFlagStabilizer e b).inclusion.onPoints x ∈
      Bor1.generalLinearSubspaceStabilizer e (basisInitialSpan b r) := by
    simpa [fullFlagPiece, r] using hxPiece
  have hmap := (Bor1.mem_generalLinearSubspaceStabilizer_iff e
    (basisInitialSpan b r) _).mp hxStabilizer
  have hbj : b j ∈ basisInitialSpan b r := by
    rw [basisInitialSpan_eq b r hr]
    apply Submodule.subset_span
    refine ⟨⟨j, by omega⟩, ?_⟩
    congr 1
  have hmapped :
      (glPointEquivOf k V e ((fullFlagStabilizer e b).inclusion.onPoints x)).1
          (b j) ∈ basisInitialSpan b r := by
    have :
        (glPointEquivOf k V e
            ((fullFlagStabilizer e b).inclusion.onPoints x)).1
            (b j) ∈
          Submodule.map
            ((glPointEquivOf k V e
              ((fullFlagStabilizer e b).inclusion.onPoints x)).1)
            (basisInitialSpan b r) := ⟨b j, hbj, rfl⟩
    rwa [hmap] at this
  rw [basisInitialSpan_eq b r hr] at hmapped
  have hcoords := (basisSpanCoord V (Module.finrank k V) b r hr
    (b.equivFun ((glPointEquivOf k V e
      ((fullFlagStabilizer e b).inclusion.onPoints x)).1 (b j)))).mp (by
        simpa using hmapped)
  exact hcoords i (by omega)

omit [CharZero k] in
private lemma tDiagonalHom_apply_val (n : ℕ)
    (A : tTriangularGL k n) (i : Fin n) :
    (↑(tDiagonalHom n A i) : k) = A.1.1 i i := by
  let x := (tPointEquiv k n).symm A
  simpa only [x, Equiv.apply_symm_apply, tPointMatrix,
    tPointEquiv_symm_val_inl] using tDiagonalHom_val n x i

omit [CharZero k] in
private lemma tTriangularGL_isSolvable (n : ℕ) :
    Group.IsSolvable (tTriangularGL k n) := by
  let U := uUnipotentGL k n
  let uToKer : U →* (tDiagonalHom (k := k) n).ker :=
    { toFun := fun A => ⟨uToTHom n A, by
          ext i
          rw [tDiagonalHom_apply_val]
          change A.1.1 i i = 1
          exact A.2.2 i⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (uToTHom (k := k) n)
      map_mul' := by
        intro A B
        apply Subtype.ext
        exact map_mul (uToTHom (k := k) n) A B }
  have huToKer_surjective : Function.Surjective uToKer := by
    intro A
    have hdiag : ∀ i : Fin n, A.1.1.1 i i = 1 := by
      intro i
      have hi := congrFun A.2 i
      have hi' := congrArg (fun z : kˣ => (z : k)) hi
      rw [tDiagonalHom_apply_val] at hi'
      simpa using hi'
    let B : U := ⟨A.1.1, ⟨A.1.2, hdiag⟩⟩
    refine ⟨B, ?_⟩
    apply Subtype.ext
    rfl
  let : Group.IsNilpotent U := uUnipotentGL_isNilpotent n
  let : Group.IsSolvable (tDiagonalHom (k := k) n).ker :=
    Group.isSolvable_of_surjective huToKer_surjective
  let : Group.IsSolvable (Fin n → kˣ) :=
    Group.isSolvable_of_comm fun _ _ => mul_comm _ _
  exact Group.isSolvable_of_ker_le_range
      (tDiagonalHom (k := k) n).ker.subtype (tDiagonalHom n) (by
    intro A hA
    exact ⟨⟨A, hA⟩, rfl⟩)

omit [CharZero k] in
private lemma fullFlagStabilizer_isSolvable
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Group.IsSolvable (Variety.Point (fullFlagStabilizer e b).carrierVariety) := by
  let P := fullFlagStabilizer e b
  let toRawGL : Variety.Point P.carrierVariety →*
      GL (Fin (Module.finrank k V)) k :=
    (translationGLPointMulEquiv (k := k)
      (Module.finrank k V)).toMonoidHom.comp P.inclusion.onPoints
  let toV : Variety.Point P.carrierVariety →*
      LinearMap.GeneralLinearGroup k V :=
    (Matrix.GeneralLinearGroup.toLin' e).toMonoidHom.comp toRawGL
  let toGL : Variety.Point P.carrierVariety →*
      GL (Fin (Module.finrank k V)) k :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp toV
  let toT : Variety.Point P.carrierVariety →*
      tTriangularGL k (Module.finrank k V) :=
    toGL.codRestrict (tTriangularGL k (Module.finrank k V)) fun x =>
      fullFlagStabilizer_point_tTriangular e b x
  have htoT : Function.Injective toT := by
    intro x y hxy
    apply P.inclusion_injective
    apply (translationGLPointMulEquiv (k := k)
      (Module.finrank k V)).injective
    apply (Matrix.GeneralLinearGroup.toLin' e).injective
    apply (Matrix.GeneralLinearGroup.toLin' b).symm.injective
    exact congrArg (fun A : tTriangularGL k (Module.finrank k V) => A.1) hxy
  let : Group.IsSolvable (tTriangularGL k (Module.finrank k V)) :=
    tTriangularGL_isSolvable (Module.finrank k V)
  exact Group.isSolvable_of_isSolvable_injective htoT

private lemma fullFlagStabilizer_tangent_mem_of_tTriangular
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e b : Module.Basis (Fin (Module.finrank k V)) k V)
    (D : IdentityPointDerivation (glVarietyOf k V))
    (hD : tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b
        (Bor1.generalLinearIdentityTangentLinearMap e D))) :
    D ∈ LinearMap.range (identityTangentMorphismLinearMap
      (fullFlagStabilizer e b).inclusion) := by
  have hpiece (r : ℕ) (hr : r ≤ Module.finrank k V) :
      D ∈ LinearMap.range (identityTangentMorphismLinearMap
        (fullFlagPiece e b r).inclusion) := by
    by_cases hr0 : r = 0
    · subst r
      have hpieceEq : fullFlagPiece e b 0 =
          Bor1.generalLinearSubspaceStabilizer e ⊥ := by
        simp [fullFlagPiece]
      rw [hpieceEq]
      exact (Bor1.identityTangent_generalLinearSubspaceStabilizer_range_iff
        e ⊥ D).2 (by
          intro w hw
          rw [Submodule.mem_bot] at hw ⊢
          subst w
          exact map_zero _)
    · have hpieceEq : fullFlagPiece e b r =
          Bor1.generalLinearSubspaceStabilizer e (basisInitialSpan b r) := by
        simp [fullFlagPiece, hr0]
      rw [hpieceEq]
      exact (Bor1.identityTangent_generalLinearSubspaceStabilizer_range_iff
        e (basisInitialSpan b r) D).2
          (tTriangular_preserves_basisInitialSpan b
            (Bor1.generalLinearIdentityTangentLinearMap e D) hD r hr)
  have haux : ∀ m : ℕ, m ≤ Module.finrank k V →
      D ∈ LinearMap.range (identityTangentMorphismLinearMap
        (fullFlagStabilizerAux e b m).inclusion) := by
    intro m hm
    induction m with
    | zero => exact hpiece 0 (by omega)
    | succ m ih =>
        rw [fullFlagStabilizerAux,
          identityTangent_range_inter_eq_inf_charZero]
        exact ⟨ih (by omega), hpiece (m + 1) hm⟩
  exact haux (Module.finrank k V) le_rfl

/-- A solvable Lie ideal of the canonical tangent Lie algebra of a reductive
algebraic group is contained in the embedded tangent of its radical. -/
public theorem solvableLieIdeal_le_radicalIdentityTangent
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G)
    (R : ClosedSubgroup G) (hR : IsRadicalSubgroup R)
    (I : LieIdeal k (IdentityPointDerivation G))
    [LieAlgebra.IsSolvable I] :
    I.toSubmodule ≤ LinearMap.range
      (identityTangentMorphismLinearMap R.inclusion) := by
  let V := coordinateTranslationSubmodule G
  let : Module.Finite k V := coordinateTranslationSubmodule_finite G
  let rho := coordinateTranslationRationalRepresentation G
  let e := coordinateTranslationBasis G
  let f := coordinateTranslationRepresentationMorphism G
  let d := Bor1.rationalRepresentationDifferentialLieHom rho e f
  let dI := d.comp I.incl
  let : LieRingModule I V := LieRingModule.compLieHom V dI
  let : LieModule k I V := LieModule.compLieHom V dI
  obtain ⟨b, hb⟩ :=
    exists_basis_lie_action_tTriangular (k := k) (L := I) (V := V)
  let P := fullFlagStabilizer e b
  let H := f.closedSubgroupPreimage P
  let toP : AlgebraicGroup.Morphism H.carrierVariety P.carrierVariety :=
    f.preimageRestriction P
  have htoP : Function.Injective toP.onPoints := by
    intro x y hxy
    apply H.inclusion_injective
    apply coordinateTranslationRepresentationMorphism_injective G
    calc
      f.onPoints (H.inclusion.onPoints x) =
          P.inclusion.onPoints (toP.onPoints x) := by
        symm
        exact f.preimageRestriction_inclusion_apply P x
      _ = P.inclusion.onPoints (toP.onPoints y) :=
        congrArg P.inclusion.onPoints hxy
      _ = f.onPoints (H.inclusion.onPoints y) := by
        exact f.preimageRestriction_inclusion_apply P y
  have hPsolvable : Group.IsSolvable (Variety.Point P.carrierVariety) :=
    fullFlagStabilizer_isSolvable e b
  let : Group.IsSolvable (Variety.Point P.carrierVariety) := hPsolvable
  have hHsolvable : Group.IsSolvable (Variety.Point H.carrierVariety) :=
    Group.isSolvable_of_isSolvable_injective htoP
  have hIH : I.toSubmodule ≤ LinearMap.range
      (identityTangentMorphismLinearMap H.inclusion) := by
    change I.toSubmodule ≤ LinearMap.range
      (Bor1.identityTangentMorphismLinearMap
        (f.closedSubgroupPreimage P).inclusion)
    rw [Bor1.identityTangent_closedSubgroupPreimage_range_eq_comap_charZero]
    intro D hD
    rw [Submodule.mem_comap]
    apply fullFlagStabilizer_tangent_mem_of_tTriangular e b
    have htri := hb ⟨D, hD⟩
    change tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b (d D)) at htri
    change tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b
        ((Bor1.rationalRepresentationDifferentialLieHom rho e f) D))
    exact htri
  have hIinvariant :
      IsInvariantSubmodule (identityTangentRepresentation G) I.toSubmodule := by
    intro g D hD
    have haction :
        ((identityTangentRepresentation G).action g).1 D =
          identityTangentConjugationLinearMap G g D := by
      apply Derivation.ext
      intro a
      rw [identityTangentRepresentation_action_apply,
        identityTangentConjugationLinearMap_apply]
    rw [haction]
    exact Theory.AlgebraicGroup.LieIdeal.identityTangentConjugationLinearMap_mem
      G I hG.1 g hD
  obtain ⟨N, hNH, hNconnected, hNnormal, hIN⟩ :=
    exists_connected_normal_closedSubgroup_le_with_tangent_range
      hG.1 H I.toSubmodule hIinvariant hIH
  let toH : AlgebraicGroup.Morphism N.carrierVariety H.carrierVariety :=
    N.inclusion.codRestrictClosedSubgroup H fun x =>
      hNH (N.pointEquiv x).property
  have htoH : Function.Injective toH.onPoints := by
    intro x y hxy
    apply N.inclusion_injective
    have hxy' := congrArg H.inclusion.onPoints hxy
    simpa [toH,
      AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply] using hxy'
  let : Group.IsSolvable (Variety.Point H.carrierVariety) := hHsolvable
  have hNsolvable : Group.IsSolvable (Variety.Point N.carrierVariety) :=
    Group.isSolvable_of_isSolvable_injective htoH
  have hNR : N ≤ R := hR.maximal N hNnormal hNconnected hNsolvable
  let toR : AlgebraicGroup.Morphism N.carrierVariety R.carrierVariety :=
    N.inclusion.codRestrictClosedSubgroup R fun x =>
      hNR (N.pointEquiv x).property
  intro D hD
  obtain ⟨E, rfl⟩ := hIN hD
  refine ⟨identityTangentMorphismLinearMap toR E, ?_⟩
  have hcomp : R.inclusion.comp toR = N.inclusion := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
      N.inclusion R (fun y => hNR (N.pointEquiv y).property) x
  rw [← hcomp]
  rfl

/-! The preceding integration theorem identifies the Lie radical with the
algebraic radical.  Reductivity then identifies that algebraic subgroup with
the connected algebraic center, whose differential is the Lie center. -/

/-- The canonical tangent Lie algebra of a reductive group has central
radical.  The Killing conclusion is deliberately reserved for its central
quotient or derived semisimple object. -/
public theorem identityTangent_hasCentralRadical_of_reductive
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G) :
    LieAlgebra.HasCentralRadical k (IdentityPointDerivation G) := by
  obtain ⟨R, hR⟩ := exists_radical G
  apply LieAlgebra.hasCentralRadical_of_radical_le
  intro D hD
  have hD' : D ∈ (LieAlgebra.radical k (IdentityPointDerivation G)).toSubmodule := hD
  have hsolv : LieAlgebra.IsSolvable
      (LieAlgebra.radical k (IdentityPointDerivation G)) := inferInstance
  have hle := solvableLieIdeal_le_radicalIdentityTangent hG R hR
    (LieAlgebra.radical k (IdentityPointDerivation G))
  have hrange : D ∈ LinearMap.range
      (identityTangentMorphismLinearMap R.inclusion) := hle hD'
  rw [radical_eq_center_identityComponent_of_reductive hG R hR] at hrange
  have htangent : identityTangentMorphismLinearMap
      ((ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient.inclusion) =
      (identityTangentMorphismLieHom
        ((ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient.inclusion)).toLinearMap := rfl
  have hrange' : D ∈ (identityTangentMorphismLieHom
      ((ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient.inclusion)).range := by
    rcases hrange with ⟨E, hE⟩
    exact ⟨E, hE⟩
  rw [identityComponentCenterTangent_range_eq_lieCenter hG.1] at hrange'
  exact hrange'

end Theory.AlgebraicGroup
