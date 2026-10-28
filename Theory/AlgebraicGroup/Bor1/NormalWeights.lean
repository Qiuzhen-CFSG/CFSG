module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Theory.AlgebraicGroup.Representations.Operations
public import Theory.AlgebraicGroup.Representations.Matrix
public import Theory.AlgebraicGroup.Instance.Stabilizer
public import Theory.AlgebraicGroup.Connected

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Over an algebraically closed field, a finite-dimensional commuting family
has a nonzero common eigenspace. -/
public lemma exists_nontrivial_common_eigenspace_of_commuting_family
    [IsAlgClosed k]
    {ι V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Nontrivial V] (f : ι → Module.End k V)
    (hcomm : Pairwise fun i j => Commute (f i) (f j)) :
    ∃ χ : ι → k, Nontrivial ↥(⨅ i, (f i).eigenspace (χ i)) := by
  generalize hdim : Module.finrank k V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      choose χ hχ using fun i => Module.End.exists_eigenvalue (f i)
      by_cases hall : ∀ i, (f i).eigenspace (χ i) = ⊤
      · refine ⟨χ, ?_⟩
        have htop : (⨅ i, (f i).eigenspace (χ i)) = ⊤ := by simp [hall]
        rw [htop]
        exact Equiv.nontrivial Submodule.topEquiv.toEquiv
      · obtain ⟨i, hi⟩ := not_forall.mp hall
        let E : Submodule k V := (f i).eigenspace (χ i)
        haveI : Nontrivial E := (Submodule.nontrivial_iff_ne_bot).mpr (hχ i)
        have hE_lt : Module.finrank k E < n := by
          rw [← hdim]
          exact Submodule.finrank_lt hi
        have hstable (j : ι) : Set.MapsTo (f j) E E := by
          dsimp [E]
          by_cases hij : i = j
          · subst j
            exact Module.End.mapsTo_genEigenspace_of_comm (Commute.refl _) (χ i) 1
          · exact Module.End.mapsTo_genEigenspace_of_comm (hcomm hij) (χ i) 1
        let fE : ι → Module.End k E := fun j => (f j).restrict (hstable j)
        have hcommE : Pairwise fun a b => Commute (fE a) (fE b) := by
          intro a b hab
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          have hc := LinearMap.congr_fun (hcomm hab).eq (x : E)
          change (f a) ((f b) (x : E)) = (f b) ((f a) (x : E))
          exact hc
        obtain ⟨χE, hχE⟩ := ih (Module.finrank k E) hE_lt fE hcommE rfl
        let W : Submodule k E := ⨅ j, (fE j).eigenspace (χE j)
        letI : Nontrivial W := hχE
        obtain ⟨x, hx⟩ := exists_ne (0 : W)
        refine ⟨χE, ?_⟩
        rw [Submodule.nontrivial_iff_ne_bot]
        intro hbot
        have hxmem : (x : E) ∈ ⨅ j, (fE j).eigenspace (χE j) := x.property
        have hxmem' : (x : V) ∈ ⨅ j, (f j).eigenspace (χE j) := by
          rw [Submodule.mem_iInf] at hxmem ⊢
          intro j
          exact Module.End.eigenspace_restrict_le_eigenspace
            (f j) (hstable j) (χE j) ⟨x, hxmem j, rfl⟩
        rw [hbot] at hxmem'
        have hxzeroV : (x : V) = 0 := (Submodule.mem_bot k).mp hxmem'
        apply hx
        apply Subtype.ext
        apply Subtype.ext
        exact hxzeroV

/-- The weight of a normal subgroup obtained by transporting a character
along conjugation by an ambient group element. -/
@[expose]
public def normalSubgroupConjugateWeight
    {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]
    (χ : N → k) (g : Γ) : N → k := fun n =>
  χ ⟨g⁻¹ * n * g, by
    simpa using (inferInstance : N.Normal).conj_mem n n.property g⁻¹⟩

/-- Choose a basis of a finite-dimensional space whose initial block spans a
given subspace. -/
public lemma exists_basis_span_initial_Bor1
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W : Submodule k V) :
    ∃ (e : Module.Basis (Fin (Module.finrank k V)) k V)
      (hr : Module.finrank k W ≤ Module.finrank k V),
      W = Submodule.span k (Set.range (fun j : Fin (Module.finrank k W) =>
        e (Fin.castLE hr j))) := by
  let bW := Module.finBasis k W
  let bQ := Module.finBasis k (V ⧸ W)
  have hdim : Module.finrank k W + Module.finrank k (V ⧸ W) =
      Module.finrank k V := by
    rw [add_comm]
    exact W.finrank_quotient_add_finrank
  let idx : (Fin (Module.finrank k W) ⊕ Fin (Module.finrank k (V ⧸ W))) ≃
      Fin (Module.finrank k V) := finSumFinEquiv.trans (finCongr hdim)
  let e := (bW.sumQuot bQ).reindex idx
  have hr : Module.finrank k W ≤ Module.finrank k V := by omega
  refine ⟨e, hr, ?_⟩
  have he (j : Fin (Module.finrank k W)) :
      e (Fin.castLE hr j) = (bW j : V) := by
    have hj : idx (Sum.inl j) = Fin.castLE hr j := by
      apply Fin.ext
      rfl
    rw [← hj]
    simp [e, idx, Module.Basis.reindex_apply]
  rw [show (Set.range fun j : Fin (Module.finrank k W) =>
      e (Fin.castLE hr j)) = Set.range fun j : Fin (Module.finrank k W) =>
      (bW j : V) by
        ext x
        simp only [Set.mem_range]
        constructor <;> rintro ⟨j, rfl⟩ <;> exact ⟨j, by simp [he]⟩]
  rw [show (Set.range fun j : Fin (Module.finrank k W) => (bW j : V)) =
      W.subtype '' Set.range bW by
        ext x
        constructor
        · rintro ⟨j, rfl⟩
          exact ⟨bW j, ⟨j, rfl⟩, rfl⟩
        · rintro ⟨w, ⟨j, rfl⟩, rfl⟩
          exact ⟨j, rfl⟩]
  rw [← Submodule.map_span, bW.span_eq, Submodule.map_top,
    Submodule.range_subtype]

/-- The stabilizer of a subspace in a finite-dimensional rational
representation is Zariski closed. -/
public lemma RationalRepresentation.subspaceStabilizer_isZariskiClosed_Bor1
    {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [IsAlgClosed k]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (W : Submodule k V) :
    IsZariskiClosed G {g : Variety.Point G |
      Submodule.map (ρ.action g : Module.End k V) W = W} := by
  rcases hρ with ⟨b, f, hf⟩
  obtain ⟨e, hr, hW⟩ := exists_basis_span_initial_Bor1 (k := k) W
  let matrixCoefficient : Fin (Module.finrank k V) →
      Fin (Module.finrank k V) → G.PolynomialFunction := fun i j =>
    rationalRepresentationLinearMatrixCoefficient ρ b f (e.dualBasis i) (e j)
  have matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        e.repr ((ρ.action g : Module.End k V) (e j)) i := by
    intro i j g
    rw [show matrixCoefficient i j =
      rationalRepresentationLinearMatrixCoefficient ρ b f
        (e.dualBasis i) (e j) by rfl]
    rw [rationalRepresentationLinearMatrixCoefficient_apply ρ b f hf]
    exact Module.Basis.dualBasis_apply e i
      ((ρ.action g : Module.End k V) (e j))
  let inverseMatrixCoefficient : Fin (Module.finrank k V) →
      Fin (Module.finrank k V) → G.PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G)
      (matrixCoefficient i j)
  have inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        e.repr (((((ρ.action g)⁻¹ : LinearMap.GeneralLinearGroup k V) :
          Module.End k V)) (e j)) i := by
    intro i j g
    change matrixCoefficient i j g⁻¹ = _
    rw [matrixCoefficient_apply]
    simp
  let F := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    e ρ.action matrixCoefficient inverseMatrixCoefficient
      matrixCoefficient_apply inverseMatrixCoefficient_apply
  have hclosed : IsZariskiClosed G
      (F.toVariety.toFun ⁻¹'
        stabMatrixSet (Module.finrank k V) (Module.finrank k W)) :=
    F.toVariety.isZariskiClosed_preimage
      (stabMatrixSet_closed (Module.finrank k V) (Module.finrank k W))
  have hstabilizer (x : Variety.Point (glVariety (Module.finrank k V) : Variety k)) :
      x ∈ stabMatrixSet (Module.finrank k V) (Module.finrank k W) ↔
        Submodule.map
          ((glPointEquivOf k V e x : LinearMap.GeneralLinearGroup k V) :
            Module.End k V) W = W := by
    have hstab := subspaceStabilizer_matrix_iff V W e (Module.finrank k W) hr hW x
    constructor
    · intro hmaps
      have hmaps' := hstab.mp hmaps
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.map_le_iff_le_comap]
        intro w hw
        exact hmaps' w hw
      · exact LinearEquiv.finrank_map_eq
          (LinearMap.GeneralLinearGroup.toLinearEquiv
            (glPointEquivOf k V e x)) W
    · intro hmap
      apply hstab.mpr
      intro w' hw'
      have hwmap :
          ((glPointEquivOf k V e x : LinearMap.GeneralLinearGroup k V) :
            Module.End k V) w' ∈
            Submodule.map
              ((glPointEquivOf k V e x : LinearMap.GeneralLinearGroup k V) :
                Module.End k V) W :=
        ⟨w', hw', rfl⟩
      rw [hmap] at hwmap
      exact hwmap
  rw [show {g : Variety.Point G |
      Submodule.map (ρ.action g : Module.End k V) W = W} =
      F.toVariety.toFun ⁻¹'
        stabMatrixSet (Module.finrank k V) (Module.finrank k W) by
    ext g
    change Submodule.map (ρ.action g : Module.End k V) W = W ↔
      F.onPoints g ∈ stabMatrixSet (Module.finrank k V) (Module.finrank k W)
    rw [hstabilizer]
    rw [show glPointEquivOf k V e (F.onPoints g) = ρ.action g by
      change glPointEquivOf k V e
        (generalLinearRepresentationPoint e (ρ.action g)) = ρ.action g
      exact glPointEquivOf_generalLinearRepresentationPoint e (ρ.action g)]]
  exact hclosed

/-- An ambient group element sends a common eigenvector for a normal subgroup
to a common eigenvector of the transported weight. -/
public lemma Representation.commonEigenvector_conjugateWeight
    {Γ V : Type*} [Group Γ] [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal]
    (χ : N → k) (v : V) (hv : ∀ n : N, ρ n v = χ n • v)
    (g : Γ) :
    ∀ n : N, ρ n (ρ g v) = normalSubgroupConjugateWeight N χ g n • ρ g v := by
  intro n
  let q : N := ⟨g⁻¹ * n * g, by
    simpa using (inferInstance : N.Normal).conj_mem n n.property g⁻¹⟩
  change ρ n (ρ g v) = χ q • ρ g v
  calc
    ρ n (ρ g v) = ρ (n * g) v := by
      rw [map_mul]
      rfl
    _ = ρ (g * q) v := by
      congr 2
      dsimp [q]
      group
    _ = ρ g (ρ q v) := by
      rw [map_mul]
      rfl
    _ = ρ g (χ q • v) := by rw [hv q]
    _ = χ q • ρ g v := by rw [map_smul]

/-- Conjugation transports the whole common weight space, not only its
nonzero vectors. -/
public lemma Representation.commonEigenspace_conjugateWeight_eq_map
    {Γ V : Type*} [Group Γ] [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal]
    (χ : N → k) (g : Γ) :
    Submodule.map (ρ g : Module.End k V)
      (⨅ n : N, Module.End.eigenspace (ρ n) (χ n)) =
      (⨅ n : N, Module.End.eigenspace (ρ n)
        (normalSubgroupConjugateWeight N χ g n)) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro v hv
    rw [Submodule.mem_iInf] at hv
    change ρ g v ∈ ⨅ n : N, Module.End.eigenspace (ρ n)
      (normalSubgroupConjugateWeight N χ g n)
    rw [Submodule.mem_iInf]
    have hveigen : ∀ n : N, ρ n v = χ n • v := fun n =>
      Module.End.mem_eigenspace_iff.mp (hv n)
    intro n
    exact Module.End.mem_eigenspace_iff.mpr
      (Representation.commonEigenvector_conjugateWeight ρ N χ v hveigen g n)
  · intro y hy
    rw [Submodule.mem_iInf] at hy
    let x : V := ρ g⁻¹ y
    have hx : x ∈ ⨅ n : N, Module.End.eigenspace (ρ n) (χ n) := by
      rw [Submodule.mem_iInf]
      intro m
      apply Module.End.mem_eigenspace_iff.mpr
      let n : N := ⟨g * m * g⁻¹, by
        simpa using (inferInstance : N.Normal).conj_mem m m.property g⟩
      have hyn := Module.End.mem_eigenspace_iff.mp (hy n)
      change ρ m (ρ g⁻¹ y) = χ m • ρ g⁻¹ y
      calc
        ρ m (ρ g⁻¹ y) = ρ (m * g⁻¹) y := by rw [map_mul]; rfl
        _ = ρ (g⁻¹ * n) y := by
          congr 2
          dsimp [n]
          group
        _ = ρ g⁻¹ (ρ n y) := by rw [map_mul]; rfl
        _ = ρ g⁻¹ (normalSubgroupConjugateWeight N χ g n • y) := by rw [hyn]
        _ = χ m • ρ g⁻¹ y := by
          rw [map_smul]
          congr 1
          dsimp [normalSubgroupConjugateWeight, n]
          congr 1
          apply Subtype.ext
          group
    refine ⟨x, hx, ?_⟩
    dsimp [x]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

/-- A nonzero common weight space remains nonzero after conjugation. -/
public lemma Representation.commonEigenspace_conjugateWeight_ne_bot
    {Γ V : Type*} [Group Γ] [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal]
    (χ : N → k)
    (hχ : (⨅ n : N, Module.End.eigenspace (ρ n) (χ n)) ≠ ⊥)
    (g : Γ) :
    (⨅ n : N, Module.End.eigenspace (ρ n)
      (normalSubgroupConjugateWeight N χ g n)) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hχ ⊢
  obtain ⟨v, hv, hvne⟩ := hχ
  refine ⟨ρ g v, ?_, ?_⟩
  · rw [Submodule.mem_iInf] at hv ⊢
    have hveigen : ∀ n : N, ρ n v = χ n • v := fun n =>
      Module.End.mem_eigenspace_iff.mp (hv n)
    intro n
    exact Module.End.mem_eigenspace_iff.mpr
      (Representation.commonEigenvector_conjugateWeight ρ N χ v hveigen g n)
  · intro hz
    apply hvne
    apply (ρ.apply_bijective g).1
    simpa using hz

/-- In finite dimensions, a commuting action has only finitely many nonzero
common weight spaces. -/
private lemma finite_nontrivial_common_eigenspaces_of_commuting_family
    {ι V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : ι → Module.End k V)
    (hcomm : Pairwise fun i j => Commute (f i) (f j)) :
    Finite {χ : ι → k // (⨅ i, (f i).eigenspace (χ i)) ≠ ⊥} := by
  have hstable : ∀ i j φ,
      Set.MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ) := by
    intro i j φ
    by_cases hij : j = i
    · subst j
      exact Module.End.mapsTo_genEigenspace_of_comm (Commute.refl _) φ ⊤
    · exact Module.End.mapsTo_genEigenspace_of_comm (hcomm hij) φ ⊤
  have hmax : iSupIndep fun χ : ι → k =>
      ⨅ i, (f i).maxGenEigenspace (χ i) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hstable
  have heig : iSupIndep fun χ : ι → k =>
      ⨅ i, (f i).eigenspace (χ i) := by
    apply hmax.mono
    intro χ
    exact iInf_mono fun i => Module.End.eigenspace_le_maxGenEigenspace
  letI : Fintype {χ : ι → k // (⨅ i, (f i).eigenspace (χ i)) ≠ ⊥} :=
    heig.fintypeNeBotOfFiniteDimensional
  exact Finite.of_fintype _

/-- The orbit of a nonzero common weight space is finite when the subgroup
acts by commuting operators. -/
public lemma Representation.finite_commonEigenspace_orbit_of_normal_commuting_action
    {Γ V : Type*} [Group Γ] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal]
    (hcomm : Pairwise fun a b : N => Commute (ρ a) (ρ b))
    (χ : N → k)
    (hχ : (⨅ n : N, Module.End.eigenspace (ρ n) (χ n)) ≠ ⊥) :
    (Set.range fun g : Γ => Submodule.map (ρ g : Module.End k V)
      (⨅ n : N, Module.End.eigenspace (ρ n) (χ n))).Finite := by
  let A := {ψ : N → k //
    (⨅ n : N, Module.End.eigenspace (ρ n) (ψ n)) ≠ ⊥}
  letI : Finite A := finite_nontrivial_common_eigenspaces_of_commuting_family
    (fun n : N => (ρ n : Module.End k V)) hcomm
  let F : A → Submodule k V := fun ψ =>
    ⨅ n : N, Module.End.eigenspace (ρ n) (ψ.1 n)
  apply (Set.finite_range F).subset
  rintro U ⟨g, rfl⟩
  let ψ : A := ⟨normalSubgroupConjugateWeight N χ g,
    Representation.commonEigenspace_conjugateWeight_ne_bot ρ N χ hχ g⟩
  refine ⟨ψ, ?_⟩
  dsimp [F, ψ]
  exact (Representation.commonEigenspace_conjugateWeight_eq_map ρ N χ g).symm

/-- If a connected algebraic group moves a subspace through only finitely many
subspaces, and the subspace stabilizer is closed, then the subspace is fixed
by the whole group. -/
public lemma Representation.subspace_invariant_of_connected_of_finite_orbit
    {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k (Variety.Point G) V)
    (W : Submodule k V)
    (hG : Variety.IsConnected G)
    (hclosed : IsZariskiClosed G
      {g : Variety.Point G | Submodule.map (ρ g : Module.End k V) W = W})
    (hfinite : (Set.range fun g : Variety.Point G =>
      Submodule.map (ρ g : Module.End k V) W).Finite) :
    ∀ g : Variety.Point G, Submodule.map (ρ g : Module.End k V) W = W := by
  letI : MulAction (Variety.Point G) (Submodule k V) := {
    smul g U := Submodule.map (ρ g : Module.End k V) U
    one_smul U := by
      change Submodule.map (ρ 1 : Module.End k V) U = U
      rw [map_one]
      exact Submodule.map_id U
    mul_smul g h U := by
      change Submodule.map (ρ (g * h) : Module.End k V) U =
        Submodule.map (ρ g : Module.End k V)
          (Submodule.map (ρ h : Module.End k V) U)
      rw [map_mul]
      exact Submodule.map_comp (ρ h : Module.End k V) (ρ g : Module.End k V) U }
  let S : Subgroup (Variety.Point G) :=
    MulAction.stabilizer (Variety.Point G) W
  have hScarr : (S : Set (Variety.Point G)) =
      {g : Variety.Point G | Submodule.map (ρ g : Module.End k V) W = W} := rfl
  let K : ClosedSubgroup G :=
    ClosedSubgroup.ofSubgroup S (by simpa [hScarr] using hclosed)
  have horbit : (MulAction.orbit (Variety.Point G) W).Finite := by
    rw [MulAction.orbit]
    change (Set.range fun g : Variety.Point G =>
      Submodule.map (ρ g : Module.End k V) W).Finite
    exact hfinite
  letI : Fintype (MulAction.orbit (Variety.Point G) W) := horbit.fintype
  letI : Finite (MulAction.orbit (Variety.Point G) W) := Finite.of_fintype _
  letI : Finite (Variety.Point G ⧸ S) :=
    Finite.of_equiv (MulAction.orbit (Variety.Point G) W)
      (MulAction.orbitEquivQuotientStabilizer (Variety.Point G) W)
  letI : S.FiniteIndex := S.finiteIndex_of_finite_quotient
  letI : K.toSubgroup.FiniteIndex := by
    change S.FiniteIndex
    infer_instance
  have hcomponent : AlgebraicGroup.identityComponent G ⊆
      (K.toSubgroup : Set (Variety.Point G)) :=
    identityComponent_subset_of_finiteIndexSubgroup G K
  have htop : AlgebraicGroup.identityComponent G = Set.univ :=
    (identityComponent_eq_univ_iff_isConnected G).mpr hG
  intro g
  have hgK : g ∈ K.toSubgroup := hcomponent (by rw [htop]; trivial)
  change g • W = W
  exact hgK

/-- The preceding linear-algebra and connectedness steps combine as follows:
if the stabilizer of every candidate subspace is closed, a nonzero common
weight space for a normal commuting subgroup can be chosen invariant under
the connected ambient group. -/
public lemma Representation.exists_invariant_commonEigenspace_of_normal_commuting_action
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k (Variety.Point G) V)
    (N : Subgroup (Variety.Point G)) [N.Normal]
    (hcomm : Pairwise fun a b : N => Commute (ρ a) (ρ b))
    (hG : Variety.IsConnected G)
    (hclosed : ∀ W : Submodule k V, IsZariskiClosed G
      {g : Variety.Point G | Submodule.map (ρ g : Module.End k V) W = W}) :
    ∃ (χ : N → k) (W : Submodule k V),
      W ≠ ⊥ ∧
      (∀ g : Variety.Point G,
        Submodule.map (ρ g : Module.End k V) W = W) ∧
      ∀ (n : N) (w : V), w ∈ W →
        (ρ n : Module.End k V) w = χ n • w := by
  obtain ⟨χ, hχnontrivial⟩ :=
    exists_nontrivial_common_eigenspace_of_commuting_family
      (fun n : N => (ρ n : Module.End k V)) hcomm
  let W : Submodule k V :=
    ⨅ n : N, Module.End.eigenspace (ρ n : Module.End k V) (χ n)
  have hχ : W ≠ ⊥ := by
    rw [← Submodule.nontrivial_iff_ne_bot]
    exact hχnontrivial
  have hfinite : (Set.range fun g : Variety.Point G =>
      Submodule.map (ρ g : Module.End k V) W).Finite := by
    rw [show W = ⨅ n : N,
      Module.End.eigenspace (ρ n : Module.End k V) (χ n) by rfl]
    exact finite_commonEigenspace_orbit_of_normal_commuting_action
      ρ N hcomm χ hχ
  have hinvariant : ∀ g : Variety.Point G,
      Submodule.map (ρ g : Module.End k V) W = W :=
    subspace_invariant_of_connected_of_finite_orbit
      ρ W hG (hclosed W) hfinite
  refine ⟨χ, W, hχ, hinvariant, ?_⟩
  intro n w hw
  apply Module.End.mem_eigenspace_iff.mp
  have hwall : w ∈ ⨅ m : N,
      Module.End.eigenspace (ρ m : Module.End k V) (χ m) := hw
  rw [Submodule.mem_iInf] at hwall
  exact hwall n

/-- Bor1's invariant-weight-space construction for a rational representation:
the matrix-coefficient argument supplies the closed-stabilizer hypothesis
needed by the abstract representation lemma above. -/
public lemma RationalRepresentation.exists_invariant_commonEigenspace_of_normal_commuting_action_Bor1
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (N : Subgroup (Variety.Point G)) [N.Normal]
    (hcomm : Pairwise fun a b : N =>
      Commute (ρ.action a : Module.End k V) (ρ.action b : Module.End k V))
    (hG : Variety.IsConnected G) :
    ∃ (χ : N → k) (W : Submodule k V),
      W ≠ ⊥ ∧
      (∀ g : Variety.Point G,
        Submodule.map (ρ.action g : Module.End k V) W = W) ∧
      ∀ (n : N) (w : V), w ∈ W →
        (ρ.action n : Module.End k V) w = χ n • w := by
  let σ : Representation k (Variety.Point G) V :=
    (Units.coeHom (Module.End k V)).comp ρ.action
  have hcommσ : Pairwise fun a b : N => Commute (σ a) (σ b) := by
    exact hcomm
  have hclosedσ : ∀ W : Submodule k V, IsZariskiClosed G
      {g : Variety.Point G | Submodule.map (σ g : Module.End k V) W = W} := by
    intro W
    exact RationalRepresentation.subspaceStabilizer_isZariskiClosed_Bor1 ρ hρ W
  obtain ⟨χ, W, hWne, hWinv, hweight⟩ :=
    Representation.exists_invariant_commonEigenspace_of_normal_commuting_action
      σ N hcommσ hG hclosedσ
  refine ⟨χ, W, hWne, ?_, ?_⟩
  · exact hWinv
  · intro n w hw
    exact hweight n w hw

end Theory.AlgebraicGroup.Bor1
