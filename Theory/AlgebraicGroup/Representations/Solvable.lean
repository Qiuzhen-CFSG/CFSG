module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Theory.AlgebraicGroup.Instance.Stabilizer
public import Theory.AlgebraicGroup.Instance.Triangular
public import Theory.AlgebraicGroup.Representations.Operations
public import Theory.AlgebraicGroup.Representations.Unipotent.Flag
public import Theory.AlgebraicGroup.Solvable.Basic

universe u

set_option linter.style.haveILetI false

/-! Lie--Kolchin theory for finite-dimensional rational representations of
connected solvable algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A commuting finite-dimensional family over an algebraically closed field
has a nontrivial common eigenspace. -/
private lemma exists_nontrivial_common_eigenspace_of_commuting_family
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
        have : Nontrivial E := (Submodule.nontrivial_iff_ne_bot).mpr (hχ i)
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
        let : Nontrivial W := hχE
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

omit [IsAlgClosed k] in
/-- In finite dimensions, a commuting family has only finitely many
nontrivial simultaneous eigenspaces. -/
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

/-- Conjugation transports a weight of a normal subgroup. -/
private def normalSubgroupConjugateWeight
    {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]
    (χ : N → k) (g : Γ) : N → k := fun n =>
  χ ⟨g⁻¹ * n * g, by
    simpa using (inferInstance : N.Normal).conj_mem n n.property g⁻¹⟩

omit [IsAlgClosed k] in
/-- A finite-dimensional subspace admits a basis of the ambient space whose
initial block spans the subspace. -/
private lemma exists_basis_span_initial
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
  rw [show (Set.range fun j : Fin (Module.finrank k W) => e (Fin.castLE hr j)) =
      Set.range fun j : Fin (Module.finrank k W) => (bW j : V) by
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
private lemma RationalRepresentation.subspaceStabilizer_isZariskiClosed
    {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (W : Submodule k V) :
    IsZariskiClosed G {g : Variety.Point G |
      Submodule.map (ρ.action g : Module.End k V) W = W} := by
  rcases hρ with ⟨b, f, hf⟩
  obtain ⟨e, hr, hW⟩ := exists_basis_span_initial (k := k) W
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

omit [IsAlgClosed k] in
/-- An ambient group element sends a common eigenvector for a normal subgroup
to a common eigenvector of the conjugated weight. -/
private lemma Representation.commonEigenvector_conjugateWeight
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

omit [IsAlgClosed k] in
/-- The span of the ambient orbit of a common eigenvector for a normal
subgroup is nonzero and ambient-invariant, and the normal subgroup acts on it
by commuting operators. -/
private lemma Representation.exists_invariant_orbitSpan_of_normal_commonEigenvector
    {Γ V : Type*} [Group Γ] [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal]
    (χ : N → k) (v : V) (hvne : v ≠ 0)
    (hv : ∀ n : N, ρ n v = χ n • v) :
    ∃ W : Submodule k V,
      W ≠ ⊥ ∧
      (∀ g : Γ, Submodule.map (ρ g : Module.End k V) W = W) ∧
      ∀ a b : N, ∀ w ∈ W, ρ a (ρ b w) = ρ b (ρ a w) := by
  let W : Submodule k V := Submodule.span k (Set.range fun g : Γ => ρ g v)
  have hvW : v ∈ W := by
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    simp
  have hWne : W ≠ ⊥ := by
    intro hW
    have hvzero : v = 0 := by
      have hvbot : v ∈ (⊥ : Submodule k V) := by
        rw [← hW]
        exact hvW
      simpa using hvbot
    exact hvne hvzero
  have hforward (g : Γ) :
      Submodule.map (ρ g : Module.End k V) W ≤ W := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    change ρ g (ρ h v) ∈ W
    apply Submodule.subset_span
    refine ⟨g * h, ?_⟩
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl
  have hinvariant (g : Γ) :
      Submodule.map (ρ g : Module.End k V) W = W := by
    apply le_antisymm (hforward g)
    intro w hw
    refine ⟨ρ g⁻¹ w, ?_, ?_⟩
    · have hw' : ρ g⁻¹ w ∈
          Submodule.map (ρ g⁻¹ : Module.End k V) W :=
        ⟨w, hw, rfl⟩
      exact hforward g⁻¹ hw'
    · rw [← Module.End.mul_apply, ← map_mul]
      simp
  refine ⟨W, hWne, hinvariant, ?_⟩
  intro a b w hw
  refine Submodule.span_induction
    (p := fun w _ => ρ a (ρ b w) = ρ b (ρ a w)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨g, rfl⟩
    have ha := Representation.commonEigenvector_conjugateWeight ρ N χ v hv g a
    have hb := Representation.commonEigenvector_conjugateWeight ρ N χ v hv g b
    rw [hb, ha, map_smul, map_smul, ha, hb]
    simp [smul_smul, mul_comm]
  · simp
  · intro x y hx hy hxe hye
    simp only [map_add]
    rw [hxe, hye]
  · intro c x hx hxe
    simp only [map_smul]
    rw [hxe]

omit [IsAlgClosed k] in
/-- Conjugation preserves nontriviality of a normal subgroup's common weight
space. -/
private lemma Representation.commonEigenspace_conjugateWeight_ne_bot
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

omit [IsAlgClosed k] in
/-- Conjugation transports the whole common weight space of a normal
subgroup, not merely its nonzero vectors. -/
private lemma Representation.commonEigenspace_conjugateWeight_eq_map
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

omit [IsAlgClosed k] in
/-- The orbit of a nontrivial common weight space of a normal subgroup
is finite when that subgroup acts by commuting operators. -/
private lemma Representation.finite_commonEigenspace_orbit_of_normal_commuting_action
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
  let : Finite A := finite_nontrivial_common_eigenspaces_of_commuting_family
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

omit [IsAlgClosed k] in
/-- A finite orbit of a subspace under a rational representation of a
connected algebraic group is constant as soon as its stabilizer is Zariski
closed. -/
private lemma Representation.subspace_invariant_of_connected_of_finite_orbit
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
  let : Finite (MulAction.orbit (Variety.Point G) W) := Finite.of_fintype _
  let : Finite (Variety.Point G ⧸ S) :=
    Finite.of_equiv (MulAction.orbit (Variety.Point G) W)
      (MulAction.orbitEquivQuotientStabilizer (Variety.Point G) W)
  let : S.FiniteIndex := S.finiteIndex_of_finite_quotient
  let : K.toSubgroup.FiniteIndex := by
    change S.FiniteIndex
    infer_instance
  have hcomponent : AlgebraicGroup.identityComponent G ⊆
      (K.toSubgroup : Set (Variety.Point G)) := identityComponent_subset_of_finiteIndexSubgroup G K
  have htop : AlgebraicGroup.identityComponent G = Set.univ :=
    (identityComponent_eq_univ_iff_isConnected G).mpr hG
  intro g
  have hgK : g ∈ K.toSubgroup := hcomponent (by rw [htop]; trivial)
  change g • W = W
  exact hgK

/-- A normal subgroup acting by commuting operators in a rational
representation of a connected algebraic group has a nonzero ambient-invariant
common weight space. -/
private lemma RationalRepresentation.exists_invariant_commonEigenspace_of_normal_commuting_action
    {G : Variety k} [AlgebraicGroup G]
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
  obtain ⟨χ, hχnontrivial⟩ :=
    exists_nontrivial_common_eigenspace_of_commuting_family
      (fun n : N => (ρ.action n : Module.End k V)) hcomm
  set W : Submodule k V :=
    ⨅ n : N, Module.End.eigenspace (ρ.action n : Module.End k V) (χ n)
      with hW
  have hχ : W ≠ ⊥ := by
    rw [hW, ← Submodule.nontrivial_iff_ne_bot]
    exact hχnontrivial
  let σ : Representation k (Variety.Point G) V :=
    (Units.coeHom (Module.End k V)).comp ρ.action
  have hcommσ : Pairwise fun a b : N => Commute (σ a) (σ b) := by
    exact hcomm
  have hχ0 : (⨅ n : N, Module.End.eigenspace (σ n) (χ n)) ≠ ⊥ := by
    rw [show (⨅ n : N, Module.End.eigenspace (σ n) (χ n)) = W by
      rw [hW]
      rfl]
    exact hχ
  have hfinite0 : (Set.range fun g : Variety.Point G =>
      Submodule.map (σ g : Module.End k V)
        (⨅ n : N, Module.End.eigenspace (σ n) (χ n))).Finite :=
    Representation.finite_commonEigenspace_orbit_of_normal_commuting_action
      (k := k) (ρ := σ) (N := N) hcommσ χ hχ0
  have hfiniteσ : (Set.range fun g : Variety.Point G =>
      Submodule.map (σ g) W).Finite := by
    rw [hW]
    exact hfinite0
  have hclosedσ : IsZariskiClosed G {g : Variety.Point G |
      Submodule.map (σ g) W = W} := by
    exact ρ.subspaceStabilizer_isZariskiClosed hρ W
  have hinvariantσ : ∀ g : Variety.Point G,
      Submodule.map (σ g) W = W :=
    Representation.subspace_invariant_of_connected_of_finite_orbit
      σ W hG hclosedσ hfiniteσ
  have hinvariant : ∀ g : Variety.Point G,
      Submodule.map (ρ.action g : Module.End k V) W = W := by
    exact hinvariantσ
  refine ⟨χ, W, hχ, hinvariant, ?_⟩
  intro n w hw
  apply Module.End.mem_eigenspace_iff.mp
  have hwall : w ∈ ⨅ m : N,
      Module.End.eigenspace (ρ.action m : Module.End k V) (χ m) := by
    rw [← hW]
    exact hw
  rw [Submodule.mem_iInf] at hwall
  exact hwall n

/-- If every commutator in a nonzero finite-dimensional rational
representation of a connected algebraic group acts by a scalar, then the
representation is commutative. -/
private lemma RationalRepresentation.commutes_of_connected_of_commutator_scalars
    {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Nontrivial V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (hG : Variety.IsConnected G)
    (hscalar : ∀ x y : Variety.Point G, ∃ c : k,
      (ρ.action (x * y * x⁻¹ * y⁻¹) : Module.End k V) = c • LinearMap.id) :
    ∀ x y : Variety.Point G, ρ.action x * ρ.action y = ρ.action y * ρ.action x := by
  rcases hρ with ⟨e, f, hf⟩
  let q : Variety.Morphism (Variety.prod G G) (glVarietyOf k V) :=
    f.toVariety.comp (AlgebraicGroup.commutatorMorphism G)
  let roots : Set k := {c | c ^ Module.finrank k V = 1}
  have hroots : roots.Finite := by
    let p : Polynomial k := Polynomial.X ^ Module.finrank k V - 1
    apply (Polynomial.finite_setOfPred_isRoot (p := p) (by
      rw [show p = Polynomial.X ^ Module.finrank k V - Polynomial.C 1 by rfl]
      exact Polynomial.X_pow_sub_C_ne_zero Module.finrank_pos 1)).subset
    intro c hc
    change p.IsRoot c
    simpa [p, Polynomial.IsRoot, roots, sub_eq_zero] using hc
  have hscalarRoot (x y : Variety.Point G) :
      ∃ c ∈ roots,
        (ρ.action (x * y * x⁻¹ * y⁻¹) : Module.End k V) = c • LinearMap.id := by
    obtain ⟨c, hc⟩ := hscalar x y
    refine ⟨c, ?_, hc⟩
    change c ^ Module.finrank k V = 1
    have hdet := congrArg LinearMap.det hc
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one] at hdet
    let δ : LinearMap.GeneralLinearGroup k V →* kˣ :=
      LinearEquiv.det.comp
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom
    have hδ : δ (ρ.action (x * y * x⁻¹ * y⁻¹)) = 1 := by
      simp [δ, map_mul]
    have hδcoe (a : LinearMap.GeneralLinearGroup k V) :
        ↑(δ a) = LinearMap.det (a : Module.End k V) := by
      simp [δ]
    rw [← hδcoe, hδ] at hdet
    simpa using hdet.symm
  have hendFinite : (Set.range fun z : Variety.Point (Variety.prod G G) =>
      (ρ.action ((AlgebraicGroup.commutatorMorphism G).toFun z) :
        Module.End k V)).Finite := by
    apply (hroots.image fun c : k => c • LinearMap.id).subset
    rintro A ⟨z, rfl⟩
    obtain ⟨⟨x, y⟩, rfl⟩ := (Variety.prodPointEquiv G G).symm.surjective z
    obtain ⟨c, hcroot, hc⟩ := hscalarRoot x y
    refine ⟨c, hcroot, ?_⟩
    change c • LinearMap.id =
      (ρ.action ((AlgebraicGroup.commutatorMorphism G).toFun
        ((Variety.prodPointEquiv G G).symm (x, y))) : Module.End k V)
    rw [AlgebraicGroup.commutatorMorphism_apply]
    exact hc.symm
  have hactionFinite : (Set.range fun z : Variety.Point (Variety.prod G G) =>
      ρ.action ((AlgebraicGroup.commutatorMorphism G).toFun z)).Finite := by
    apply Set.Finite.of_finite_image (f := fun a : LinearMap.GeneralLinearGroup k V =>
      (a : Module.End k V))
    · have himage : (fun a : LinearMap.GeneralLinearGroup k V =>
          (a : Module.End k V)) ''
          (Set.range fun z : Variety.Point (Variety.prod G G) =>
            ρ.action ((AlgebraicGroup.commutatorMorphism G).toFun z)) =
          Set.range fun z : Variety.Point (Variety.prod G G) =>
            (ρ.action ((AlgebraicGroup.commutatorMorphism G).toFun z) :
              Module.End k V) := by
        ext A
        constructor
        · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
          exact ⟨z, rfl⟩
        · rintro ⟨z, rfl⟩
          exact ⟨ρ.action ((AlgebraicGroup.commutatorMorphism G).toFun z),
            ⟨z, rfl⟩, rfl⟩
      rw [himage]
      exact hendFinite
    · intro a _ b _ hab
      exact Units.ext hab
  have hqFinite : (Set.range q.toFun).Finite := by
    apply Set.Finite.of_finite_image (f := glPointEquivOf k V e)
    · have heq : (glPointEquivOf k V e) '' Set.range q.toFun =
          Set.range fun z : Variety.Point (Variety.prod G G) =>
            ρ.action ((AlgebraicGroup.commutatorMorphism G).toFun z) := by
        ext a
        constructor
        · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
          refine ⟨z, ?_⟩
          change ρ.action ((AlgebraicGroup.commutatorMorphism G).toFun z) =
            glPointEquivOf k V e
              (f.onPoints ((AlgebraicGroup.commutatorMorphism G).toFun z))
          exact (hf ((AlgebraicGroup.commutatorMorphism G).toFun z)).symm
        · rintro ⟨z, rfl⟩
          refine ⟨q.toFun z, ⟨z, rfl⟩, ?_⟩
          change glPointEquivOf k V e
              (f.onPoints ((AlgebraicGroup.commutatorMorphism G).toFun z)) =
            ρ.action ((AlgebraicGroup.commutatorMorphism G).toFun z)
          exact hf ((AlgebraicGroup.commutatorMorphism G).toFun z)
      rw [heq]
      exact hactionFinite
    · intro a _ b _ hab
      exact (glPointEquivOf k V e).injective hab
  have hprodConnected : Variety.IsConnected (Variety.prod G G) := by
    have hI := prodSet_irreducible_of_irreducible
      (connectedAlgebraicGroup_irreducible G hG)
      (connectedAlgebraicGroup_irreducible G hG)
    have hprod : Variety.prodSet
        (Set.univ : Set (Variety.Point G))
        (Set.univ : Set (Variety.Point G)) =
        (Set.univ : Set (Variety.Point (Variety.prod G G))) := by
      ext z
      simp [Variety.prodSet]
    rw [hprod] at hI
    exact hI.isConnected
  have hsingleton :=
    connected_finite_morphism_range_subsingleton q hprodConnected hqFinite
  intro x y
  have hqeq : q.toFun ((Variety.prodPointEquiv G G).symm (x, y)) =
      q.toFun ((Variety.prodPointEquiv G G).symm (1, 1)) :=
    hsingleton (Set.mem_range_self _) (Set.mem_range_self _)
  have hactionEq := congrArg (glPointEquivOf k V e) hqeq
  have hleft : glPointEquivOf k V e
      (q.toFun ((Variety.prodPointEquiv G G).symm (x, y))) =
      ρ.action (x * y * x⁻¹ * y⁻¹) := by
    change glPointEquivOf k V e
      (f.onPoints ((AlgebraicGroup.commutatorMorphism G).toFun
        ((Variety.prodPointEquiv G G).symm (x, y)))) = _
    rw [AlgebraicGroup.commutatorMorphism_apply]
    exact hf (x * y * x⁻¹ * y⁻¹)
  have hright : glPointEquivOf k V e
      (q.toFun ((Variety.prodPointEquiv G G).symm (1, 1))) = 1 := by
    change glPointEquivOf k V e
      (f.onPoints ((AlgebraicGroup.commutatorMorphism G).toFun
        ((Variety.prodPointEquiv G G).symm (1, 1)))) = _
    rw [AlgebraicGroup.commutatorMorphism_apply]
    simpa using hf 1
  have hcommOne : ρ.action (x * y * x⁻¹ * y⁻¹) = 1 := by
    rw [hleft, hright] at hactionEq
    exact hactionEq
  apply mul_right_cancel (b := (ρ.action x)⁻¹ * (ρ.action y)⁻¹)
  simpa [mul_assoc] using hcommOne

/-- Every nonzero finite-dimensional rational representation of a connected
solvable algebraic group has a common eigenvector. -/
private lemma RationalRepresentation.exists_common_eigenvector_of_isSolvable_isConnected
    {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G) :
    ∃ (χ : Variety.Point G → k) (v : V), v ≠ 0 ∧
      ∀ g, (ρ.action g : Module.End k V) v = χ g • v := by
  have main : ∀ d : Cardinal, ∀ (G : Variety k) [AlgebraicGroup G],
      Variety.dimension G = d →
      (ρ : RationalRepresentation G V) → IsRationalRepresentation ρ →
      Group.IsSolvable (Variety.Point G) → Variety.IsConnected G →
      ∃ (χ : Variety.Point G → k) (v : V), v ≠ 0 ∧
        ∀ g, (ρ.action g : Module.End k V) v = χ g • v := by
    intro d
    induction d using WellFoundedLT.induction with
    | ind d ih =>
      intro G _ hdim ρ hρ hsolvable hconnected
      by_cases hsub : Subsingleton (Variety.Point G)
      · let : Subsingleton (Variety.Point G) := hsub
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        refine ⟨fun _ => 1, v, hv, ?_⟩
        intro g
        have hg : g = 1 := Subsingleton.elim _ _
        rw [hg]
        simp
      · let : Nontrivial (Variety.Point G) :=
          not_subsingleton_iff_nontrivial.mp hsub
        let D : ClosedSubgroup G :=
          subgroupZariskiClosure G (commutator (Variety.Point G))
        let : D.toSubgroup.Normal := subgroupZariskiClosure_isNormal G
          (commutator (Variety.Point G)) (derivedSeries_normal (Variety.Point G) 1)
        have hDset : _root_.IsConnected (D : Set (Variety.Point G)) := by
          exact subgroupZariskiClosure_commutator_isConnected hconnected
        have hDconnected : Variety.IsConnected D.carrierVariety := by
          let e := Variety.closedSubvarietyPointHomeomorph D.isZariskiClosed
          let : ConnectedSpace {x : Variety.Point G // x ∈ (D : Set (Variety.Point G))} :=
            Subtype.connectedSpace hDset
          let : ConnectedSpace (Variety.Point D.carrierVariety) :=
            e.connectedSpace_iff.mpr inferInstance
          exact connectedSpace_iff_univ.mp inferInstance
        let : Group.IsSolvable (Variety.Point G) := hsolvable
        have hDsolvable : Group.IsSolvable (Variety.Point D.carrierVariety) :=
          Group.isSolvable_of_isSolvable_injective D.inclusion_injective
        let : Group.IsSolvable (Variety.Point D.carrierVariety) := hDsolvable
        have hDproper : D ≠ ClosedSubgroup.top :=
          subgroupZariskiClosure_commutator_ne_top_of_isSolvable hsolvable inferInstance
        have hdimle : Variety.dimension D.carrierVariety ≤ Variety.dimension G :=
          closedSubvariety_dimension_le G D.isZariskiClosed
        have hdimne : Variety.dimension D.carrierVariety ≠ Variety.dimension G := by
          intro heq
          have hcontains := (closedSubgroup_dimension_eq_iff_contains_identityComponent G D).mp heq
          have hid : AlgebraicGroup.identityComponent G = Set.univ :=
            (identityComponent_eq_univ_iff_isConnected G).mpr hconnected
          rw [hid] at hcontains
          apply hDproper
          apply SetLike.coe_injective
          exact Set.Subset.antisymm (fun _ _ => trivial) hcontains
        have hdimlt : Variety.dimension D.carrierVariety < Variety.dimension G :=
          lt_of_le_of_ne hdimle hdimne
        obtain ⟨τD, hpull, hτD⟩ :=
          rationalRepresentation_pullback_exists D.inclusion ρ hρ
        have hDlt : Variety.dimension D.carrierVariety < d := by
          rw [← hdim]
          exact hdimlt
        obtain ⟨χD, v, hvne, hvD⟩ :=
          ih (Variety.dimension D.carrierVariety) hDlt
            D.carrierVariety rfl τD hτD hDsolvable hDconnected
        let N : Subgroup (Variety.Point G) := D.toSubgroup
        let χN : N → k := fun n => χD (D.pointEquiv.symm n)
        have hvN : ∀ n : N,
            (ρ.action n : Module.End k V) v = χN n • v := by
          intro n
          have hvDn := hvD (D.pointEquiv.symm n)
          rw [hpull] at hvDn
          change (ρ.action n : Module.End k V) v = χN n • v
          exact hvDn
        let σ : Representation k (Variety.Point G) V :=
          (Units.coeHom (Module.End k V)).comp ρ.action
        obtain ⟨W, hWne, hWinvariant, hWcomm⟩ :=
          Representation.exists_invariant_orbitSpan_of_normal_commonEigenvector
            σ N χN v hvne hvN
        have hWinvariant' : IsInvariantSubmodule ρ W := by
          intro g w hw
          have hmem : (ρ.action g : Module.End k V) w ∈
              Submodule.map (ρ.action g : Module.End k V) W := ⟨w, hw, rfl⟩
          have heq := hWinvariant g
          change Submodule.map (ρ.action g : Module.End k V) W = W at heq
          rw [← heq]
          exact hmem
        let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
        obtain ⟨τW, hτWrestrict, hτWrational⟩ :=
          rationalRepresentation_restriction_exists ρ hρ W hWinvariant'
        have hcommτW : Pairwise fun a b : N =>
            Commute (τW.action a : Module.End k W) (τW.action b : Module.End k W) := by
          intro a b _
          apply LinearMap.ext
          intro w
          apply Subtype.ext
          change (((τW.action a : Module.End k W)
            ((τW.action b : Module.End k W) w) : W) : V) =
            (((τW.action b : Module.End k W)
              ((τW.action a : Module.End k W) w) : W) : V)
          have hab := hWcomm a b w w.property
          change (ρ.action a : Module.End k V)
              ((ρ.action b : Module.End k V) (w : V)) =
            (ρ.action b : Module.End k V)
              ((ρ.action a : Module.End k V) (w : V)) at hab
          calc
            (((τW.action a : Module.End k W)
                ((τW.action b : Module.End k W) w) : W) : V) =
                (ρ.action a : Module.End k V)
                  (((τW.action b : Module.End k W) w : W) : V) :=
              hτWrestrict a ((τW.action b : Module.End k W) w)
            _ = (ρ.action a : Module.End k V)
                  ((ρ.action b : Module.End k V) (w : V)) :=
              congrArg (ρ.action a : Module.End k V) (hτWrestrict b w)
            _ = (ρ.action b : Module.End k V)
                  ((ρ.action a : Module.End k V) (w : V)) := hab
            _ = (ρ.action b : Module.End k V)
                  (((τW.action a : Module.End k W) w : W) : V) :=
              (congrArg (ρ.action b : Module.End k V) (hτWrestrict a w)).symm
            _ = (((τW.action b : Module.End k W)
                ((τW.action a : Module.End k W) w) : W) : V) :=
              (hτWrestrict b ((τW.action a : Module.End k W) w)).symm
        obtain ⟨χW, U, hUne, hUinvariant, hUeigen⟩ :=
          τW.exists_invariant_commonEigenspace_of_normal_commuting_action
            hτWrational N hcommτW hconnected
        have hUinvariant' : IsInvariantSubmodule τW U := by
          intro g w hw
          have hmem : (τW.action g : Module.End k W) w ∈
              Submodule.map (τW.action g : Module.End k W) U := ⟨w, hw, rfl⟩
          rw [hUinvariant g] at hmem
          exact hmem
        let : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
        obtain ⟨τU, hτUrestrict, hτUrational⟩ :=
          rationalRepresentation_restriction_exists τW hτWrational U hUinvariant'
        have hscalar : ∀ x y : Variety.Point G, ∃ c : k,
            (τU.action (x * y * x⁻¹ * y⁻¹) : Module.End k U) =
              c • LinearMap.id := by
          intro x y
          let n : N := ⟨x * y * x⁻¹ * y⁻¹, by
            change x * y * x⁻¹ * y⁻¹ ∈ closure
              (commutator (Variety.Point G) : Set (Variety.Point G))
            apply subset_closure
            exact Subgroup.commutator_mem_commutator
              (H₁ := ⊤) (H₂ := ⊤) trivial trivial⟩
          refine ⟨χW n, ?_⟩
          apply LinearMap.ext
          intro u
          apply Subtype.ext
          change (((τU.action (x * y * x⁻¹ * y⁻¹) : Module.End k U) u : U) : W) =
            (((χW n • LinearMap.id : Module.End k U) u : U) : W)
          calc
            (((τU.action (x * y * x⁻¹ * y⁻¹) : Module.End k U) u : U) : W) =
                (τW.action n : Module.End k W) (u : W) :=
              hτUrestrict (x * y * x⁻¹ * y⁻¹) u
            _ = χW n • (u : W) := hUeigen n u u.property
            _ = (((χW n • LinearMap.id : Module.End k U) u : U) : W) := by
              simp
        have hcommU := τU.commutes_of_connected_of_commutator_scalars
          hτUrational hconnected hscalar
        let fU : Variety.Point G → Module.End k U :=
          fun g => (τU.action g : Module.End k U)
        have hpairU : Pairwise fun x y => Commute (fU x) (fU y) := by
          intro x y _
          change (τU.action x : Module.End k U) *
              (τU.action y : Module.End k U) =
            (τU.action y : Module.End k U) *
              (τU.action x : Module.End k U)
          have hxy := congrArg
            (fun z : LinearMap.GeneralLinearGroup k U => (z : Module.End k U))
            (hcommU x y)
          exact hxy
        obtain ⟨χU, hχU⟩ :=
          exists_nontrivial_common_eigenspace_of_commuting_family fU hpairU
        let E : Submodule k U :=
          ⨅ g : Variety.Point G, Module.End.eigenspace (fU g) (χU g)
        let : Nontrivial E := by simpa [E] using hχU
        obtain ⟨z, hz⟩ := exists_ne (0 : E)
        let u : U := z
        let w : W := u
        let v : V := w
        have hvne : v ≠ 0 := by
          intro hv
          apply hz
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          exact hv
        refine ⟨χU, v, hvne, ?_⟩
        intro g
        have hzall := z.property
        change (z : U) ∈ ⨅ h : Variety.Point G,
          Module.End.eigenspace (fU h) (χU h) at hzall
        rw [Submodule.mem_iInf] at hzall
        have heigen := Module.End.mem_eigenspace_iff.mp (hzall g)
        change (τU.action g : Module.End k U) u = χU g • u at heigen
        calc
          (ρ.action g : Module.End k V) v =
              (((τW.action g : Module.End k W) w : W) : V) :=
            (hτWrestrict g w).symm
          _ = ((((τU.action g : Module.End k U) u : U) : W) : V) := by
            exact congrArg (fun q : W => (q : V)) (hτUrestrict g u).symm
          _ = χU g • v := by rw [heigen]; rfl
  exact main (Variety.dimension G) G rfl ρ hρ hsolvable hconnected

public theorem RationalRepresentation.exists_common_eigenvector_of_isSolvable_isConnected_public
    {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G) :
    ∃ (χ : Variety.Point G → k) (v : V), v ≠ 0 ∧
      ∀ g, (ρ.action g : Module.End k V) v = χ g • v :=
  ρ.exists_common_eigenvector_of_isSolvable_isConnected hρ hsolvable hconnected

/-- A connected solvable algebraic group preserves a nonzero one-dimensional
subspace in every nonzero finite-dimensional rational representation. -/
private lemma RationalRepresentation.exists_invariant_finrank_one_of_isSolvable_isConnected
    {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G) :
    ∃ W : Submodule k V, W ≠ ⊥ ∧ Module.finrank k W = 1 ∧
      ∀ g, Submodule.map (ρ.action g : Module.End k V) W = W := by
  obtain ⟨χ, v, hvne, hv⟩ :=
    ρ.exists_common_eigenvector_of_isSolvable_isConnected hρ hsolvable hconnected
  let W : Submodule k V := k ∙ v
  have hforward (g : Variety.Point G) :
      Submodule.map (ρ.action g : Module.End k V) W ≤ W := by
    rw [Submodule.map_le_iff_le_comap]
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    change (ρ.action g : Module.End k V) v ∈ W
    rw [hv g]
    exact W.smul_mem (χ g) (Submodule.mem_span_singleton_self v)
  have hinvariant (g : Variety.Point G) :
      Submodule.map (ρ.action g : Module.End k V) W = W := by
    apply le_antisymm (hforward g)
    intro w hw
    refine ⟨(ρ.action g⁻¹ : Module.End k V) w, ?_, ?_⟩
    · have hmem : (ρ.action g⁻¹ : Module.End k V) w ∈
          Submodule.map (ρ.action g⁻¹ : Module.End k V) W := ⟨w, hw, rfl⟩
      exact hforward g⁻¹ hmem
    · have hinv : ρ.action g⁻¹ = (ρ.action g)⁻¹ := map_inv ρ.action g
      rw [hinv]
      exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k V
        (ρ.action g)).apply_symm_apply w
  refine ⟨W, ?_, finrank_span_singleton hvne, hinvariant⟩
  simpa [W, Submodule.span_singleton_eq_bot] using hvne

/-- Every proper invariant submodule in a rational representation of a
connected solvable algebraic group has an invariant extension of finrank one
larger. -/
private lemma RationalRepresentation.exists_invariant_extension_finrank_succ_of_isSolvable_isConnected
    {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (W : Submodule k V) (hWinvariant : IsInvariantSubmodule ρ W)
    (hWlt : Module.finrank k W < Module.finrank k V) :
    ∃ S : Submodule k V, W ≤ S ∧ IsInvariantSubmodule ρ S ∧
      Module.finrank k S = Module.finrank k W + 1 := by
  have hquotfinrank : 0 < Module.finrank k (V ⧸ W) := by
    rw [Submodule.finrank_quotient]
    omega
  let : Nontrivial (V ⧸ W) := Module.finrank_pos_iff.mp hquotfinrank
  obtain ⟨τ, hτquotient, hτrational⟩ :=
    rationalRepresentation_quotient_exists ρ hρ W hWinvariant
  obtain ⟨U, _hUne, hUdim, hUmap⟩ :=
    τ.exists_invariant_finrank_one_of_isSolvable_isConnected
      hτrational hsolvable hconnected
  let S : Submodule k V := U.comap W.mkQ
  have hWS : W ≤ S := Submodule.le_comap_mkQ W U
  have hSinvariant : IsInvariantSubmodule ρ S := by
    intro g x hx
    change Submodule.Quotient.mk ((ρ.action g : Module.End k V) x) ∈ U
    rw [← hτquotient g x]
    have hmem : (τ.action g : Module.End k (V ⧸ W)) (W.mkQ x) ∈
        Submodule.map (τ.action g : Module.End k (V ⧸ W)) U :=
      ⟨W.mkQ x, hx, rfl⟩
    rw [hUmap g] at hmem
    exact hmem
  have hrange : LinearMap.range (W.mkQ.domRestrict S) = U := by
    rw [LinearMap.range_domRestrict]
    exact Submodule.map_comap_eq_self (by simp)
  have hker : LinearMap.ker (W.mkQ.domRestrict S) =
      Submodule.comap S.subtype W := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ]
  have hkerfinrank : Module.finrank k (LinearMap.ker (W.mkQ.domRestrict S)) =
      Module.finrank k W := by
    rw [hker]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hWS)
  have hranknull := LinearMap.finrank_range_add_finrank_ker (W.mkQ.domRestrict S)
  rw [hrange, hUdim, hkerfinrank] at hranknull
  refine ⟨S, hWS, hSinvariant, ?_⟩
  omega

/-- A finite-dimensional rational representation of a connected solvable
algebraic group admits a single increasing invariant chain with every possible
finrank. -/
private lemma RationalRepresentation.exists_full_invariant_submodule_chain_of_isSolvable_isConnected
    {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G) :
    ∃ F : ℕ → Submodule k V, Monotone F ∧
      ∀ i, IsInvariantSubmodule ρ (F i) ∧
        Module.finrank k (F i) = min i (Module.finrank k V) := by
  let Inv := {W : Submodule k V // IsInvariantSubmodule ρ W}
  let bottomInv : Inv := ⟨⊥, by
    intro g x hx
    change x = 0 at hx
    subst x
    simp⟩
  let next : Inv → Inv := fun W =>
    if hlt : Module.finrank k W.1 < Module.finrank k V then
      ⟨Classical.choose
          (ρ.exists_invariant_extension_finrank_succ_of_isSolvable_isConnected
            hρ hsolvable hconnected W.1 W.2 hlt),
        (Classical.choose_spec
          (ρ.exists_invariant_extension_finrank_succ_of_isSolvable_isConnected
            hρ hsolvable hconnected W.1 W.2 hlt)).2.1⟩
    else W
  have next_le (W : Inv) : W.1 ≤ (next W).1 := by
    simp only [next]
    split
    next hlt =>
      exact (Classical.choose_spec
        (ρ.exists_invariant_extension_finrank_succ_of_isSolvable_isConnected
          hρ hsolvable hconnected W.1 W.2 hlt)).1
    next => exact le_rfl
  have next_finrank (W : Inv) :
      Module.finrank k (next W).1 =
        if Module.finrank k W.1 < Module.finrank k V then
          Module.finrank k W.1 + 1
        else Module.finrank k W.1 := by
    by_cases hlt : Module.finrank k W.1 < Module.finrank k V
    · rw [if_pos hlt]
      rw [show next W =
        ⟨Classical.choose
            (ρ.exists_invariant_extension_finrank_succ_of_isSolvable_isConnected
              hρ hsolvable hconnected W.1 W.2 hlt),
          (Classical.choose_spec
            (ρ.exists_invariant_extension_finrank_succ_of_isSolvable_isConnected
              hρ hsolvable hconnected W.1 W.2 hlt)).2.1⟩ by
        simp [next, hlt]]
      exact (Classical.choose_spec
        (ρ.exists_invariant_extension_finrank_succ_of_isSolvable_isConnected
          hρ hsolvable hconnected W.1 W.2 hlt)).2.2
    · rw [if_neg hlt]
      rw [show next W = W by simp [next, hlt]]
  let chain : ℕ → Inv := fun i => next^[i] bottomInv
  have chain_finrank (i : ℕ) :
      Module.finrank k (chain i).1 = min i (Module.finrank k V) := by
    induction i with
    | zero =>
        change Module.finrank k (⊥ : Submodule k V) = 0
        simp
    | succ i ih =>
        rw [show chain i.succ = next (chain i) by
          simp [chain, Function.iterate_succ_apply']]
        rw [next_finrank, ih]
        split
        next hlt =>
          have hi : i < Module.finrank k V := by omega
          rw [Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left (by omega)]
        next hnot =>
          have hi : Module.finrank k V ≤ i := by omega
          rw [Nat.min_eq_right hi,
            Nat.min_eq_right (Nat.le_trans hi (Nat.le_succ i))]
  let F : ℕ → Submodule k V := fun i => (chain i).1
  refine ⟨F, ?_, ?_⟩
  · apply monotone_nat_of_le_succ
    intro i
    change (chain i).1 ≤ (chain (i + 1)).1
    rw [show chain (i + 1) = next (chain i) by
      simp [chain, Function.iterate_succ_apply']]
    exact next_le (chain i)
  · intro i
    exact ⟨(chain i).2, chain_finrank i⟩

/-- Every finite-dimensional rational representation of a connected solvable
algebraic group has a basis in which every group element acts by an
upper-triangular matrix. -/
public theorem RationalRepresentation.exists_basis_tTriangular_of_isSolvable_isConnected
    {G : Variety k} [AlgebraicGroup G]
    {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V,
      ∀ g : Variety.Point G,
        tTriangular (Module.finrank k V)
          (LinearMap.toMatrix b b (ρ.action g : Module.End k V)) := by
  obtain ⟨F, hFmono, hFinvariant⟩ :=
    ρ.exists_full_invariant_submodule_chain_of_isSolvable_isConnected
      hρ hsolvable hconnected
  obtain ⟨b, hb⟩ := exists_basis_adapted_to_full_submodule_chain
    F hFmono (fun i => (hFinvariant i).2)
  refine ⟨b, ?_⟩
  intro g i j hji
  rw [LinearMap.toMatrix_apply]
  have hjle : (j : ℕ) + 1 ≤ Module.finrank k V := j.isLt
  have hjmem : b j ∈ F ((j : ℕ) + 1) := by
    rw [hb ((j : ℕ) + 1) hjle]
    apply Submodule.subset_span
    refine ⟨⟨j, by omega⟩, ?_⟩
    congr 1
  have hactmem : (ρ.action g : Module.End k V) (b j) ∈ F ((j : ℕ) + 1) :=
    (hFinvariant ((j : ℕ) + 1)).1 g (b j) hjmem
  rw [hb ((j : ℕ) + 1) hjle] at hactmem
  have hcoords := (basisSpanCoord V (Module.finrank k V) b
    ((j : ℕ) + 1) hjle
    (b.equivFun ((ρ.action g : Module.End k V) (b j)))).mp (by
      simpa using hactmem)
  exact hcoords i (by omega)

end Theory.AlgebraicGroup
