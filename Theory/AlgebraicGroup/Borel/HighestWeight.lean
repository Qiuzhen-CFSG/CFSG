module

public import Theory.AlgebraicGroup.Borel.OppositeBigCell
public import Theory.AlgebraicGroup.Representations.Algebraic.HighestWeight

/-!
# Highest weights from an opposite Borel big cell

This module proves the uniqueness and classification parts of the highest-weight
argument used in GLS3, Theorem 1.14.6(c).  The geometric input is an explicit
`OppositeBorelBigCell`: compatible positive and opposite Borels containing the
same torus, their torus-times-root decompositions, and density of their product.

For uniqueness, a high-weight vector is paired with an opposite high-weight
functional in the dual representation.  If that pairing vanished, its matrix
coefficient would vanish on the reverse big cell and hence everywhere; the
irreducibility criterion for invariant submodules then gives a contradiction.
Two high-weight vectors of the same character therefore have a high-weight
linear combination annihilated by the functional only when that combination is
zero.

For classification, normalize opposite high-weight functionals on the selected
vectors.  Their matrix coefficients agree on the reverse big cell by the two
Borel decompositions, hence agree globally by density.  Each representation
embeds into polynomial functions through this coefficient, and irreducibility
identifies its image with the right-translation span of the common coefficient.
The resulting linear equivalence intertwines the group actions.

The source theorem obtains the big-cell package from its semisimple universal
group and realized-root hypotheses.  That geometric construction is kept as a
separate prerequisite rather than assumed inside the representation argument.
-/

universe u v w

open scoped Pointwise

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma polynomialFunction_eq_zero_of_dense
    {K : Variety k} {S : Set (Variety.Point K)} (hS : Dense S)
    (f : K.PolynomialFunction) (hf : ∀ x ∈ S, f x = 0) : f = 0 := by
  apply Variety.PolynomialFunction.ext
  intro x
  have hclosed : IsClosed {y : Variety.Point K | f y = 0} := by
    rw [Variety.isClosed_iff_isZariskiClosed]
    obtain ⟨p, hp⟩ := f.representedBy
    refine ⟨{p}, ?_⟩
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
    rw [← hp y]
  have hclosure : closure S ⊆ {y : Variety.Point K | f y = 0} :=
    closure_minimal hf hclosed
  exact hclosure (hS x)

private lemma matrixCoefficient_separates_of_irreducible
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V]
    (rho : RationalRepresentation K V) (hirr : IsIrreducibleRepresentation rho)
    (l : Module.Dual k V) (hl : l ≠ 0) (x : V)
    (hx : ∀ g, l ((rho.action g).1 x) = 0) : x = 0 := by
  let A : Submodule k V :=
    ⨅ g : Variety.Point K, LinearMap.ker (l.comp (rho.action g).1)
  have hAInvariant : IsInvariantSubmodule rho A := by
    intro h y hy
    rw [Submodule.mem_iInf] at hy ⊢
    intro g
    have hgy := hy (g * h)
    change l ((rho.action g).1 ((rho.action h).1 y)) = 0
    simpa [map_mul] using hgy
  have hxA : x ∈ A := by
    rw [Submodule.mem_iInf]
    exact hx
  rcases hirr.2 A hAInvariant with hbot | htop
  · rw [hbot] at hxA
    simpa using hxA
  · exfalso
    apply hl
    ext y
    have hyA : y ∈ A := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_iInf] at hyA
    have hyOne := hyA (1 : Variety.Point K)
    simpa using hyOne

omit [IsAlgClosed k] in
private lemma reverse_oppositeBorel_product_dense
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T} {P : Set D.Root}
    (H : OppositeBorelBigCell T D P) :
    Dense ((H.data.Bopp.toSubgroup : Set (Variety.Point K)) *
      (H.data.B.toSubgroup : Set (Variety.Point K))) := by
  let invHomeo : Variety.Point K ≃ₜ Variety.Point K :=
    { toFun := fun g ↦ g⁻¹
      invFun := fun g ↦ g⁻¹
      left_inv := inv_inv
      right_inv := inv_inv
      continuous_toFun := (AlgebraicGroup.invMorphism K).continuous
      continuous_invFun := (AlgebraicGroup.invMorphism K).continuous }
  have hpreimage := H.product_dense.preimage invHomeo.isOpenMap
  apply hpreimage.mono
  intro x hx
  rcases Set.mem_mul.mp hx with ⟨b, hb, bopp, hbopp, hmul⟩
  change b * bopp = x⁻¹ at hmul
  have hxmul : x = bopp⁻¹ * b⁻¹ := by
    rw [← inv_inv x, ← hmul, mul_inv_rev]
  rw [hxmul]
  exact Set.mul_mem_mul (H.data.Bopp.inv_mem hbopp) (H.data.B.inv_mem hb)

private lemma opposite_pairing_ne_zero
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T} {P : Set D.Root}
    (H : OppositeBorelBigCell T D P)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V) (hirr : IsIrreducibleRepresentation rho)
    (tau : RationalRepresentation K (Module.Dual k V))
    (htau : IsDualRepresentation rho tau)
    (v : V) (chi : TorusWeight T)
    (hv : HasHighWeight rho H.data.B T v chi)
    (l : Module.Dual k V) (nu : TorusWeight T)
    (hl : HasHighWeight tau H.data.Bopp T l nu) : l v ≠ 0 := by
  intro hlv
  obtain ⟨e, f, hf⟩ := hirr.1
  let q : K.PolynomialFunction :=
    rationalRepresentationLinearMatrixCoefficient rho e f l v
  have hq_apply (g : Variety.Point K) : q g = l ((rho.action g).1 v) := by
    exact rationalRepresentationLinearMatrixCoefficient_apply rho e f hf l v g
  have hq_zero_on_reverse : ∀ g ∈
      ((H.data.Bopp.toSubgroup : Set (Variety.Point K)) *
        (H.data.B.toSubgroup : Set (Variety.Point K))), q g = 0 := by
    intro g hg
    rcases Set.mem_mul.mp hg with ⟨bopp, hbopp, b, hb, hmul⟩
    obtain ⟨c, hc⟩ := hv.1.2 b hb
    obtain ⟨d, hd⟩ := hl.1.2 bopp⁻¹ (H.data.Bopp.inv_mem hbopp)
    rw [hq_apply, ← hmul, map_mul]
    change l ((rho.action bopp).1 ((rho.action b).1 v)) = 0
    rw [hc, map_smul, map_smul]
    have hdual := htau bopp⁻¹ l v
    rw [hd] at hdual
    have heval : l ((rho.action bopp).1 v) = d • l v := by
      simpa using hdual.symm
    rw [heval, hlv, smul_zero, smul_zero]
  have hqzero : q = 0 :=
    polynomialFunction_eq_zero_of_dense (reverse_oppositeBorel_product_dense H)
      q hq_zero_on_reverse
  apply hv.1.1
  apply matrixCoefficient_separates_of_irreducible rho hirr l hl.1.1 v
  intro g
  have := congrArg (fun z : K.PolynomialFunction ↦ z g) hqzero
  simpa [hq_apply] using this

public theorem highWeight_exists_of_borel
    {K : Variety k} [AlgebraicGroup K] (B T : ClosedSubgroup K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Nontrivial V] (rho : RationalRepresentation K V)
    (hrho : IsRationalRepresentation rho) (hB : IsBorelSubgroup B)
    (_hT : IsMaximalTorus T) (hTB : T ≤ B) :
    ∃ v chi, HasHighWeight rho B T v chi := by
  obtain ⟨tau, htau, htaur⟩ :=
    rationalRepresentation_pullback_exists B.inclusion rho hrho
  have hBconnected : Variety.IsConnected B.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed
    let : ConnectedSpace {x : Variety.Point K // x ∈ (B : Set (Variety.Point K))} :=
      Subtype.connectedSpace hB.connected
    let : ConnectedSpace (Variety.Point B.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  obtain ⟨chiB, v, hv, heigen⟩ :=
    tau.exists_common_eigenvector_of_isSolvable_isConnected_public htaur
      hB.solvable hBconnected
  have hvgen : GeneratesInvariantLine rho B v := by
    refine ⟨hv, ?_⟩
    intro b hb
    let bB : Variety.Point B.carrierVariety := B.pointEquiv.symm ⟨b, hb⟩
    have hc := heigen bB
    have hbB : B.inclusion.onPoints bB = b := by
      change (B.pointEquiv bB).val = b
      simp [bB]
    refine ⟨chiB bB, ?_⟩
    rw [htau, hbB] at hc
    exact hc
  have hvgenT : GeneratesInvariantLine rho T v := by
    refine ⟨hvgen.1, ?_⟩
    intro t ht
    exact hvgen.2 (T.inclusion.onPoints (T.pointEquiv.symm ⟨t, ht⟩)) (hTB ht)
  obtain ⟨chi, hchi, _⟩ :=
    invariantLine_torusWeight_existsUnique_public rho hrho T v hvgenT
  exact ⟨v, chi, hvgen, hchi⟩

omit [IsAlgClosed k] in
private lemma highWeight_eq_of_dual_pairing_ne_zero
    {K : Variety k} [AlgebraicGroup K]
    {T B Bopp : ClosedSubgroup K}
    {V : Type v} [AddCommGroup V] [Module k V]
    (rho : RationalRepresentation K V)
    (tau : RationalRepresentation K (Module.Dual k V))
    (htau : IsDualRepresentation rho tau)
    (v w : V) (chi mu : TorusWeight T)
    (hv : HasHighWeight rho B T v chi)
    (hw : HasHighWeight rho B T w mu)
    (l : Module.Dual k V) (nu : TorusWeight T)
    (hl : HasHighWeight tau Bopp T l nu)
    (hlv : l v ≠ 0) (hlw : l w ≠ 0) : chi = mu := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  have hvdual := htau (T.includePoint t)⁻¹ l v
  have hwdual := htau (T.includePoint t)⁻¹ l w
  have hlt := hl.2.2 t⁻¹
  have hvt := hv.2.2 t
  have hwt := hw.2.2 t
  have hinv : (T.includePoint t)⁻¹ = T.includePoint t⁻¹ := by rfl
  have hinvinv : (T.includePoint t⁻¹)⁻¹ = T.includePoint t := by
    rw [← hinv, inv_inv]
  rw [hinv, hlt] at hvdual hwdual
  rw [hinvinv, hvt] at hvdual
  rw [hinvinv, hwt] at hwdual
  have hvchar : nu.pointCharacter t⁻¹ = chi.pointCharacter t := by
    apply mul_right_cancel₀ hlv
    simpa using hvdual
  have hwchar : nu.pointCharacter t⁻¹ = mu.pointCharacter t := by
    apply mul_right_cancel₀ hlw
    simpa using hwdual
  exact hvchar.symm.trans hwchar

omit [IsAlgClosed k] in
private lemma dual_highWeight_inverse_weight
    {K : Variety k} [AlgebraicGroup K]
    {T B Bopp : ClosedSubgroup K}
    {V : Type v} [AddCommGroup V] [Module k V]
    (rho : RationalRepresentation K V)
    (tau : RationalRepresentation K (Module.Dual k V))
    (htau : IsDualRepresentation rho tau)
    (v : V) (chi : TorusWeight T)
    (hv : HasHighWeight rho B T v chi)
    (l : Module.Dual k V) (nu : TorusWeight T)
    (hl : HasHighWeight tau Bopp T l nu)
    (hlv : l v ≠ 0) :
    ∀ t, nu.pointCharacter t⁻¹ = chi.pointCharacter t := by
  intro t
  have hvdual := htau (T.includePoint t)⁻¹ l v
  have hlt := hl.2.2 t⁻¹
  have hvt := hv.2.2 t
  have hinv : (T.includePoint t)⁻¹ = T.includePoint t⁻¹ := by rfl
  have hinvinv : (T.includePoint t⁻¹)⁻¹ = T.includePoint t := by
    rw [← hinv, inv_inv]
  rw [hinv, hlt, hinvinv, hvt] at hvdual
  apply mul_right_cancel₀ hlv
  simpa using hvdual

private lemma highWeight_action_torus_mul_rootGenerated
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T} {Q : Set D.Root}
    {B : ClosedSubgroup K} (hB : IsBorelOfPositiveSystem D Q B)
    {V : Type v} [AddCommGroup V] [Module k V]
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (v : V) (chi : TorusWeight T) (hv : HasHighWeight rho B T v chi)
    (t u : Variety.Point K) (ht : t ∈ T) (hu : u ∈ RootSubgroupGenerated D Q) :
    (rho.action (t * u)).1 v =
      chi.pointCharacter (T.pointEquiv.symm ⟨t, ht⟩) • v := by
  have hUle : hB.unipotent ≤ B := hB.radical.1
  have hUunipotent : IsUnipotentAlgebraicGroup hB.unipotent.carrierVariety :=
    hB.radical.2.1
  have hvfixed := invariantLine_fixed_of_unipotent_subgroup rho hrho
    B hB.unipotent v hv.1 hUle hUunipotent
  have huU : u ∈ hB.unipotent := by
    change u ∈ hB.unipotent.toSubgroup
    rw [hB.root_generated]
    exact hu
  let tT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
  have htT : T.includePoint tT = t := by
    change (T.pointEquiv tT).val = t
    simp [tT]
  rw [map_mul]
  change (rho.action t).1 ((rho.action u).1 v) = _
  rw [hvfixed u huU]
  change (rho.action t).1 v = chi.pointCharacter tT • v
  rw [← htT, hv.2.2 tT]

private lemma normalized_highWeight_coefficients_eq
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T} {P : Set D.Root}
    (H : OppositeBorelBigCell T D P)
    {V W : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W]
    (rho : RationalRepresentation K V) (sigma : RationalRepresentation K W)
    (hrho : IsRationalRepresentation rho) (hsigma : IsRationalRepresentation sigma)
    (v : V) (w : W) (chi : TorusWeight T)
    (hv : HasHighWeight rho H.data.B T v chi)
    (hw : HasHighWeight sigma H.data.B T w chi)
    (tau : RationalRepresentation K (Module.Dual k V))
    (upsilon : RationalRepresentation K (Module.Dual k W))
    (htau : IsDualRepresentation rho tau)
    (hupsilon : IsDualRepresentation sigma upsilon)
    (htauRational : IsRationalRepresentation tau)
    (hupsilonRational : IsRationalRepresentation upsilon)
    (l : Module.Dual k V) (m : Module.Dual k W)
    (nu omega : TorusWeight T)
    (hl : HasHighWeight tau H.data.Bopp T l nu)
    (hm : HasHighWeight upsilon H.data.Bopp T m omega)
    (hlone : l v = 1) (hmone : m w = 1)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism K (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = rho.action g)
    (e' : Module.Basis (Fin (Module.finrank k W)) k W)
    (f' : AlgebraicGroup.Morphism K (glVarietyOf k W))
    (hf' : ∀ g, glPointEquivOf k W e' (f'.onPoints g) = sigma.action g) :
    rationalRepresentationLinearMatrixCoefficient rho e f l v =
      rationalRepresentationLinearMatrixCoefficient sigma e' f' m w := by
  have hlv : l v ≠ 0 := by rw [hlone]; exact one_ne_zero
  have hmw : m w ≠ 0 := by rw [hmone]; exact one_ne_zero
  have hnu := dual_highWeight_inverse_weight rho tau htau v chi hv l nu hl hlv
  have homega := dual_highWeight_inverse_weight sigma upsilon hupsilon
    w chi hw m omega hm hmw
  apply sub_eq_zero.mp
  apply polynomialFunction_eq_zero_of_dense (reverse_oppositeBorel_product_dense H)
  intro g hg
  rcases Set.mem_mul.mp hg with ⟨bopp, hbopp, b, hb, hmul⟩
  obtain ⟨t, u, ht, hu, htu⟩ := (H.positive_decomposition b).mp hb
  obtain ⟨s, z, hs, hz, hsz⟩ :=
    (H.negative_decomposition bopp⁻¹).mp (H.data.Bopp.inv_mem hbopp)
  let tT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
  let sT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨s, hs⟩
  have hrhob := highWeight_action_torus_mul_rootGenerated
    H.data.positive_witness rho hrho v chi hv t u ht hu
  have hsigmab := highWeight_action_torus_mul_rootGenerated
    H.data.positive_witness sigma hsigma w chi hw t u ht hu
  have htaubopp := highWeight_action_torus_mul_rootGenerated
    H.data.opposite_witness tau htauRational l nu hl s z hs hz
  have hupsilonbopp := highWeight_action_torus_mul_rootGenerated
    H.data.opposite_witness upsilon hupsilonRational m omega hm s z hs hz
  rw [← htu] at hrhob hsigmab
  rw [← hsz] at htaubopp hupsilonbopp
  have hnueq : nu.pointCharacter sT = chi.pointCharacter sT⁻¹ := by
    have := hnu sT⁻¹
    simpa using this
  have homegaeq : omega.pointCharacter sT = chi.pointCharacter sT⁻¹ := by
    have := homega sT⁻¹
    simpa using this
  have hrhodual := htau bopp⁻¹ l v
  have hsigmadual := hupsilon bopp⁻¹ m w
  rw [htaubopp] at hrhodual
  rw [hupsilonbopp] at hsigmadual
  change rationalRepresentationLinearMatrixCoefficient rho e f l v g -
    rationalRepresentationLinearMatrixCoefficient sigma e' f' m w g = 0
  rw [rationalRepresentationLinearMatrixCoefficient_apply rho e f hf]
  rw [rationalRepresentationLinearMatrixCoefficient_apply sigma e' f' hf']
  rw [← hmul, map_mul, map_mul]
  change l ((rho.action bopp).1 ((rho.action b).1 v)) -
    m ((sigma.action bopp).1 ((sigma.action b).1 w)) = 0
  rw [hrhob, hsigmab, map_smul, map_smul, map_smul, map_smul]
  have hrhobopp : l ((rho.action bopp).1 v) = nu.pointCharacter sT • l v := by
    simpa using hrhodual.symm
  have hsigmabopp : m ((sigma.action bopp).1 w) =
      omega.pointCharacter sT • m w := by
    simpa using hsigmadual.symm
  rw [hrhobopp, hsigmabopp, hnueq, homegaeq, hlone, hmone]
  simp

private lemma highWeight_linearCombination
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T} {P : Set D.Root}
    (H : OppositeBorelBigCell T D P)
    {V : Type v} [AddCommGroup V] [Module k V]
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (v w : V) (chi : TorusWeight T)
    (hv : HasHighWeight rho H.data.B T v chi)
    (hw : HasHighWeight rho H.data.B T w chi)
    (a b : k) (hx : a • v + b • w ≠ 0) :
    HasHighWeight rho H.data.B T (a • v + b • w) chi := by
  have hUle : H.data.positive_witness.unipotent ≤ H.data.B :=
    H.data.positive_witness.radical.1
  have hUunipotent : IsUnipotentAlgebraicGroup
      H.data.positive_witness.unipotent.carrierVariety :=
    H.data.positive_witness.radical.2.1
  have hvfixed := invariantLine_fixed_of_unipotent_subgroup rho hrho
    H.data.B H.data.positive_witness.unipotent v hv.1 hUle hUunipotent
  have hwfixed := invariantLine_fixed_of_unipotent_subgroup rho hrho
    H.data.B H.data.positive_witness.unipotent w hw.1 hUle hUunipotent
  constructor
  · refine ⟨hx, ?_⟩
    intro g hg
    obtain ⟨t, u, ht, hu, htu⟩ := (H.positive_decomposition g).mp hg
    have huU : u ∈ H.data.positive_witness.unipotent := by
      change u ∈ H.data.positive_witness.unipotent.toSubgroup
      rw [H.data.positive_witness.root_generated]
      exact hu
    let tT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
    have htT : T.includePoint tT = t := by
      change (T.pointEquiv tT).val = t
      simp [tT]
    refine ⟨chi.pointCharacter tT, ?_⟩
    rw [htu, map_mul]
    change (rho.action t).1 ((rho.action u).1 (a • v + b • w)) = _
    rw [map_add, map_smul, map_smul, hvfixed u huU,
      hwfixed u huU, ← htT, map_add, map_smul, map_smul,
      hv.2.2 tT, hw.2.2 tT]
    simp [smul_add, smul_smul, mul_comm]
  · refine ⟨hx, ?_⟩
    intro t
    rw [map_add, map_smul, map_smul, hv.2.2 t, hw.2.2 t]
    simp [smul_add, smul_smul, mul_comm]

public theorem irreducible_highWeight_unique_line_of_oppositeBorelBigCell
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T} {P : Set D.Root}
    (H : OppositeBorelBigCell T D P) (hT : IsMaximalTorus T)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V) (hirr : IsIrreducibleRepresentation rho)
    (v w : V) (chi mu : TorusWeight T)
    (hv : HasHighWeight rho H.data.B T v chi)
    (hw : HasHighWeight rho H.data.B T w mu) :
    ∃ c : k, c ≠ 0 ∧ w = c • v := by
  letI : Nontrivial V := ⟨⟨v, 0, hv.1.1⟩⟩
  obtain ⟨tau, htau, htaur⟩ := rationalRepresentation_dual_exists rho hirr.1
  obtain ⟨l, nu, hl⟩ := highWeight_exists_of_borel
    H.data.Bopp T tau htaur H.data.Bopp_isBorel hT H.torus_le_negative
  have hlv : l v ≠ 0 :=
    opposite_pairing_ne_zero H rho hirr tau htau v chi hv l nu hl
  have hlw : l w ≠ 0 :=
    opposite_pairing_ne_zero H rho hirr tau htau w mu hw l nu hl
  have hchimu : chi = mu :=
    highWeight_eq_of_dual_pairing_ne_zero rho tau htau v w chi mu hv hw
      l nu hl hlv hlw
  subst mu
  have hcomb : l v • w - l w • v = 0 := by
    by_contra hne
    have hhigh := highWeight_linearCombination H rho hirr.1 w v chi hw hv
      (l v) (-l w) (by simpa [sub_eq_add_neg] using hne)
    have hpair := opposite_pairing_ne_zero H rho hirr tau htau
      (l v • w - l w • v) chi (by simpa [sub_eq_add_neg] using hhigh)
      l nu hl
    apply hpair
    simp [map_sub, map_smul, mul_comm]
  have heq : l v • w = l w • v := sub_eq_zero.mp hcomb
  refine ⟨l w / l v, div_ne_zero hlw hlv, ?_⟩
  apply (smul_right_injective V hlv)
  change l v • w = l v • ((l w / l v) • v)
  rw [heq, smul_smul]
  have hscalar : l v * (l w / l v) = l w := by
    simpa [mul_comm] using div_mul_cancel₀ (l w) hlv
  rw [hscalar]

private noncomputable def representationCoefficientMap
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism K (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = rho.action g)
    (l : Module.Dual k V) : V →ₗ[k] K.PolynomialFunction where
  toFun x := rationalRepresentationLinearMatrixCoefficient rho e f l x
  map_add' x y := by
    apply Variety.PolynomialFunction.ext
    intro g
    rw [rationalRepresentationLinearMatrixCoefficient_apply rho e f hf l (x + y)]
    change l ((rho.action g).1 (x + y)) =
      rationalRepresentationLinearMatrixCoefficient rho e f l x g +
        rationalRepresentationLinearMatrixCoefficient rho e f l y g
    rw [rationalRepresentationLinearMatrixCoefficient_apply rho e f hf]
    rw [rationalRepresentationLinearMatrixCoefficient_apply rho e f hf]
    simp
  map_smul' c x := by
    apply Variety.PolynomialFunction.ext
    intro g
    rw [rationalRepresentationLinearMatrixCoefficient_apply rho e f hf l (c • x)]
    rw [polynomialFunction_smul_apply]
    change l ((rho.action g).1 (c • x)) =
      c * rationalRepresentationLinearMatrixCoefficient rho e f l x g
    rw [rationalRepresentationLinearMatrixCoefficient_apply rho e f hf]
    simp

private lemma representationCoefficientMap_apply
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism K (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = rho.action g)
    (l : Module.Dual k V) (x : V) (g : Variety.Point K) :
    representationCoefficientMap rho e f hf l x g =
      l ((rho.action g).1 x) := by
  exact rationalRepresentationLinearMatrixCoefficient_apply rho e f hf l x g

private lemma rightTranslate_representationCoefficientMap
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism K (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = rho.action g)
    (l : Module.Dual k V) (h : Variety.Point K) (x : V) :
    (AlgebraicGroup.rightMulMorphism K h).pullbackAlgHom
        (representationCoefficientMap rho e f hf l x) =
      representationCoefficientMap rho e f hf l ((rho.action h).1 x) := by
  apply Variety.PolynomialFunction.ext
  intro g
  change representationCoefficientMap rho e f hf l x (g * h) = _
  rw [representationCoefficientMap_apply, representationCoefficientMap_apply,
    map_mul]
  rfl

private lemma representationCoefficientMap_injective
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V) (hirr : IsIrreducibleRepresentation rho)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism K (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = rho.action g)
    (l : Module.Dual k V) (hl : l ≠ 0) :
    Function.Injective (representationCoefficientMap rho e f hf l) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply matrixCoefficient_separates_of_irreducible rho hirr l hl (x - y)
  intro g
  have hvalue := congrArg (fun q : K.PolynomialFunction ↦ q g) hxy
  rw [representationCoefficientMap_apply, representationCoefficientMap_apply]
    at hvalue
  simpa [map_sub] using sub_eq_zero.mpr hvalue

private lemma representationCoefficientMap_range_eq_orbitSpan
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V) (hirr : IsIrreducibleRepresentation rho)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism K (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = rho.action g)
    (l : Module.Dual k V) (v : V) (hv : v ≠ 0) :
    LinearMap.range (representationCoefficientMap rho e f hf l) =
      rightTranslateOrbitSpan K (representationCoefficientMap rho e f hf l v) := by
  let F := representationCoefficientMap rho e f hf l
  let O := rightTranslateOrbitSpan K (F v)
  have hOrbitRange : O ≤ LinearMap.range F := by
    apply Submodule.span_le.mpr
    rintro q ⟨g, rfl⟩
    change (AlgebraicGroup.rightMulMorphism K g).pullbackAlgHom
      (representationCoefficientMap rho e f hf l v) ∈
        LinearMap.range (representationCoefficientMap rho e f hf l)
    rw [rightTranslate_representationCoefficientMap]
    exact ⟨(rho.action g).1 v, rfl⟩
  let W : Submodule k V := O.comap F
  have hWInvariant : IsInvariantSubmodule rho W := by
    intro g x hx
    change F ((rho.action g).1 x) ∈ O
    rw [← rightTranslate_representationCoefficientMap]
    exact rightTranslateOrbitSpan_stable K (F v) g (F x) hx
  have hvW : v ∈ W := by
    change F v ∈ O
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    exact rightMul_pullback_one K (F v)
  have hWtop : W = ⊤ := by
    rcases hirr.2 W hWInvariant with hbot | htop
    · exfalso
      apply hv
      have : v = 0 := by
        rw [hbot] at hvW
        simpa using hvW
      exact this
    · exact htop
  apply le_antisymm
  · rintro q ⟨x, rfl⟩
    have hxW : x ∈ W := by rw [hWtop]; exact Submodule.mem_top
    exact hxW
  · exact hOrbitRange

omit [IsAlgClosed k] in
private lemma hasHighWeight_smul
    {K : Variety k} [AlgebraicGroup K] {B T : ClosedSubgroup K}
    {V : Type v} [AddCommGroup V] [Module k V]
    (rho : RationalRepresentation K V) (v : V) (chi : TorusWeight T)
    (hv : HasHighWeight rho B T v chi) (c : k) (hc : c ≠ 0) :
    HasHighWeight rho B T (c • v) chi := by
  constructor
  · constructor
    · exact smul_ne_zero hc hv.1.1
    · intro b hb
      obtain ⟨d, hd⟩ := hv.1.2 b hb
      refine ⟨d, ?_⟩
      rw [map_smul, hd]
      simp [smul_smul, mul_comm]
  · constructor
    · exact smul_ne_zero hc hv.2.1
    · intro t
      rw [map_smul, hv.2.2 t]
      simp [smul_smul, mul_comm]

public theorem irreducible_highWeight_equivalent_of_oppositeBorelBigCell
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T} {P : Set D.Root}
    (H : OppositeBorelBigCell T D P) (hT : IsMaximalTorus T)
    {V W : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (rho : RationalRepresentation K V) (sigma : RationalRepresentation K W)
    (hirr : IsIrreducibleRepresentation rho)
    (hsirr : IsIrreducibleRepresentation sigma)
    (v : V) (w : W) (chi : TorusWeight T)
    (hv : HasHighWeight rho H.data.B T v chi)
    (hw : HasHighWeight sigma H.data.B T w chi) :
    AreEquivalentRepresentations rho sigma := by
  letI : Nontrivial V := ⟨⟨v, 0, hv.1.1⟩⟩
  letI : Nontrivial W := ⟨⟨w, 0, hw.1.1⟩⟩
  obtain ⟨tau, htau, htauRational⟩ :=
    rationalRepresentation_dual_exists rho hirr.1
  obtain ⟨upsilon, hupsilon, hupsilonRational⟩ :=
    rationalRepresentation_dual_exists sigma hsirr.1
  obtain ⟨l0, nu, hl0⟩ := highWeight_exists_of_borel
    H.data.Bopp T tau htauRational H.data.Bopp_isBorel hT H.torus_le_negative
  obtain ⟨m0, omega, hm0⟩ := highWeight_exists_of_borel
    H.data.Bopp T upsilon hupsilonRational H.data.Bopp_isBorel hT
      H.torus_le_negative
  have hl0v : l0 v ≠ 0 :=
    opposite_pairing_ne_zero H rho hirr tau htau v chi hv l0 nu hl0
  have hm0w : m0 w ≠ 0 :=
    opposite_pairing_ne_zero H sigma hsirr upsilon hupsilon w chi hw m0 omega hm0
  let l : Module.Dual k V := (l0 v)⁻¹ • l0
  let m : Module.Dual k W := (m0 w)⁻¹ • m0
  have hl : HasHighWeight tau H.data.Bopp T l nu :=
    hasHighWeight_smul tau l0 nu hl0 (l0 v)⁻¹ (inv_ne_zero hl0v)
  have hm : HasHighWeight upsilon H.data.Bopp T m omega :=
    hasHighWeight_smul upsilon m0 omega hm0 (m0 w)⁻¹ (inv_ne_zero hm0w)
  have hlone : l v = 1 := by
    change (l0 v)⁻¹ * l0 v = 1
    exact inv_mul_cancel₀ hl0v
  have hmone : m w = 1 := by
    change (m0 w)⁻¹ * m0 w = 1
    exact inv_mul_cancel₀ hm0w
  obtain ⟨e, f, hf⟩ := hirr.1
  obtain ⟨e', f', hf'⟩ := hsirr.1
  let F := representationCoefficientMap rho e f hf l
  let G := representationCoefficientMap sigma e' f' hf' m
  have hq : F v = G w := normalized_highWeight_coefficients_eq H
    rho sigma hirr.1 hsirr.1 v w chi hv hw tau upsilon htau hupsilon
    htauRational hupsilonRational l m nu omega hl hm hlone hmone e f hf e' f' hf'
  have hFInjective : Function.Injective F :=
    representationCoefficientMap_injective rho hirr e f hf l hl.1.1
  have hGInjective : Function.Injective G :=
    representationCoefficientMap_injective sigma hsirr e' f' hf' m hm.1.1
  have hFRange := representationCoefficientMap_range_eq_orbitSpan
    rho hirr e f hf l v hv.1.1
  have hGRange := representationCoefficientMap_range_eq_orbitSpan
    sigma hsirr e' f' hf' m w hw.1.1
  have hRange : LinearMap.range F = LinearMap.range G := by
    rw [hFRange, hGRange, hq]
  let eF : V ≃ₗ[k] LinearMap.range F := LinearEquiv.ofInjective F hFInjective
  let G' : W →ₗ[k] LinearMap.range F :=
    G.codRestrict (LinearMap.range F) (fun x ↦ by
      rw [hRange]
      exact LinearMap.mem_range_self G x)
  have hG'Injective : Function.Injective G' := by
    intro x y hxy
    apply hGInjective
    exact congrArg Subtype.val hxy
  have hG'Surjective : Function.Surjective G' := by
    intro q
    have hqG : q.val ∈ LinearMap.range G := by
      rw [← hRange]
      exact q.property
    rcases hqG with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  let eG : W ≃ₗ[k] LinearMap.range F :=
    LinearEquiv.ofBijective G' ⟨hG'Injective, hG'Surjective⟩
  let equiv : V ≃ₗ[k] W := eF.trans eG.symm
  refine ⟨equiv, ?_⟩
  intro g x
  apply hGInjective
  have hcompat (y : V) : G (equiv y) = F y := by
    have heq := eG.apply_symm_apply (eF y)
    exact congrArg Subtype.val heq
  calc
    G (equiv ((rho.action g).1 x)) = F ((rho.action g).1 x) := hcompat _
    _ = (AlgebraicGroup.rightMulMorphism K g).pullbackAlgHom (F x) :=
      (rightTranslate_representationCoefficientMap rho e f hf l g x).symm
    _ = (AlgebraicGroup.rightMulMorphism K g).pullbackAlgHom (G (equiv x)) := by
      rw [hcompat]
    _ = G ((sigma.action g).1 (equiv x)) :=
      rightTranslate_representationCoefficientMap sigma e' f' hf' m g (equiv x)

end Theory.AlgebraicGroup
