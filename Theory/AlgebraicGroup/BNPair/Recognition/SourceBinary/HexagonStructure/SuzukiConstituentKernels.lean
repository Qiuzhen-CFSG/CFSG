module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiSeparatedKernels
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanProduct
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiWeightProfile

/-!
# Distinct kernels of all five Suzuki root constituents

Transport the neighboring, same-type and separated Cartan-kernel
intersections along the literal Weyl words to obtain all ten intersections
among the five radical roots. Odd-order Frattini faithfulness identifies
each binary quotient representation kernel with its root-action kernel.
The previously computed order q−1 makes the kernels nontrivial, so they
are pairwise different. SuzukiDerivedProducts uses these precise action
kernels to isolate the middle root in the derived radical.

Source: Fong--Seitz I (6C), printed pp.40–41. The actual Cartan, roots,
panel kernels and right-conjugation words all belong to the same quotient.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
private abbrev kernelAt (i : Fin 2) (w : Weyl Q) := (rootAction Q split i w).ker
private abbrev H := (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))

private theorem kernelAt_one (i : Fin 2) : kernelAt Q split i 1 = (cartanPanelMap Q i).ker := by
  rw [kernelAt,rootAction_kernel_conjugate,map_one]
  rfl

private theorem kernelAt_mul (i : Fin 2) (v w : Weyl Q) :
    kernelAt Q split i (v*w) = (kernelAt Q split i v).comap (weylCartanAction Q split w).toMonoidHom := by
  simp only [kernelAt,rootAction_kernel_conjugate,map_mul]
  rfl

private theorem kernelAt_simple_fixed (i : Fin 2) {h : H Q}
    (hh : h ∈ kernelAt Q split i 1) : simpleCartanAction Q split i h = h := by
  rw [kernelAt_one] at hh
  exact cartanPanelMap_kernel_le_fixed Q split i (UnitarySource.actorReflection Q split i) hh

private theorem kernelAt_orthogonal (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    kernelAt Q split i (Q.simple j*Q.simple i*Q.simple j) =
      kernelAt Q split i (Q.simple j*Q.simple i) := by
  simp only [kernelAt,rootAction,RootAction.action_kernel,
    GTwoSource.orthogonal_root_stabilizer Q split hhex i j hij]

private theorem kernelAt_pair (hcore : Q.tits.B.normalCore = ⊥)
    (i j : Fin 2) (hij : i ≠ j) (w : Weyl Q) :
    kernelAt Q split i w ⊓ kernelAt Q split j w = ⊥ := by
  simp only [kernelAt,rootAction_kernel_conjugate,←comap_inf]
  have hjoint : (cartanPanelMap Q i).ker ⊓ (cartanPanelMap Q j).ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro h hh
    have h0 : h ∈ (cartanPanelMap Q 0).ker := by
      by_cases hi : i = 0
      · subst i; exact hh.1
      · have hj : j = 0 := by omega
        subst j; exact hh.2
    have h1 : h ∈ (cartanPanelMap Q 1).ker := by
      by_cases hi : i = 1
      · subst i; exact hh.1
      · have hj : j = 1 := by omega
        subst j; exact hh.2
    have he : ((cartanPanelMap Q 0).prod (cartanPanelMap Q 1)) h = 1 := Prod.ext h0 h1
    exact (cartanPanelPair_injective Q split (UnitarySource.actorReflection Q split) hcore)
      (he.trans (map_one _).symm)
  rw [hjoint]
  exact (MonoidHom.ker_eq_bot_iff _).mpr (weylCartanAction Q split w).injective

private theorem kernelAt_same (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) :
    kernelAt Q split i 1 ⊓ kernelAt Q split i (Q.simple j) = ⊥ := by
  have he := suzuki_same_type_cartan_kernels_disjoint Q split hhex hcore i j hij hKi hKj hm hn μi μj νi νj
  apply eq_bot_iff.mpr
  intro h hh
  have h1 := hh.1
  have h2 := hh.2
  rw [kernelAt_one,cartanPanelMap_kernel] at h1
  rw [kernelAt,rootAction_kernel_conjugate,cartanPanelMap_kernel] at h2
  have hw : weylCartanAction Q split (Q.simple j) = normalizerCartanAction Q (representative (Q.simple j)) := by
    conv_lhs => rw [←representative_spec (Q.simple j),weylCartanAction_lift]
  change ((weylCartanAction Q split (Q.simple j) h : H Q) : X ⧸ Q.D) ∈ embeddedPanelKernel Q i at h2
  rw [hw] at h2
  apply Subtype.ext
  apply he.le
  exact ⟨⟨h.property,h1⟩,
    (mem_normalizer_iff.mp (torus_normalizes (representative (Q.simple j))) _).mp h.property,h2⟩

private theorem kernelAt_same_three (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (h : kernelAt Q split i 1 ⊓ kernelAt Q split i (Q.simple j) = ⊥) :
    kernelAt Q split i 1 ⊓ kernelAt Q split i (Q.simple j*Q.simple i) = ⊥ ∧
      kernelAt Q split i (Q.simple j) ⊓ kernelAt Q split i (Q.simple j*Q.simple i) = ⊥ := by
  have hfirst : kernelAt Q split i 1 ⊓ kernelAt Q split i (Q.simple j*Q.simple i) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hi := kernelAt_simple_fixed Q split i hx.1
    have hx2 := hx.2
    rw [kernelAt_mul] at hx2
    change simpleCartanAction Q split i x ∈ kernelAt Q split i (Q.simple j) at hx2
    rw [hi] at hx2
    exact h.le ⟨hx.1,hx2⟩
  refine ⟨hfirst,?_⟩
  apply eq_bot_iff.mpr
  intro x hx
  let y := simpleCartanAction Q split j x
  have hy1 : y ∈ kernelAt Q split i 1 := by
    have hx1 := hx.1
    rw [kernelAt,rootAction_kernel_conjugate] at hx1
    rw [kernelAt_one]
    exact hx1
  have hy2 : y ∈ kernelAt Q split i (Q.simple j*Q.simple i) := by
    have hx2 := hx.2
    rw [←kernelAt_orthogonal Q split hhex i j hij,kernelAt_mul] at hx2
    exact hx2
  have hy : y = 1 := hfirst.le ⟨hy1,hy2⟩
  exact (simpleCartanAction Q split j).map_eq_one_iff.mp hy


private theorem kernelAt_neighbor (hcore : Q.tits.B.normalCore = ⊥)
    (i j : Fin 2) (hij : i ≠ j) :
    kernelAt Q split i 1 ⊓ kernelAt Q split j (Q.simple i) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hi := kernelAt_simple_fixed Q split i hx.1
  have hj := hx.2
  rw [kernelAt,rootAction_kernel_conjugate] at hj
  change simpleCartanAction Q split i x ∈ (cartanPanelMap Q j).ker at hj
  rw [hi,←kernelAt_one Q split j] at hj
  exact (kernelAt_pair Q split hcore i j hij 1).le ⟨hx.1,hj⟩

/-- The kernels of the five literal radical-root actions have pairwise
trivial intersection, in the full source Cartan. -/
theorem suzuki_radical_root_kernels_disjoint (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    Pairwise fun t u : Fin 5 =>
      (rootAction Q split (radicalRootKind i j t) (radicalRootWord Q i j t)).ker ⊓
        (rootAction Q split (radicalRootKind i j u) (radicalRootWord Q i j u)).ker = ⊥ := by
  have hAE := kernelAt_same Q split hhex hcore i j hij hKi hKj hm hm μi μj νi νj
  have hI := kernelAt_same_three Q split hhex i j hij hAE
  have hJ := kernelAt_same_three Q split hhex j i hij.symm
    (kernelAt_same Q split hhex hcore j i hij.symm hKj hKi hm hm μj μi νj νi)
  have hAB := kernelAt_neighbor Q split hcore i j hij
  have hBA := kernelAt_neighbor Q split hcore j i hij.symm
  have hAD := suzuki_separated_cartan_kernels_disjoint Q split hhex hcore i j hij
    hKi hKj hm μi μj νi νj
  rw [←kernelAt_one Q split i] at hAD
  have transport (k l : Fin 2) (v w z : Weyl Q)
      (hh : kernelAt Q split k v ⊓ kernelAt Q split l w = ⊥) :
      kernelAt Q split k (v*z) ⊓ kernelAt Q split l (w*z) = ⊥ := by
    rw [kernelAt_mul,kernelAt_mul,←comap_inf,hh]
    exact (MonoidHom.ker_eq_bot_iff _).mpr (weylCartanAction Q split z).injective
  have hs (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
  have hBC : kernelAt Q split j (Q.simple i) ⊓
      kernelAt Q split i (Q.simple j*Q.simple i) = ⊥ := by
    simpa only [one_mul] using transport j i 1 (Q.simple j) (Q.simple i) hBA
  have hBE : kernelAt Q split j (Q.simple i) ⊓ kernelAt Q split i (Q.simple j) = ⊥ := by
    have hh := transport i j 1 (Q.simple i*Q.simple j) (Q.simple j) hAD
    simpa only [one_mul,mul_assoc,hs,mul_one,inf_comm] using hh
  have hCD : kernelAt Q split i (Q.simple j*Q.simple i) ⊓
      kernelAt Q split j (Q.simple i*Q.simple j) = ⊥ := by
    have hh := transport j i (Q.simple i) (Q.simple j*Q.simple i) (Q.simple j) hBC
    rw [kernelAt_orthogonal Q split hhex i j hij] at hh
    exact (inf_comm _ _).trans hh
  have hDE : kernelAt Q split j (Q.simple i*Q.simple j) ⊓ kernelAt Q split i (Q.simple j) = ⊥ := by
    simpa only [one_mul,inf_comm] using transport i j 1 (Q.simple i) (Q.simple j) hAB
  intro t u htu
  have forward (t u : Fin 5) (htu : t < u) :
      kernelAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⊓
        kernelAt Q split (radicalRootKind i j u) (radicalRootWord Q i j u) = ⊥ := by
    fin_cases t <;> fin_cases u <;> norm_num at htu <;>
      dsimp only [radicalRootKind,radicalRootWord]
    · exact hAB
    · exact hI.1
    · exact hAD
    · exact hAE
    · exact hBC
    · exact hJ.2
    · exact hBE
    · exact hCD
    · exact (inf_comm _ _).trans hI.2
    · exact hDE
  rcases lt_or_gt_of_ne htu with hh | hh
  · exact forward t u hh
  · exact (inf_comm _ _).trans (forward u t hh)

/-- The binary representation has the same kernel as the literal root action:
odd Cartan elements are detected on the Frattini quotient. -/
theorem rootAtCartanFrattiniRepresentation_kernel (k : Fin 2) (w : Weyl Q) :
    (rootAtCartanFrattiniRepresentation Q split k w).ker = (rootAction Q split k w).ker := by
  ext h
  constructor
  · intro hh
    apply OddInvolutionFrattini.automorphism_eq_one_of_quotient_eq_one
      (rootAt_isTwo Q split k w).out (rootAction Q split k w h)
      (split.odd.symm.of_dvd_left
        ((orderOf_map_dvd (rootAction Q split k w) h).trans (orderOf_dvd_natCard h)))
    ext v
    have hv := congrArg (fun f : Module.End (ZMod 2)
      (Additive (rootAt Q split k w ⧸ frattini (rootAt Q split k w))) =>
        f (Additive.ofMul v)) (show rootAtCartanFrattiniRepresentation Q split k w h = 1 from hh)
    exact congrArg Additive.toMul hv
  · intro hh
    change rootAtCartanFrattiniRepresentation Q split k w h = 1
    ext v
    change Additive.ofMul ((quotientAut (frattini (rootAt Q split k w)))
      (rootAction Q split k w h) v.toMul) = v
    rw [show rootAction Q split k w h = 1 from hh,map_one]
    rfl

/-- All five actual Cartan constituents have distinct action kernels. -/
theorem suzuki_radical_root_representation_kernels_distinct (hhex : rotationOrder Q = 6)
    (hcore : Q.tits.B.normalCore = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    Pairwise fun t u : Fin 5 =>
      (rootAtCartanFrattiniRepresentation Q split (radicalRootKind i j t) (radicalRootWord Q i j t)).ker ≠
        (rootAtCartanFrattiniRepresentation Q split (radicalRootKind i j u) (radicalRootWord Q i j u)).ker := by
  intro t u htu he
  simp only [rootAtCartanFrattiniRepresentation_kernel] at he
  have hd := suzuki_radical_root_kernels_disjoint Q split hhex hcore i j hij hKi hKj hm μi μj νi νj htu
  dsimp only at hd
  rw [he,inf_idem] at hd
  exact suzuki_rootAction_kernel_ne_bot Q split hhex hcore i j hij hKi hKj hm μi μj νi νj _ _ hd

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
