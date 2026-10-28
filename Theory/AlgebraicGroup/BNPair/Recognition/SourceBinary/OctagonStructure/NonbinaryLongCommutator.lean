module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicProduct
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicRootMovement
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanOpposition
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.OddCartan

/-!
# The nonbinary long-root commutator in a two-linear octagon

The two middle fixed roots have distinct actions of the full Cartan.
Equality of their kernels propagates under the two reflections to equality
of the perpendicular kernels, contradicting the nontrivial rank-one Cartan.
The nonzero long commutator is invariant under the full Cartan and the
reflection interchanging these roots. If its intersection with one root
were trivial, its two coordinates would force those kernels to coincide.
Root irreducibility then identifies the commutator with both whole roots.

Source: Fong--Seitz I (1973), (6G), printed p.50, the first paragraph after
“Thus a > 1”. This proves the displayed long-commutator identity used in
the later containment and (4B) cardinality argument. The source adapters
retain the original full Borel and both endpoint maps.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
private abbrev kernelAt (i : Fin 2) (w : Weyl Q) := (rootAction Q split i w).ker
private theorem ssq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem kernelAt_mul (i : Fin 2) (v w : Weyl Q) :
    kernelAt Q split i (v*w) = (kernelAt Q split i v).comap (weylCartanAction Q split w).toMonoidHom := by
  simp only [kernelAt,rootAction_kernel_conjugate,map_mul]
  rfl
private theorem kernelAt_perpendicular (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    kernelAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      kernelAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  have he := perpendicular_root_stable Q split hm i j hij
    (representative (Q.simple i)) (representative_spec _)
  rw [rootAt_right Q split i _ _ _ (representative_spec _)] at he
  simp only [kernelAt,rootAction,RootAction.action_kernel,he]

private theorem perpendicular_kernels_ne
    (i : Fin 2) (w : Weyl Q)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (hq : 2 < Nat.card F)
    (hc : ⁅rankOne Q split i,
      rightConjugate (rankOne Q split i) (representative w : X ⧸ Q.D)⁆ = ⊥) :
    kernelAt Q split i 1 ≠ kernelAt Q split i w := by
  intro he
  let T := (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i
  have hcard : Nat.card T = Nat.card F - 1 := by
    rw [←Nat.card_congr (alignedCartanEquiv Q split i hK μ
      (UnitarySource.actorReflection Q split i)).toEquiv,Nat.card_units]
  have ht : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let := ht
  obtain ⟨t,htne⟩ := exists_ne (1 : T)
  have htne' : (t : X ⧸ Q.D) ≠ 1 := fun h => htne (Subtype.ext h)
  have htperp : (⟨t,t.property.1⟩ : ↥(Q.tits.B ⊓ Q.tits.N)) ∈ kernelAt Q split i w := by
    rw [kernelAt,rootAction,RootAction.action_kernel]
    intro y hy
    exact commutator_eq_bot_iff_le_centralizer.mp hc t.property.2 y
      ((comap_mono (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)) hy)
  have htroot' : (t : X ⧸ Q.D) ∈ centralizer (simpleRoot Q split i : Set _) := by
    have hh : (⟨t,t.property.1⟩ : ↥(Q.tits.B ⊓ Q.tits.N)) ∈ kernelAt Q split i 1 := he.symm ▸ htperp
    simpa only [kernelAt,rootAction,RootAction.action_kernel,rootAt_one,mem_subgroupOf] using hh
  have hz := rankOne_cartan_root_fixedFree Q split i hK μ
    (UnitarySource.actorReflection Q split i) t.property.1 t.property.2 htne'
  have hu : simpleRoot Q split i = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    exact hz.le ⟨hu,mem_centralizer_singleton_iff.mpr (htroot' u hu)⟩
  exact rootAt_ne_bot Q split i 1 (by simpa only [rootAt_one] using hu)

/-- The two middle fixed roots have different full-Cartan action kernels
when the fixed linear root is nonbinary. -/
theorem separated_nonbinary_middle_kernels
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (hq : 2 < Nat.card F)
    (hc : ⁅rankOne Q split i,
      rightConjugate (rankOne Q split i)
        (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)⁆ = ⊥) :
    (rootAction Q split i (Q.simple j*Q.simple i)).ker ≠
      (rootAction Q split i (Q.simple j*Q.simple i*Q.simple j)).ker := by
  intro he
  change kernelAt Q split i (Q.simple j*Q.simple i) =
    kernelAt Q split i (Q.simple j*Q.simple i*Q.simple j) at he
  have transport (v w z : Weyl Q) (h : kernelAt Q split i v = kernelAt Q split i w) :
      kernelAt Q split i (v*z) = kernelAt Q split i (w*z) := by
    rw [kernelAt_mul,kernelAt_mul,h]
  have h1 := transport _ _ (Q.simple i) he
  simp only [mul_assoc,ssq,mul_one] at h1
  have hp := kernelAt_perpendicular Q split hm i j hij
  simp only [mul_assoc] at hp
  rw [hp] at h1
  have h2 := transport _ _ (Q.simple j) h1
  simp only [mul_assoc,ssq,mul_one] at h2
  have hfinal : kernelAt Q split i 1 = kernelAt Q split i
      (Q.simple j*Q.simple i*Q.simple j) := h2.trans he
  exact perpendicular_kernels_ne Q split i _ hK μ hq hc hfinal
private theorem right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

/-- In the nonbinary branch the nonzero long commutator fills both middle
fixed roots. Full-Cartan invariance separates the two coordinates. -/
theorem separated_nonbinary_long_commutator
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (hq : 2 < Nat.card F)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥)
    (hperp : ⁅rankOne Q split i,
      rightConjugate (rankOne Q split i)
        (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)⁆ = ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ⊔
        rootAt Q split i (Q.simple j*Q.simple i) := by
  let D := ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆
  let B := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let n := representative (Q.simple j)
  have hswapB : rightConjugate B (n : X ⧸ Q.D) = C := by
    dsimp only [B,C,n]
    rw [right_rep]
    simp only [mul_assoc,ssq,mul_one]
  have hswapC : rightConjugate C (n : X ⧸ Q.D) = B := right_rep Q split i _ _
  have hswapD : rightConjugate D (n : X ⧸ Q.D) = D := by
    dsimp only [D,n]
    rw [right_comm]
    change ⁅rootAt Q split i (Q.simple j),
      rightConjugate (rootAt Q split i (Q.simple j))
        (representative (Q.simple j) : X ⧸ Q.D)⁆ = _
    rw [right_rep,ssq,rootAt_one,commutator_comm]
  have hD : D ≠ ⊥ := separated_long_commutator_ne_bot Q split hm i j hij
    (UnitarySource.actorReflection Q split i)
    (separated_distance_two_commutator Q split hm i j hij hK c hc)
  have hHD : Q.tits.B ⊓ Q.tits.N ≤ normalizer (D : Set (X ⧸ Q.D)) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆).map _ = _
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (torus_normalizes_simpleRoot Q split i ht),
      mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split i (Q.simple j) ht)]
  have hHB := rootAt_torus_normalizes Q split i (Q.simple j*Q.simple i*Q.simple j)
  have hBC : D ⊓ B ≠ ⊥ := by
    intro hz
    have hnotC : ¬ D ≤ C := by
      intro hle
      have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hle
      change rightConjugate D (n : X ⧸ Q.D) ≤ rightConjugate C (n : X ⧸ Q.D) at hh
      rw [hswapD,hswapC] at hh
      exact hD (bot_unique ((le_inf le_rfl hh).trans hz.le))
    obtain ⟨x,hx,hxC⟩ := Set.not_subset.mp hnotC
    obtain ⟨b,hb,d,hd,hbd⟩ := separated_long_commutator_support Q split hm i j hij hK c hc x hx
    change b*d = x at hbd
    have hbne : b ≠ 1 := by
      intro hb1
      apply hxC
      rw [←hbd,hb1,one_mul]
      exact hd
    have hle : kernelAt Q split i (Q.simple j*Q.simple i) ≤
        kernelAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
      intro t ht
      have htC : (t : X ⧸ Q.D) ∈ centralizer (C : Set (X ⧸ Q.D)) := by
        simpa only [kernelAt,rootAction,RootAction.action_kernel,mem_subgroupOf] using ht
      have hdcomm : (t : X ⧸ Q.D)*d*(t : X ⧸ Q.D)⁻¹ = d := by
        rw [←htC d hd,mul_inv_cancel_right]
      let z := (t : X ⧸ Q.D)*x*(t : X ⧸ Q.D)⁻¹*x⁻¹
      have hzD : z ∈ D := D.mul_mem
        ((mem_normalizer_iff.mp (hHD t.property) x).mp hx) (D.inv_mem hx)
      have hzb : z = (t : X ⧸ Q.D)*b*(t : X ⧸ Q.D)⁻¹*b⁻¹ := by
        dsimp only [z]
        rw [←hbd]
        calc
          _ = ((t : X ⧸ Q.D)*b*(t : X ⧸ Q.D)⁻¹)*
              ((t : X ⧸ Q.D)*d*(t : X ⧸ Q.D)⁻¹)*(b*d)⁻¹ := by group
          _ = _ := by rw [hdcomm]; group
      have hzB : z ∈ B := by
        rw [hzb]
        exact B.mul_mem ((mem_normalizer_iff.mp (hHB t.property) b).mp hb) (B.inv_mem hb)
      have hz1 : z = 1 := hz.le ⟨hzD,hzB⟩
      have hbfix : b ∈ centralizer ({(t : X ⧸ Q.D)} : Set (X ⧸ Q.D)) := by
        rw [hzb,mul_inv_eq_one] at hz1
        exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hz1).symm
      have htB : (t : X ⧸ Q.D) ∈ centralizer (B : Set (X ⧸ Q.D)) := by
        rcases linear_cartan_root_fixed_dichotomy Q split i hK μ
          (Q.simple j*Q.simple i*Q.simple j) t.property with hzero | hcent
        · exact (hbne (hzero.le ⟨hb,hbfix⟩)).elim
        · exact hcent
      simpa only [kernelAt,rootAction,RootAction.action_kernel,mem_subgroupOf] using htB
    have hle' := comap_mono (f := (weylCartanAction Q split (Q.simple j)).toMonoidHom) hle
    rw [←kernelAt_mul,←kernelAt_mul] at hle'
    simp only [mul_assoc,ssq,mul_one] at hle'
    exact separated_nonbinary_middle_kernels Q split hm i j hij hK μ hq hperp
      (le_antisymm hle (by
        change kernelAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
          kernelAt Q split i (Q.simple j*Q.simple i)
        rw [←mul_assoc] at hle'
        exact hle'))
  have he : D ⊓ B = B := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split i μ hK
    (Q.simple j*Q.simple i*Q.simple j) (D ⊓ B) inf_le_right hBC
    ((le_inf hHD hHB).trans inf_normalizer_le_normalizer_inf)
  have hBD : B ≤ D := he.symm ▸ inf_le_left
  have hCD : C ≤ D := by
    have hh := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hBD
    change rightConjugate B (n : X ⧸ Q.D) ≤ rightConjugate D (n : X ⧸ Q.D) at hh
    rwa [hswapB,hswapD] at hh
  apply le_antisymm ?_ (sup_le hBD hCD)
  intro x hx
  obtain ⟨b,hb,d,hd,rfl⟩ := separated_long_commutator_support Q split hm i j hij hK c hc x hx
  exact mul_mem_sup hb hd
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
