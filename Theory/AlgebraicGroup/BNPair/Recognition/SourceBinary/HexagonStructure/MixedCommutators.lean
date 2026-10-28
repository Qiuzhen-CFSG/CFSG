module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MiddleIsolation

/-!
# Both nonzero commutators in an unequal linear hexagon

The odd-Cartan argument has identified V_j' with the smaller middle root C.
It is central in V_j. If U_i commuted with U_i^(s_j), then both generators
of the actual R_i would centralize U_i^(s_j): conjugation by s_i exchanges
that root with C. But s_i lies in R_i and exchanges two disjoint nontrivial
roots. Thus the long-root commutator is nonzero, and Cartan irreducibility
identifies it with C.

If the two larger middle roots commuted, the three-middle-root product M
would be central in V_j. The nonzero long commutator and Cartan
irreducibility make its two outside-root centralizer kernels trivial.
The exact five-root coordinates then give Z(V_j)=M. Since R_j preserves
the radical's center, this contradicts the proved non-invariance of M.
Hence the larger-root commutator is nonzero too; Cartan irreducibility
again identifies it with C. The same coordinates and the two nonzero
pairings then identify the entire center of V_j with C. Adjacent commutations used in this argument
are transported from centrality of C by the literal simple reflections.

Every subgroup is in the same finite marked quotient, with right conjugation.
The actual local models and kernel inclusions remain earlier source inputs.
There is no ambient perfectness assumption, and the binary opposite root,
acting field four and exponent-six case are retained. The companion Irreducibility module proves the actual irreducible action;
CubicRatio proves the field ratio. Nonlinear exclusions remain open.

Source: Fong--Seitz I (6E)(b), printed pp.43--45, especially the center
argument on p.44. The CFSG companion discharges the last commutator premise
of the actual triality StructuralRow and supplies the original/geometric
applications with all seven subgroup identities.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem simple_sq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem simple_inv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (simple_sq Q i)
private theorem conjugate_commutator (A B : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ n = ⁅rightConjugate A n,rightConjugate B n⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

/-- Reflection by the first endpoint forces the long-root commutator to be nonzero
once that endpoint centralizes the middle root. -/
theorem long_commutator_ne_bot_of_middle_central
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split i)
    (hAC : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≠ ⊥ := by
  intro hAE
  have hcE := commutator_eq_bot_iff_le_centralizer.mp hAE
  have hcC := commutator_eq_bot_iff_le_centralizer.mp hAC
  have hni : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) s.val⁻¹ =
      Q.simple i := by rw [map_inv,s.class_eq,simple_inv]
  have hRC : rankOne Q split i ≤ centralizer (rootAt Q split i (Q.simple j) : Set _) := by
    apply sup_le hcE
    intro x hx
    rw [rootAt_eq Q split i (Q.simple i) s.val s.class_eq] at hx
    change (s.val : X ⧸ Q.D)*x*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i at hx
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy' : (s.val : X ⧸ Q.D)*y*(s.val : X ⧸ Q.D)⁻¹ ∈
        rootAt Q split i (Q.simple j*Q.simple i) := by
      rw [← rootAt_right Q split i (Q.simple j) (Q.simple i) s.val⁻¹ hni]
      change (s.val : X ⧸ Q.D)⁻¹*((s.val : X ⧸ Q.D)*y*(s.val : X ⧸ Q.D)⁻¹)*
        ((s.val : X ⧸ Q.D)⁻¹)⁻¹ ∈ rootAt Q split i (Q.simple j)
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using (show y ∈ rootAt Q split i (Q.simple j) from hy)
    have he := mem_centralizer_iff.mp (hcC hx) _ hy'
    apply (MulAut.conj (s.val : X ⧸ Q.D)).injective
    simpa only [map_mul,MulAut.conj_apply] using he
  have he : rootAt Q split i (Q.simple j*Q.simple i) = rootAt Q split i (Q.simple j) := by
    rw [← rootAt_right Q split i (Q.simple j) (Q.simple i) s.val s.class_eq]
    exact rightConjugate_eq_self _ (Subgroup.centralizer_le_normalizer _ (hRC s.mem_rankOne))
  have hd := exchanged_roots_disjoint Q split hm i j hij
  rw [he,disjoint_self] at hd
  exact rootAt_ne_bot Q split i (Q.simple j) hd

variable {F E : Type*} [Field F] [Finite F] [CharP F 2]
  [Field E] [Finite E] [CharP E 2]

/-- The first exact nonzero commutator in (6E)(b), including a binary smaller root. -/
theorem unequal_linear_long_commutator
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      rootAt Q split i (Q.simple j*Q.simple i) := by
  have hder := unequal_linear_derived_eq_middle_root Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hzero := unequal_linear_zero_relations Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  apply QuadrangleStructure.rootAt_eq_of_torus_invariant Q split i μi hKi _ _
    ((commutator_mono (simpleRoot_le_other_remainder Q split hm i j hij)
      (exchanged_roots_le_remainder Q split hm i j hij).1).trans hder.le)
    (long_commutator_ne_bot_of_middle_central Q split hm i j hij si hzero.1)
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (torus_normalizes_simpleRoot Q split i hn),
    mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split i (Q.simple j) hn)]

private theorem radical_le_of_five_roots
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (Z : Subgroup (X ⧸ Q.D))
    (hA : simpleRoot Q split i ≤ Z)
    (hB : rootAt Q split j (Q.simple i) ≤ Z)
    (hC : rootAt Q split i (Q.simple j*Q.simple i) ≤ Z)
    (hD : rootAt Q split j (Q.simple i*Q.simple j) ≤ Z)
    (hE : rootAt Q split i (Q.simple j) ≤ Z) :
    simpleRemainder Q split j ≤ Z := by
  intro x hx
  have hx' : x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := hx
  rw [radical_five_product Q split hm i j hij] at hx'
  obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩ := hx'
  exact Z.mul_mem (Z.mul_mem (Z.mul_mem (Z.mul_mem (hA ha) (hB hb)) (hC hc)) (hD hd)) (hE he)

/-- Centrality of the derived middle root also forces the two adjacent
commutations, by the actual two simple reflections. -/
theorem adjacent_commutators_of_middle_central
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hVC : ⁅simpleRemainder Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i)⁆ = ⊥ ∧
      ⁅rootAt Q split j (Q.simple i*Q.simple j),rootAt Q split i (Q.simple j)⁆ = ⊥ := by
  have hDV : rootAt Q split j (Q.simple i*Q.simple j) ≤ simpleRemainder Q split j :=
    le_sup_right.trans (middleRoots_le_remainder Q split hm i j hij)
  have hDC := bot_unique ((commutator_mono hDV le_rfl).trans hVC.le)
  have hDE := congrArg (fun A => rightConjugate A (representative (Q.simple i) : X ⧸ Q.D)) hDC
  rw [conjugate_commutator,
    rootAt_right Q split j _ _ _ (representative_spec _),
    rootAt_right Q split i _ _ _ (representative_spec _),
    orthogonal_root_stabilizer Q split hm j i hij.symm,
    mul_assoc,simple_sq,mul_one] at hDE
  have hDE' : ⁅rootAt Q split j (Q.simple i*Q.simple j),rootAt Q split i (Q.simple j)⁆ = ⊥ :=
    hDE.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot])
  have hAB := congrArg (fun A => rightConjugate A (representative (Q.simple j) : X ⧸ Q.D)) hDE'
  rw [conjugate_commutator,
    rootAt_right Q split j _ _ _ (representative_spec _),
    rootAt_right Q split i _ _ _ (representative_spec _),
    mul_assoc,simple_sq,mul_one,rootAt_one,commutator_comm] at hAB
  exact ⟨hAB.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]),hDE'⟩

private theorem rootAt_abelian (k : Fin 2) (w : Weyl Q)
    (h : ⁅simpleRoot Q split k,simpleRoot Q split k⁆ = ⊥) :
    ⁅rootAt Q split k w,rootAt Q split k w⁆ = ⊥ := by
  rw [rootAt,← conjugate_commutator,h]
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]

private theorem root_inf_centralizer_eq_bot
    (k : Fin 2) (w : Weyl Q) (μ : localGroup Q split k ≃* PSL(2,E))
    (hK : simpleRemainder Q split k ≤ localKernel Q k)
    (A : Subgroup (X ⧸ Q.D))
    (hA : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hne : ⁅rootAt Q split k w,A⁆ ≠ ⊥) :
    rootAt Q split k w ⊓ centralizer (A : Set (X ⧸ Q.D)) = ⊥ := by
  by_contra hh
  have hn := (le_inf (rootAt_torus_normalizes Q split k w)
    (hA.trans (normalizer_le_normalizer_centralizer A))).trans inf_normalizer_le_normalizer_inf
  have he := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split k μ hK w _ inf_le_left hh hn
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [← he]
  exact inf_le_right

private theorem middle_central_of_short_commutator_bot
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hUj : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ = ⊥)
    (hVC : ⁅simpleRemainder Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hAD : ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j)⁆ = ⊥)
    (hBE : ⁅rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j)⁆ = ⊥)
    (hBD : ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i*Q.simple j)⁆ = ⊥) :
    middleRoots Q split i j ≤ centralizer (simpleRemainder Q split j : Set (X ⧸ Q.D)) := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E₀ := rootAt Q split i (Q.simple j)
  let V := simpleRemainder Q split j
  let M := middleRoots Q split i j
  have hAV : A ≤ V := simpleRoot_le_other_remainder Q split hm i j hij
  have hEV : E₀ ≤ V := (exchanged_roots_le_remainder Q split hm i j hij).1
  have hMV : M ≤ V := middleRoots_le_remainder Q split hm i j hij
  have hBV : B ≤ V := (le_sup_left.trans le_sup_left).trans hMV
  have hDV : D ≤ V := le_sup_right.trans hMV
  have hCV : C ≤ centralizer (V : Set (X ⧸ Q.D)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hVC)
  have hM (K : Subgroup (X ⧸ Q.D))
      (hBK : ⁅B,K⁆ = ⊥) (hCK : C ≤ centralizer (K : Set (X ⧸ Q.D)))
      (hDK : ⁅D,K⁆ = ⊥) : M ≤ centralizer (K : Set (X ⧸ Q.D)) :=
    sup_le (sup_le (commutator_eq_bot_iff_le_centralizer.mp hBK) hCK)
      (commutator_eq_bot_iff_le_centralizer.mp hDK)
  obtain ⟨hAB,hDE⟩ := adjacent_commutators_of_middle_central Q split hm i j hij hVC
  apply le_centralizer_iff.mpr
  apply radical_le_of_five_roots Q split hm i j hij
  · exact le_centralizer_iff.mp (hM A ((commutator_comm B A).trans hAB)
      (hCV.trans (centralizer_le hAV)) ((commutator_comm D A).trans hAD))
  · exact le_centralizer_iff.mp (hM B (rootAt_abelian Q split j _ hUj)
      (hCV.trans (centralizer_le hBV)) ((commutator_comm D B).trans hBD))
  · exact hCV.trans (centralizer_le hMV)
  · exact le_centralizer_iff.mp (hM D hBD (hCV.trans (centralizer_le hDV))
      (rootAt_abelian Q split j _ hUj))
  · exact le_centralizer_iff.mp (hM E₀ hBE (hCV.trans (centralizer_le hEV)) hDE)


private theorem radical_center_eq_middle
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hAA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (hMC : middleRoots Q split i j ≤ centralizer (simpleRemainder Q split j : Set (X ⧸ Q.D)))
    (hAE : simpleRoot Q split i ⊓ centralizer (rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) = ⊥)
    (hEA : rootAt Q split i (Q.simple j) ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) = ⊥) :
    simpleRemainder Q split j ⊓ centralizer (simpleRemainder Q split j : Set (X ⧸ Q.D)) =
      middleRoots Q split i j := by
  let A := simpleRoot Q split i
  let E₀ := rootAt Q split i (Q.simple j)
  let V := simpleRemainder Q split j
  let M := middleRoots Q split i j
  have hAV : A ≤ V := simpleRoot_le_other_remainder Q split hm i j hij
  have hEV : E₀ ≤ V := (exchanged_roots_le_remainder Q split hm i j hij).1
  have hMA : M ≤ centralizer (A : Set (X ⧸ Q.D)) := hMC.trans (centralizer_le hAV)
  have hME : M ≤ centralizer (E₀ : Set (X ⧸ Q.D)) := hMC.trans (centralizer_le hEV)
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := hx.1
    rw [radical_five_product Q split hm i j hij] at hx'
    obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩ := hx'
    have hmM : b*c*d ∈ M := M.mul_mem
      (M.mul_mem (mem_sup_left (mem_sup_left hb)) (mem_sup_left (mem_sup_right hc)))
      (mem_sup_right hd)
    have haA : a ∈ centralizer (A : Set (X ⧸ Q.D)) :=
      commutator_eq_bot_iff_le_centralizer.mp hAA ha
    have hamA : a*b*c*d ∈ centralizer (A : Set (X ⧸ Q.D)) := by
      simpa only [mul_assoc] using (centralizer (A : Set (X ⧸ Q.D))).mul_mem haA (hMA hmM)
    have heA : e ∈ centralizer (A : Set (X ⧸ Q.D)) := by
      have hh := (centralizer (A : Set (X ⧸ Q.D))).mul_mem
        ((centralizer (A : Set (X ⧸ Q.D))).inv_mem hamA) ((centralizer_le hAV) hx.2)
      simpa only [inv_mul_cancel_left] using hh
    have he1 : e = 1 := mem_bot.mp (hEA ▸ ⟨he,heA⟩)
    have hamE : a*b*c*d ∈ centralizer (E₀ : Set (X ⧸ Q.D)) := by
      simpa only [he1,mul_one] using (centralizer_le hEV) hx.2
    have haE : a ∈ centralizer (E₀ : Set (X ⧸ Q.D)) := by
      have hh := (centralizer (E₀ : Set (X ⧸ Q.D))).mul_mem hamE
        ((centralizer (E₀ : Set (X ⧸ Q.D))).inv_mem (hME hmM))
      have heq : a*b*c*d*(b*c*d)⁻¹ = a := by group
      rwa [heq] at hh
    have ha1 : a = 1 := mem_bot.mp (hAE ▸ ⟨ha,haE⟩)
    simpa only [ha1,he1,one_mul,mul_one] using hmM
  · exact le_inf (middleRoots_le_remainder Q split hm i j hij) hMC

/-- The second nonzero commutator of (6E)(b), on the two actual larger
middle roots. If it vanished, the radical's center would be exactly the
three-middle-root product, contradicting its proved non-invariance. -/
theorem unequal_linear_short_commutator
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i*Q.simple j)⁆ =
      rootAt Q split i (Q.simple j*Q.simple i) := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E₀ := rootAt Q split i (Q.simple j)
  let V := simpleRemainder Q split j
  let M := middleRoots Q split i j
  have hMV : M ≤ V := middleRoots_le_remainder Q split hm i j hij
  have hBV : B ≤ V := (le_sup_left.trans le_sup_left).trans hMV
  have hDV : D ≤ V := le_sup_right.trans hMV
  have hder := unequal_linear_derived_eq_middle_root Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hzero := unequal_linear_zero_relations Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hlong := unequal_linear_long_commutator Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hlongne : ⁅A,E₀⁆ ≠ ⊥ := by
    rw [show ⁅A,E₀⁆ = C from hlong]
    exact rootAt_ne_bot Q split i _
  have hVC := derived_middle_root_radical_centralized Q split j hm i hij hKi μi hKj hder
  have hnon : ⁅B,D⁆ ≠ ⊥ := by
    intro hz
    have hMC := middle_central_of_short_commutator_bot Q split hm i j hij
      (simpleRoot_commutator_eq_bot_of_linear Q split j μj) hVC hzero.2.2.1 hzero.2.2.2 hz
    have hEA : E₀ ⊓ centralizer (A : Set (X ⧸ Q.D)) = ⊥ :=
      root_inf_centralizer_eq_bot Q split i _ μi hKi A (torus_normalizes_simpleRoot Q split i)
        (by rwa [commutator_comm])
    have hAE : A ⊓ centralizer (E₀ : Set (X ⧸ Q.D)) = ⊥ := by
      have hh := root_inf_centralizer_eq_bot Q split i 1 μi hKi E₀
        (rootAt_torus_normalizes Q split i (Q.simple j)) (by simpa only [rootAt_one] using hlongne)
      simpa only [rootAt_one] using hh
    have he := radical_center_eq_middle Q split hm i j hij
      (simpleRoot_commutator_eq_bot_of_linear Q split i μi) hMC hAE hEA
    have hRV : rankOne Q split j ≤ normalizer (V : Set (X ⧸ Q.D)) :=
      (rankOne_le_parabolic Q split j).trans (remainder_parabolic_normalizes Q split j hKj)
    have hn : rankOne Q split j ≤ normalizer (M : Set (X ⧸ Q.D)) := by
      change rankOne Q split j ≤ normalizer (middleRoots Q split i j : Set (X ⧸ Q.D))
      rw [← he]
      exact (le_inf hRV (hRV.trans (normalizer_le_normalizer_centralizer V))).trans
        inf_normalizer_le_normalizer_inf
    exact (unequal_linear_middle_structure Q split j hKj μj sj hm i hij hKi μi si ha hab hE hF).1 hn
  apply QuadrangleStructure.rootAt_eq_of_torus_invariant Q split i μi hKi _ _
    ((commutator_mono hBV hDV).trans hder.le) hnon
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split j (Q.simple i) hn),
    mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split j (Q.simple i*Q.simple j) hn)]

/-- The intrinsic center of the unequal radical, expressed as an intersection
in the same ambient quotient, is exactly its derived middle root. -/
theorem unequal_linear_radical_center
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    simpleRemainder Q split j ⊓ centralizer (simpleRemainder Q split j : Set (X ⧸ Q.D)) =
      rootAt Q split i (Q.simple j*Q.simple i) := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E₀ := rootAt Q split i (Q.simple j)
  let V := simpleRemainder Q split j
  have hMV := middleRoots_le_remainder Q split hm i j hij
  have hAV : A ≤ V := simpleRoot_le_other_remainder Q split hm i j hij
  have hBV : B ≤ V := (le_sup_left.trans le_sup_left).trans hMV
  have hCV : C ≤ V := (le_sup_right.trans le_sup_left).trans hMV
  have hDV : D ≤ V := le_sup_right.trans hMV
  have hEV : E₀ ≤ V := (exchanged_roots_le_remainder Q split hm i j hij).1
  have hder := unequal_linear_derived_eq_middle_root Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hz := unequal_linear_zero_relations Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hl := unequal_linear_long_commutator Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hs := unequal_linear_short_commutator Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF
  have hlongne : ⁅A,E₀⁆ ≠ ⊥ := by rw [show ⁅A,E₀⁆ = C from hl]; exact rootAt_ne_bot Q split i _
  have hshortne : ⁅B,D⁆ ≠ ⊥ := by rw [show ⁅B,D⁆ = C from hs]; exact rootAt_ne_bot Q split i _
  have hVC := derived_middle_root_radical_centralized Q split j hm i hij hKi μi hKj hder
  have hZ : C ≤ centralizer (V : Set (X ⧸ Q.D)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hVC)
  obtain ⟨hAB,hDE⟩ := adjacent_commutators_of_middle_central Q split hm i j hij hVC
  have hEA : E₀ ⊓ centralizer (A : Set (X ⧸ Q.D)) = ⊥ :=
    root_inf_centralizer_eq_bot Q split i _ μi hKi A (torus_normalizes_simpleRoot Q split i)
      (by rwa [commutator_comm])
  have hAE : A ⊓ centralizer (E₀ : Set (X ⧸ Q.D)) = ⊥ := by
    have hh := root_inf_centralizer_eq_bot Q split i 1 μi hKi E₀
      (rootAt_torus_normalizes Q split i (Q.simple j)) (by simpa only [rootAt_one] using hlongne)
    simpa only [rootAt_one] using hh
  have hDB : D ⊓ centralizer (B : Set (X ⧸ Q.D)) = ⊥ :=
    root_inf_centralizer_eq_bot Q split j _ μj hKj B (rootAt_torus_normalizes Q split j _)
      (by rwa [commutator_comm])
  have hBD : B ⊓ centralizer (D : Set (X ⧸ Q.D)) = ⊥ :=
    root_inf_centralizer_eq_bot Q split j _ μj hKj D (rootAt_torus_normalizes Q split j _) hshortne
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := hx.1
    rw [radical_five_product Q split hm i j hij] at hx'
    obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩ := hx'
    have haA := commutator_eq_bot_iff_le_centralizer.mp
      (simpleRoot_commutator_eq_bot_of_linear Q split i μi) ha
    have hbA := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hAB) hb
    have hcA := (hZ.trans (centralizer_le hAV)) hc
    have hdA := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz.2.2.1) hd
    have habcdA := (centralizer (A : Set (X ⧸ Q.D))).mul_mem
      ((centralizer (A : Set (X ⧸ Q.D))).mul_mem
        ((centralizer (A : Set (X ⧸ Q.D))).mul_mem haA hbA) hcA) hdA
    have heA : e ∈ centralizer (A : Set (X ⧸ Q.D)) := by
      have hh := (centralizer (A : Set (X ⧸ Q.D))).mul_mem
        ((centralizer (A : Set (X ⧸ Q.D))).inv_mem habcdA) ((centralizer_le hAV) hx.2)
      simpa only [inv_mul_cancel_left] using hh
    have he1 : e = 1 := mem_bot.mp (hEA ▸ ⟨he,heA⟩)
    have hbE := commutator_eq_bot_iff_le_centralizer.mp hz.2.2.2 hb
    have hcE := (hZ.trans (centralizer_le hEV)) hc
    have hdE := commutator_eq_bot_iff_le_centralizer.mp hDE hd
    have hmE := (centralizer (E₀ : Set (X ⧸ Q.D))).mul_mem
      ((centralizer (E₀ : Set (X ⧸ Q.D))).mul_mem hbE hcE) hdE
    have haE : a ∈ centralizer (E₀ : Set (X ⧸ Q.D)) := by
      have hxE : a*b*c*d ∈ centralizer (E₀ : Set (X ⧸ Q.D)) := by
        simpa only [he1,mul_one] using (centralizer_le hEV) hx.2
      have hh := (centralizer (E₀ : Set (X ⧸ Q.D))).mul_mem hxE
        ((centralizer (E₀ : Set (X ⧸ Q.D))).inv_mem hmE)
      have heq : a*b*c*d*(b*c*d)⁻¹ = a := by group
      rwa [heq] at hh
    have ha1 : a = 1 := mem_bot.mp (hAE ▸ ⟨ha,haE⟩)
    have hxB : b*c*d ∈ centralizer (B : Set (X ⧸ Q.D)) := by
      simpa only [ha1,he1,one_mul,mul_one] using (centralizer_le hBV) hx.2
    have hbB := commutator_eq_bot_iff_le_centralizer.mp
      (rootAt_abelian Q split j (Q.simple i) (simpleRoot_commutator_eq_bot_of_linear Q split j μj)) hb
    have hcB := (hZ.trans (centralizer_le hBV)) hc
    have hdB : d ∈ centralizer (B : Set (X ⧸ Q.D)) := by
      have hh := (centralizer (B : Set (X ⧸ Q.D))).mul_mem
        ((centralizer (B : Set (X ⧸ Q.D))).inv_mem
          ((centralizer (B : Set (X ⧸ Q.D))).mul_mem hbB hcB)) hxB
      simpa only [inv_mul_cancel_left] using hh
    have hd1 : d = 1 := mem_bot.mp (hDB ▸ ⟨hd,hdB⟩)
    have hxD : b*c ∈ centralizer (D : Set (X ⧸ Q.D)) := by
      simpa only [ha1,he1,hd1,one_mul,mul_one] using (centralizer_le hDV) hx.2
    have hbD : b ∈ centralizer (D : Set (X ⧸ Q.D)) := by
      have hh := (centralizer (D : Set (X ⧸ Q.D))).mul_mem hxD
        ((centralizer (D : Set (X ⧸ Q.D))).inv_mem ((hZ.trans (centralizer_le hDV)) hc))
      simpa only [mul_inv_cancel_right] using hh
    have hb1 : b = 1 := mem_bot.mp (hBD ▸ ⟨hb,hbD⟩)
    simpa only [ha1,hb1,hd1,he1,one_mul,mul_one] using (show c ∈ rootAt Q split i (Q.simple j*Q.simple i) from hc)
  · exact le_inf hCV hZ

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

