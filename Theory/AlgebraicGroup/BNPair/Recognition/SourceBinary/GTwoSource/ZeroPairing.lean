module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.RootPairing

/-!
# Excluding two zero middle pairings in characteristic two

This proves the characteristic-two exclusion in Fong--Seitz II (9.3) on
one actual marked quotient, for either orientation and every finite field
of characteristic two. The earlier radical-kernel inclusions, actual local
PSL₂ identifications and rank-one reflection witnesses remain explicit.

First assume both middle pairings vanish. If an orthogonal pairing were
nonzero, Cartan irreducibility would give trivial centralizer kernels on
its root factors. The five-root coordinates then identify the entire
short radical center with A. Its rank-one normalizer must centralize this
root: use the proved small-action bound for q ≥ 4 and the order-two
normalizer argument for q = 2. Weyl transport contradicts nonzero
orthogonal pairing. Thus the whole positive commutation table holds.

For the remaining exclusion no module-classification theorem is needed.
The commutator of F(1) and E(1) lies in the four middle roots, now an
elementary abelian group. Each simple involution therefore centralizes
that commutator. The rank-one cubics show that F(1) fixes no nonidentity
D element and E(1) fixes no nonidentity B element. Consequently the
commutator lies in AC. Applying the short cubic to B(1) then puts E(1)
in its complementary radical, contradicting the root decomposition.

The chosen orientation has zero opposite pairing and nonzero DC. Its
binary coefficient is already normalized by RootPairing, and the
NonzeroPairingApplication consumer now gives the full binary comparison
without a pairing premise. Compatible whole-pinning labels for larger
fields remain a source obligation.

Source: Fong--Seitz I (3G), (5C), (6E)(a), printed pp.14--16,25--28,43;
II (9.1)--(9.3), printed p.211. Subgroup transport uses right conjugation;
the element calculation uses the consumer's left commutator convention.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))

private theorem ssq (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem conjugate_commutator (A B : Subgroup (X ⧸ Q.D)) (v : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ v = ⁅rightConjugate A v,rightConjugate B v⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

include μ in
private theorem carrier_abelian (short : Fin 2) (k : Fin 6) :
    ⁅positiveCarrier Q split short k,positiveCarrier Q split short k⁆ = ⊥ := by
  have h (i : Fin 2) (w : Weyl Q) : ⁅rootAt Q split i w,rootAt Q split i w⁆ = ⊥ := by
    rw [rootAt,←conjugate_commutator,simpleRoot_commutator_eq_bot_of_linear Q split i (μ i)]
    simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
  fin_cases k
  · exact h _ _
  · exact h _ _
  · exact h _ _
  · exact h _ _
  · exact simpleRoot_commutator_eq_bot_of_linear Q split _ (μ _)
  · exact simpleRoot_commutator_eq_bot_of_linear Q split _ (μ _)

include hK μ in
private theorem carrier_kernel (short : Fin 2) (k l : Fin 6)
    (hne : ⁅positiveCarrier Q split short k,positiveCarrier Q split short l⁆ ≠ ⊥) :
    positiveCarrier Q split short k ⊓ centralizer (positiveCarrier Q split short l : Set _) = ⊥ := by
  let C := positiveCarrier Q split short k
  let D := positiveCarrier Q split short l
  by_contra hh
  have hn := (le_inf (positiveCarrier_torus_normalizes Q split short k)
    ((positiveCarrier_torus_normalizes Q split short l).trans
      (normalizer_le_normalizer_centralizer D))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨i,w,hi⟩ : ∃ (i : Fin 2) (w : Weyl Q), C = rootAt Q split i w := by
    fin_cases k
    · exact ⟨1-short,Q.simple short*Q.simple (1-short),rfl⟩
    · exact ⟨1-short,Q.simple short,rfl⟩
    · exact ⟨short,Q.simple (1-short)*Q.simple short,rfl⟩
    · exact ⟨short,Q.simple (1-short),rfl⟩
    · exact ⟨1-short,1,(rootAt_one Q split (1-short)).symm⟩
    · exact ⟨short,1,(rootAt_one Q split short).symm⟩
  have he : C ⊓ centralizer (D : Set _) = C := by
    apply QuadrangleStructure.rootAt_eq_of_torus_invariant Q split i (μ i) (hK i) w
      (C ⊓ centralizer (D : Set _)) (hi ▸ inf_le_left) hh hn |>.trans hi.symm
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  change C ≤ centralizer (D : Set _)
  rw [←he]
  exact inf_le_right

/-- Weyl transport of the two vanishing middle pairings. -/
theorem carrier_zero_pairing_transports (hm : rotationOrder Q = 6) (short : Fin 2)
    (hba : ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥)
    (hdc : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ = ⊥) :
    ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 0⁆ = ⊥ ∧
    ⁅positiveCarrier Q split short 5,positiveCarrier Q split short 2⁆ = ⊥ := by
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  have ea := congrArg (fun V => rightConjugate V (representative (Q.simple short) : X ⧸ Q.D)) hba
  change rightConjugate ⁅rootAt Q split (1-short) (Q.simple short),
    rootAt Q split (1-short) (Q.simple short*Q.simple (1-short))⁆ _ = _ at ea
  rw [conjugate_commutator,rootAt_right Q split _ _ _ _ (representative_spec _),
    rootAt_right Q split _ _ _ _ (representative_spec _),ssq,rootAt_one,
    orthogonal_root_stabilizer Q split hm (1-short) short hij.symm] at ea
  have fc := congrArg (fun V => rightConjugate V (representative (Q.simple (1-short)) : X ⧸ Q.D)) hdc
  change rightConjugate ⁅rootAt Q split short (Q.simple (1-short)),
    rootAt Q split short (Q.simple (1-short)*Q.simple short)⁆ _ = _ at fc
  rw [conjugate_commutator,rootAt_right Q split _ _ _ _ (representative_spec _),
    rootAt_right Q split _ _ _ _ (representative_spec _),ssq,rootAt_one,
    orthogonal_root_stabilizer Q split hm short (1-short) hij] at fc
  exact ⟨ea.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]),
    fc.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot])⟩

private theorem orthogonal_nonzero_transports (short : Fin 2)
    (hec : ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ ≠ ⊥) :
    ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 1⁆ ≠ ⊥ ∧
    ⁅positiveCarrier Q split short 5,positiveCarrier Q split short 0⁆ ≠ ⊥ := by
  have hdb : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 1⁆ ≠ ⊥ := by
    intro hz
    have he := congrArg (fun V => rightConjugate V (representative (Q.simple short) : X ⧸ Q.D)) hz
    change rightConjugate ⁅rootAt Q split short (Q.simple (1-short)),
      rootAt Q split (1-short) (Q.simple short)⁆ _ = _ at he
    rw [conjugate_commutator,rootAt_right Q split _ _ _ _ (representative_spec _),
      rootAt_right Q split _ _ _ _ (representative_spec _),ssq,rootAt_one,commutator_comm] at he
    exact hec (he.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]))
  refine ⟨hdb,?_⟩
  intro hz
  have he := congrArg (fun V => rightConjugate V (representative (Q.simple (1-short)) : X ⧸ Q.D)) hz
  change rightConjugate ⁅simpleRoot Q split short,
    rootAt Q split (1-short) (Q.simple short*Q.simple (1-short))⁆ _ = _ at he
  rw [conjugate_commutator,←rootAt_eq Q split short (Q.simple (1-short)) _ (representative_spec _),
    rootAt_right Q split _ _ _ _ (representative_spec _),mul_assoc,ssq,mul_one] at he
  exact hdb (he.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]))

include hK μ in
/-- In the simultaneous-zero branch, nonzero orthogonal pairing makes A
exactly the intrinsic center of the short parabolic radical. -/
theorem radical_center_of_zero_pairings_of_orthogonal_ne_bot
    (hm : rotationOrder Q = 6) (short : Fin 2)
    (hba : ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥)
    (hdc : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ = ⊥)
    (hec : ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ ≠ ⊥) :
    simpleRemainder Q split short ⊓ centralizer (simpleRemainder Q split short : Set _) =
      positiveCarrier Q split short 0 := by
  let V := simpleRemainder Q split short
  let A := positiveCarrier Q split short 0
  have hij : (1-short : Fin 2) ≠ short := by fin_cases short <;> decide
  obtain ⟨hca,hcb,hda,hed,hfb⟩ := positiveCarrier_adjacent_commutators Q split hm hK short
  have hea := (carrier_zero_pairing_transports Q split hm short hba hdc).1
  have hdb := (orthogonal_nonzero_transports Q split short hec).1
  have hCE := carrier_kernel Q split hK μ short 2 4 (by rwa [commutator_comm])
  have hEC := carrier_kernel Q split hK μ short 4 2 hec
  have hBD := carrier_kernel Q split hK μ short 1 3 (by rwa [commutator_comm])
  have hDB := carrier_kernel Q split hK μ short 3 1 hdb
  have hMV := middleRoots_le_remainder Q split hm (1-short) short hij
  have hEV : positiveCarrier Q split short 4 ≤ V := simpleRoot_le_other_remainder Q split hm _ _ hij
  have hBV : positiveCarrier Q split short 1 ≤ V := (exchanged_roots_le_remainder Q split hm _ _ hij).1
  have hDV : positiveCarrier Q split short 3 ≤ V := (le_sup_left.trans le_sup_left).trans hMV
  have hAV : A ≤ V := (le_sup_right.trans le_sup_left).trans hMV
  have hCV : positiveCarrier Q split short 2 ≤ V := le_sup_right.trans hMV
  have hAZ : A ≤ centralizer (V : Set _) := by
    apply le_centralizer_iff.mpr
    intro x hx
    have hx' : x ∈ (V : Set (X ⧸ Q.D)) := hx
    rw [radical_five_product Q split hm (1-short) short hij] at hx'
    obtain ⟨edac,⟨eda,⟨ed,⟨e,he,d,hd,rfl⟩,a,ha,rfl⟩,c,hc,rfl⟩,b,hb,rfl⟩ := hx'
    change e*d*a*c*b ∈ centralizer (A : Set _)
    have heA : e ∈ centralizer (A : Set (X ⧸ Q.D)) := commutator_eq_bot_iff_le_centralizer.mp hea he
    have hdA : d ∈ centralizer (A : Set (X ⧸ Q.D)) := commutator_eq_bot_iff_le_centralizer.mp hda hd
    have haA : a ∈ centralizer (A : Set (X ⧸ Q.D)) := commutator_eq_bot_iff_le_centralizer.mp (carrier_abelian Q split μ short 0) ha
    have hcA : c ∈ centralizer (A : Set (X ⧸ Q.D)) := commutator_eq_bot_iff_le_centralizer.mp hca hc
    have hbA : b ∈ centralizer (A : Set (X ⧸ Q.D)) := commutator_eq_bot_iff_le_centralizer.mp hba hb
    exact mul_mem (mul_mem (mul_mem (mul_mem heA hdA) haA) hcA) hbA
  refine le_antisymm ?_ (le_inf hAV hAZ)
  intro x hx
  have hx' : x ∈ (V : Set (X ⧸ Q.D)) := hx.1
  rw [radical_five_product Q split hm (1-short) short hij] at hx'
  obtain ⟨edac,⟨eda,⟨ed,⟨e,he,d,hd,rfl⟩,a,ha,rfl⟩,c,hc,rfl⟩,b,hb,rfl⟩ := hx'
  have hh (k l : Fin 6) (hz : ⁅positiveCarrier Q split short k,positiveCarrier Q split short l⁆ = ⊥)
      {y : X ⧸ Q.D} (hy : y ∈ positiveCarrier Q split short k) :
      y ∈ centralizer (positiveCarrier Q split short l : Set _) :=
    commutator_eq_bot_iff_le_centralizer.mp hz hy
  have hdcab : d*a*c*b ∈ centralizer (positiveCarrier Q split short 2 : Set _) :=
    mul_mem (mul_mem (mul_mem (hh 3 2 hdc hd) (hh 0 2 (by rwa [commutator_comm]) ha))
      (hh 2 2 (carrier_abelian Q split μ short 2) hc)) (hh 1 2 (by rwa [commutator_comm]) hb)
  have heC : e ∈ centralizer (positiveCarrier Q split short 2 : Set _) := by
    have ht := mul_mem ((centralizer_le hCV) hx.2) (inv_mem hdcab)
    simpa only [mul_assoc,mul_inv_rev,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ht
  have he1 : e = 1 := mem_bot.mp (hEC ▸ ⟨he,heC⟩)
  have hdcad : d*a*c ∈ centralizer (positiveCarrier Q split short 3 : Set _) :=
    mul_mem (mul_mem (hh 3 3 (carrier_abelian Q split μ short 3) hd)
      (hh 0 3 (by rwa [commutator_comm]) ha)) (hh 2 3 (by rwa [commutator_comm]) hc)
  have hbD : b ∈ centralizer (positiveCarrier Q split short 3 : Set _) := by
    have hxD : d*a*c*b ∈ centralizer (positiveCarrier Q split short 3 : Set _) := by
      simpa only [he1,one_mul] using (centralizer_le hDV) hx.2
    have ht := mul_mem (inv_mem hdcad) hxD
    simpa only [inv_mul_cancel_left] using ht
  have hb1 : b = 1 := mem_bot.mp (hBD ▸ ⟨hb,hbD⟩)
  have hacB : a*c ∈ centralizer (positiveCarrier Q split short 1 : Set _) :=
    mul_mem (hh 0 1 (by rwa [commutator_comm]) ha) (hh 2 1 hcb hc)
  have hdB : d ∈ centralizer (positiveCarrier Q split short 1 : Set _) := by
    have hxB : d*a*c ∈ centralizer (positiveCarrier Q split short 1 : Set _) := by
      simpa only [he1,hb1,one_mul,mul_one] using (centralizer_le hBV) hx.2
    have ht := mul_mem hxB (inv_mem hacB)
    simpa only [mul_assoc,mul_inv_rev,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ht
  have hd1 : d = 1 := mem_bot.mp (hDB ▸ ⟨hd,hdB⟩)
  have hcE : c ∈ centralizer (positiveCarrier Q split short 4 : Set _) := by
    have hxE : a*c ∈ centralizer (positiveCarrier Q split short 4 : Set _) := by
      simpa only [he1,hb1,hd1,one_mul,mul_one] using (centralizer_le hEV) hx.2
    have ht := mul_mem (inv_mem (hh 0 4 (by rwa [commutator_comm]) ha)) hxE
    simpa only [inv_mul_cancel_left] using ht
  have hc1 : c = 1 := mem_bot.mp (hCE ▸ ⟨hc,hcE⟩)
  simpa only [he1,hb1,hd1,hc1,one_mul,mul_one] using (show a ∈ A from ha)

include hK μ in
/-- A whole rank-one group centralizes an invariant opposite middle root
of the same field size, including field two. -/
theorem invariant_equal_middle_root_centralized (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hn : rankOne Q split j ≤ normalizer (rootAt Q split i (Q.simple j*Q.simple i) : Set _)) :
    ⁅rankOne Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
  let := Fintype.ofFinite F
  obtain ⟨b,_,hb⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^(b : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hb
  by_cases hbin : (b : ℕ) = 1
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    apply hn.trans (normalizer_le_centralizer_of_card_two _ _)
    change Nat.card (rightConjugate (simpleRoot Q split i) _) = 2
    rw [card_rightConjugate,simpleRoot_card Q split i (hK i) (μ i),hF,hbin,pow_one]
  · apply invariant_middle_root_centralized Q split j (hK j) (μ j) s hm i hij hn
      (by have := b.pos; omega) hF
    rw [simpleRoot_card Q split i (hK i) (μ i),hF]
    exact Nat.pow_lt_pow_right (by decide) (by have := b.pos; omega)

include hK μ in
/-- The simultaneous-zero branch forces orthogonal commutation. The radical
center argument, not an assumed polynomial equation, removes this premise. -/
theorem orthogonal_eq_bot_of_zero_pairings (hm : rotationOrder Q = 6)
    (short : Fin 2) (s : RootReflection Q split short)
    (hba : ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥)
    (hdc : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ = ⊥) :
    ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ = ⊥ := by
  by_contra hec
  have hcenter := radical_center_of_zero_pairings_of_orthogonal_ne_bot Q split hK μ hm short hba hdc hec
  have hRV := (rankOne_le_parabolic Q split short).trans
    (remainder_parabolic_normalizes Q split short (hK short))
  have hn : rankOne Q split short ≤ normalizer (positiveCarrier Q split short 0 : Set _) := by
    rw [←hcenter]
    exact (le_inf hRV (hRV.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hc := invariant_equal_middle_root_centralized Q split hK μ hm (1-short) short
    (by fin_cases short <;> decide) s hn
  have hfa := (orthogonal_nonzero_transports Q split short hec).2
  exact hfa (bot_unique ((commutator_mono (show simpleRoot Q split short ≤ rankOne Q split short from le_sup_left)
    le_rfl).trans hc.le))


private theorem conjugation_fixes {Y : Type*} [Group Y] {x y : Y} (h : Commute x y) :
    MulAut.conj x y = y := by
  change x*y*x⁻¹=y
  rw [h.eq,mul_assoc,mul_inv_cancel,mul_one]

private theorem cubic_fixed_partner {Y : Type*} [Group Y] (u v a b : Y)
    (hua : Commute u a) (hub : Commute u b)
    (hva : MulAut.conj v a=b) (hvb : MulAut.conj v b=a)
    (hcube : (u*v)^3=1) : a=b := by
  let t := MulAut.conj (u*v)
  have hta : t a=b := by
    change MulAut.conj (u*v) a=b
    rw [map_mul,MulAut.mul_apply,hva,conjugation_fixes hub]
  have htb : t b=a := by
    change MulAut.conj (u*v) b=a
    rw [map_mul,MulAut.mul_apply,hvb,conjugation_fixes hua]
  calc
    a = MulAut.conj ((u*v)^3) a := by rw [hcube]; simp
    _ = t (t (t a)) := by simp only [t,pow_succ,pow_zero,map_mul,map_one,MulAut.mul_apply,MulAut.one_apply]
    _ = b := by rw [hta,htb,hta]

private theorem conjugate_commutator_fixed {Y : Type*} [Group Y] (x y : Y)
    (hx : x⁻¹=x) (hy : y⁻¹=y) (hk : ⁅x,y⁆⁻¹=⁅x,y⁆) :
    MulAut.conj x ⁅x,y⁆=⁅x,y⁆ ∧ MulAut.conj y ⁅x,y⁆=⁅x,y⁆ := by
  have hx2 : x*x=1 := by simpa only [hx] using inv_mul_cancel x
  have hy2 : y*y=1 := by simpa only [hy] using inv_mul_cancel y
  constructor
  · calc
      _ = ⁅x,y⁆⁻¹ := by simp only [MulAut.conj_apply,commutatorElement_def,mul_inv_rev,hx,hy,←mul_assoc,hx2,one_mul]
      _ = _ := hk
  · calc
      _ = ⁅x,y⁆⁻¹ := by simp only [MulAut.conj_apply,commutatorElement_def,mul_inv_rev,hx,hy,mul_assoc,hy2,mul_one]
      _ = _ := hk

variable (n : ∀ i, RootReflection Q split i) (short : Fin 2)

private theorem root_mem (k : Fin 6) (a : F) :
    (alignedSourceRoots Q split hK μ n short).x k a ∈ positiveCarrier Q split short k := by
  rw [←alignedSourceRoots_range Q split hK μ n short k]
  exact ⟨.ofAdd a,rfl⟩

private theorem root_inj (k : Fin 6) :
    Function.Injective ((alignedSourceRoots Q split hK μ n short).x k) :=
  (alignedSourceRoots_injective Q split hK μ n short k).comp Multiplicative.ofAdd.injective

private theorem simple_cubic (i : Fin 2) :
    (alignedPinningHom Q split i (hK i) (μ i) (n i)
      (Theory.PSL2.SemilinearCoverage.uni 1) * ((n i).val : X ⧸ Q.D))^3=1 := by
  let φ := alignedPinningHom Q split i (hK i) (μ i) (n i)
  have hh : (Theory.PSL2.SemilinearCoverage.uni (1 : F) *
      Theory.PSL2.SemilinearCoverage.weyl F)^3=1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ,Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
  have he := congrArg φ hh
  simpa only [map_pow,map_mul,map_one,φ,alignedPinningHom_weyl] using he

private theorem zero_pairings_simple_commutator_coordinates (hm : rotationOrder Q = 6) :
    ∃ a b c d : F,
      ⁅(alignedSourceRoots Q split hK μ n short).x 5 1,
        (alignedSourceRoots Q split hK μ n short).x 4 1⁆ =
        (alignedSourceRoots Q split hK μ n short).x 3 d *
          (alignedSourceRoots Q split hK μ n short).x 0 a *
          (alignedSourceRoots Q split hK μ n short).x 2 c *
          (alignedSourceRoots Q split hK μ n short).x 1 b := by
  let L := alignedSourceRoots Q split hK μ n short
  let k := ⁅L.x 5 1,L.x 4 1⁆
  have hij : (1-short : Fin 2) ≠ short := by fin_cases short <;> decide
  have hkU : k ∈ ⁅split.U,split.U⁆ := commutator_mem_commutator
    (positiveCarrier_le Q split hm short 5 (root_mem Q split hK μ n short 5 1))
    (positiveCarrier_le Q split hm short 4 (root_mem Q split hK μ n short 4 1))
  have hk (i : Fin 2) : k ∈ simpleRemainder Q split i :=
    unipotent_commutator_le_remainder Q split i (hK i)
      (simpleRoot_commutator_eq_bot_of_linear Q split i (μ i)) hkU
  have hs : k ∈ (simpleRemainder Q split short : Set (X ⧸ Q.D)) := hk short
  rw [radical_five_product Q split hm (1-short) short hij] at hs
  obtain ⟨edac,⟨eda,⟨ed,⟨e,he,d,hd,rfl⟩,a,ha,rfl⟩,c,hc,rfl⟩,b,hb,heq⟩ := hs
  let V := simpleRemainder Q split (1-short)
  have hMV := middleRoots_le_remainder Q split hm short (1-short) hij.symm
  have hdV : d ∈ V := (exchanged_roots_le_remainder Q split hm short (1-short) hij.symm).1 hd
  have haV : a ∈ V := hMV (mem_sup_right ha)
  have hcV : c ∈ V := hMV (mem_sup_left (mem_sup_right hc))
  have hbV : b ∈ V := hMV (mem_sup_left (mem_sup_left hb))
  have heV : e ∈ V := by
    have ht := V.mul_mem (hk (1-short)) (V.inv_mem (V.mul_mem (V.mul_mem (V.mul_mem hdV haV) hcV) hbV))
    rw [←heq] at ht
    simpa only [mul_assoc,mul_inv_rev,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ht
  have he1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split (1-short)) he heV
  change d ∈ positiveCarrier Q split short 3 at hd
  change a ∈ positiveCarrier Q split short 0 at ha
  change c ∈ positiveCarrier Q split short 2 at hc
  change b ∈ positiveCarrier Q split short 1 at hb
  rw [←alignedSourceRoots_range Q split hK μ n short 3] at hd
  rw [←alignedSourceRoots_range Q split hK μ n short 0] at ha
  rw [←alignedSourceRoots_range Q split hK μ n short 2] at hc
  rw [←alignedSourceRoots_range Q split hK μ n short 1] at hb
  obtain ⟨d,rfl⟩ := hd
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨c,rfl⟩ := hc
  obtain ⟨b,rfl⟩ := hb
  exact ⟨a.toAdd,b.toAdd,c.toAdd,d.toAdd,by simpa only [he1,one_mul,k,L,PositiveRoots.x,ofAdd_toAdd] using heq.symm⟩

include hK μ n in
/-- The rank-one cubics and characteristic two exclude simultaneous vanishing
of the two actual middle pairings, without a representation-type premise. -/
theorem not_both_middle_pairings_zero (hm : rotationOrder Q = 6)
    (hba : ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥) :
    ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥ := by
  intro hdc
  let L := alignedSourceRoots Q split hK μ n short
  let s : X ⧸ Q.D := (n short).val
  let r : X ⧸ Q.D := (n (1-short)).val
  let f := MulAut.conj (L.x 5 1)
  let w := MulAut.conj s
  let t := MulAut.conj (L.x 5 1*s)
  have hec := orthogonal_eq_bot_of_zero_pairings Q split hK μ hm short (n short) hba hdc
  have R : L.CommutingRelations := aligned_commuting_of_two Q split hK μ n short hm hba hec
  have hfc := (carrier_zero_pairing_transports Q split hm short hba hdc).2
  have commute_of (i j : Fin 6)
      (hz : ⁅positiveCarrier Q split short i,positiveCarrier Q split short j⁆ = ⊥) (a b : F) :
      Commute (L.x i a) (L.x j b) :=
    (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hz)
      (root_mem Q split hK μ n short i a)) _ (root_mem Q split hK μ n short j b)).symm
  have hFC (a : F) : f (L.x 2 a)=L.x 2 a := conjugation_fixes (commute_of 5 2 hfc 1 a)
  have hFA (a : F) : f (L.x 0 a)=L.x 0 a := conjugation_fixes (R.fa 1 a)
  have hFB (a : F) : f (L.x 1 a)=L.x 1 a := conjugation_fixes (R.fb 1 a)
  have hsA (a : F) : w (L.x 0 a)=L.x 0 a := sourceBorelWeyl_sA Q split hK μ n short split.abelian hm R a
  have hsB (a : F) : w (L.x 1 a)=L.x 4 a := sourceBorelWeyl_sB Q split hK μ n short split.abelian a
  have hsE (a : F) : w (L.x 4 a)=L.x 1 a := sourceBorelWeyl_sE Q split hK μ n short split.abelian a
  have hsC (a : F) : w (L.x 2 a)=L.x 3 a := sourceBorelWeyl_sC Q split hK μ n short split.abelian a
  have hsD (a : F) : w (L.x 3 a)=L.x 2 a := sourceBorelWeyl_sD Q split hK μ n short split.abelian a
  have hcube : (L.x 5 1*s)^3=1 := simple_cubic Q split hK μ n short
  have hrCube : (L.x 4 1*r)^3=1 := simple_cubic Q split hK μ n (1-short)
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  have hFD (d : F) (hf : Commute (L.x 5 1) (L.x 3 d)) : d=0 := by
    have he := cubic_fixed_partner (L.x 5 1) s (L.x 2 d) (L.x 3 d)
      (commute_of 5 2 hfc 1 d) hf (hsC d) (hsD d) hcube
    have h1 := disjoint_def.mp (exchanged_roots_disjoint Q split hm short (1-short) hij)
      (root_mem Q split hK μ n short 3 d) (he ▸ root_mem Q split hK μ n short 2 d)
    apply root_inj Q split hK μ n short 3
    simpa only [PositiveRoots.x_zero] using h1
  have hEB (b : F) (he : Commute (L.x 4 1) (L.x 1 b)) : b=0 := by
    have hEq := cubic_fixed_partner (L.x 4 1) r (L.x 0 b) (L.x 1 b)
      (R.ea 1 b) he
      (sourceBorelWeyl_rA Q split hK μ n short split.abelian b)
      (sourceBorelWeyl_rB Q split hK μ n short split.abelian b) hrCube
    have h1 := disjoint_def.mp (exchanged_roots_disjoint Q split hm (1-short) short hij.symm)
      (root_mem Q split hK μ n short 1 b) (hEq ▸ root_mem Q split hK μ n short 0 b)
    apply root_inj Q split hK μ n short 1
    simpa only [PositiveRoots.x_zero] using h1
  obtain ⟨a,b,c,d,hk⟩ := zero_pairings_simple_commutator_coordinates Q split hK μ n short hm
  change ⁅L.x 5 1,L.x 4 1⁆=L.x 3 d*L.x 0 a*L.x 2 c*L.x 1 b at hk
  have prod_inv (x y : X ⧸ Q.D) (hx : x⁻¹=x) (hy : y⁻¹=y) (hc : Commute x y) :
      (x*y)⁻¹=x*y := by rw [mul_inv_rev,hx,hy,hc.eq]
  have hinv (k : Fin 6) (v : F) : (L.x k v)⁻¹=L.x k v := by
    apply inv_eq_of_mul_eq_one_left
    rw [←L.x_add,CharTwo.add_self_eq_zero,L.x_zero]
  have hInv : ⁅L.x 5 1,L.x 4 1⁆⁻¹=⁅L.x 5 1,L.x 4 1⁆ := by
    rw [hk]
    exact prod_inv _ _
      (prod_inv _ _ (prod_inv _ _ (hinv 3 d) (hinv 0 a) (R.da d a)) (hinv 2 c)
        ((commute_of 3 2 hdc d c).mul_left (R.ca c a).symm))
      (hinv 1 b) (((show Commute (L.x 3 d) (L.x 1 b) from R.db d b).mul_left (R.ba b a).symm).mul_left (R.cb c b))
  obtain ⟨hfixF,hfixE⟩ := conjugate_commutator_fixed (L.x 5 1) (L.x 4 1)
    (hinv 5 1) (hinv 4 1) hInv
  have hd0 : d=0 := by
    apply hFD
    have hh : f (L.x 3 d)=L.x 3 d := by
      rw [hk,map_mul,map_mul,map_mul,hFA,hFC,hFB] at hfixF
      exact mul_right_cancel (mul_right_cancel (mul_right_cancel hfixF))
    exact (mul_inv_eq_iff_eq_mul.mp hh)
  have hb0 : b=0 := by
    apply hEB
    have hh : MulAut.conj (L.x 4 1) (L.x 1 b)=L.x 1 b := by
      rw [hk,hd0,L.x_zero,one_mul,map_mul,map_mul,
        conjugation_fixes (R.ea 1 a),conjugation_fixes (R.ec 1 c)] at hfixE
      exact mul_left_cancel hfixE
    exact (mul_inv_eq_iff_eq_mul.mp hh)
  have hFE : f (L.x 4 1)=L.x 0 a*L.x 2 c*L.x 4 1 := by
    have hh := congrArg (fun z : X ⧸ Q.D => z*L.x 4 1) hk
    simpa only [f,hd0,hb0,L.x_zero,one_mul,mul_one,commutatorElement_def,
      mul_assoc,inv_mul_cancel,MulAut.conj_apply] using hh
  have ht (x : X ⧸ Q.D) : t x=f (w x) := by
    change MulAut.conj (L.x 5 1*s) x=_
    rw [map_mul,MulAut.mul_apply]
  have hpow : (L.x 5 1*s)^2=(L.x 5 1*s)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [pow_succ] using hcube
  have hsInv : s⁻¹=s := inv_eq_of_mul_eq_one_right
    (sourceReflection_sq Q split short (hK short) (μ short) (n short))
  have he : L.x 0 a*f (L.x 3 c)*L.x 1 1=L.x 4 1 := by
    calc
      _ = t (t (L.x 1 1)) := by
        rw [ht (L.x 1 1),hsB,hFE,ht]
        simp only [map_mul,hsA,hsC,hsE,hFA,hFB]
      _ = MulAut.conj ((L.x 5 1*s)^2) (L.x 1 1) := by rw [pow_two,map_mul,MulAut.mul_apply]
      _ = MulAut.conj ((L.x 5 1*s)⁻¹) (L.x 1 1) := by rw [hpow]
      _ = L.x 4 1 := by
        rw [mul_inv_rev,hsInv,root_inv,map_mul,MulAut.mul_apply]
        change w (f (L.x 1 1))=_
        rw [hFB,hsB]
  let V := simpleRemainder Q split (1-short)
  have hMV := middleRoots_le_remainder Q split hm short (1-short) hij
  have hA : L.x 0 a ∈ V := hMV (mem_sup_right (root_mem Q split hK μ n short 0 a))
  have hB : L.x 1 1 ∈ V := hMV (mem_sup_left (mem_sup_left (root_mem Q split hK μ n short 1 1)))
  have hD : L.x 3 c ∈ V := (exchanged_roots_le_remainder Q split hm short (1-short) hij).1
    (root_mem Q split hK μ n short 3 c)
  have hF : L.x 5 1 ∈ V := simpleRoot_le_other_remainder Q split hm short (1-short) hij
    (root_mem Q split hK μ n short 5 1)
  have hEV : L.x 4 1 ∈ V := he ▸ V.mul_mem (V.mul_mem hA
    (V.mul_mem (V.mul_mem hF hD) (V.inv_mem hF))) hB
  have h1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split (1-short))
    (root_mem Q split hK μ n short 4 1) hEV
  exact one_ne_zero (root_inj Q split hK μ n short 4 (by simpa only [PositiveRoots.x_zero] using h1))


/-- Choose the source orientation of (9.2), before choosing field labels
for the mixed equation. Both possible endpoint indices are retained. -/
def sourceOrientation (hm : rotationOrder Q = 6) : Fin 2 :=
  (exists_orientation_opposite_pairing_zero Q split hK μ hm).choose

/-- The opposite pairing vanishes at the chosen orientation. -/
theorem sourceOrientation_opposite_zero (hm : rotationOrder Q = 6) :
    ⁅positiveCarrier Q split (sourceOrientation Q split hK μ hm) 1,
      positiveCarrier Q split (sourceOrientation Q split hK μ hm) 0⁆ = ⊥ :=
  (exists_orientation_opposite_pairing_zero Q split hK μ hm).choose_spec

include n in
/-- The selected pairing is nonzero by the genuine characteristic-two
exclusion, rather than by nonabelianness of the whole radical alone. -/
theorem sourceOrientation_middle_ne_bot (hm : rotationOrder Q = 6) :
    ⁅positiveCarrier Q split (sourceOrientation Q split hK μ hm) 3,
      positiveCarrier Q split (sourceOrientation Q split hK μ hm) 2⁆ ≠ ⊥ :=
  not_both_middle_pairings_zero Q split hK μ n (sourceOrientation Q split hK μ hm) hm
    (sourceOrientation_opposite_zero Q split hK μ hm)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
