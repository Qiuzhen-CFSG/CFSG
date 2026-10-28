module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.ReflectionPinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi

/-!
# The exact Cartan factors of the reflection-aligned source pinnings

The existing opposite-Levi factorization traps R_i ∩ B ∩ B^{s_i} in
H = B ∩ N. An element of the matrix Borel normalizes both the simple root
and the actual panel radical, hence normalizes U and belongs to B. Applying
this to a diagonal matrix and its Weyl conjugate proves the reverse Cartan
containment left open by ReflectionPinning. Thus the unit group maps
isomorphically onto the literal H ∩ R_i, including over F₂ and F₄.

The same specified source reflection inverts this Cartan factor, which is
normal in the full H. The field maps of different rank-one groups have not
been aligned with each other, and this does not prove that the full H is
abelian or establish any mixed root relation.

Source: Fong--Seitz II §7 and (7A), printed p.192. The underlying
opposite-Levi theorem is the earlier rank-one geometry of I (5C).
The consumers are BorelWeylPinning and the literal CartanApplication.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,F)) (n : RootReflection Q split i)

theorem alignedPinningHom_mem_borel_iff (g : SL2 F) :
    alignedPinningHom Q split i hV μ n g ∈ Q.tits.B ↔ g ∈ Borel F := by
  constructor
  · intro hg
    obtain ⟨a,ha,h,hh,he⟩ := UnitarySource.rootActor_borel_factorization Q split i
      (show alignedPinningHom Q split i hV μ n g ∈ rankOne Q split i from
        alignedPinningHom_range Q split i hV μ n ▸ ⟨g,rfl⟩) hg
    apply (alignedPinningHom_borel_iff Q split i hV μ n g).mp
    rw [he]
    exact (normalizer (simpleRoot Q split i : Set (X ⧸ Q.D))).mul_mem
      ((simpleRoot Q split i).le_normalizer ha) (torus_normalizes_simpleRoot Q split i hh.2)
  · intro hg
    have hR : alignedPinningHom Q split i hV μ n g ∈ rankOne Q split i :=
      alignedPinningHom_range Q split i hV μ n ▸ ⟨g,rfl⟩
    have hN := normalizer_inf_normalizer_le_normalizer_sup
      (simpleRoot Q split i) (simpleRemainder Q split i)
      ⟨(alignedPinningHom_borel_iff Q split i hV μ n g).mpr hg,
        remainder_parabolic_normalizes Q split i hV (rankOne_le_parabolic Q split i hR)⟩
    have hs : simpleRoot Q split i ⊔ simpleRemainder Q split i = split.U := by
      apply le_antisymm (sup_le (simpleRoot_le Q split i) inf_le_left)
      intro x hx
      have hx' : x ∈ (simpleRoot Q split i : Set (X ⧸ Q.D)) *
          (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
        rw [simpleRoot_mul_remainder]; exact hx
      obtain ⟨a,ha,v,hv,rfl⟩ := hx'
      exact mul_mem (mem_sup_left ha) (mem_sup_right hv)
    rwa [hs, split.normalizer_eq] at hN

theorem alignedTorus_mem_cartan (a : Fˣ) :
    alignedTorus Q split i hV μ n a ∈ Q.tits.B ⊓ Q.tits.N := by
  apply UnitarySource.oppositeLevi_inf_two_borels_le_torus Q split i
  refine ⟨UnitarySource.rootActor_le_oppositeLevi Q split i ?_, ?_, ?_⟩
  · change alignedPinningHom Q split i hV μ n (tor a) ∈ rankOne Q split i
    rw [← alignedPinningHom_range Q split i hV μ n]
    exact ⟨tor a,rfl⟩
  · exact (alignedPinningHom_mem_borel_iff Q split i hV μ n (tor a)).mpr
      ((mem_Borel_iff _).mpr rfl)
  · rw [borelConjugate_eq _ n.val n.class_eq]
    change (n.val : X ⧸ Q.D) * alignedPinningHom Q split i hV μ n (tor a) *
      (n.val : X ⧸ Q.D)⁻¹ ∈ Q.tits.B
    rw [← alignedPinningHom_weyl Q split i hV μ n, ← map_inv, ← map_mul, ← map_mul,
      alignedPinningHom_mem_borel_iff]
    have hinv : (weyl F)⁻¹ = weyl F := inv_eq_of_mul_eq_one_right weyl_sq
    rw [hinv, mem_Borel_iff]
    simp [Matrix.mul_apply,Fin.sum_univ_two]


/-- The coroot uses the same entire reflection-aligned pinning. -/
def alignedTorusHom : Fˣ →* X ⧸ Q.D :=
  (alignedPinningHom Q split i hV μ n).comp (BenderSuzuki.Converse.torHom F)

@[simp] theorem alignedTorusHom_apply (a : Fˣ) :
    alignedTorusHom Q split i hV μ n a = alignedTorus Q split i hV μ n a := rfl

theorem alignedTorusHom_injective : Function.Injective (alignedTorusHom Q split i hV μ n) :=
  (alignedPinningHom_injective Q split i hV μ n).comp BenderSuzuki.Converse.torHom_injective

/-- Its range is exactly the source H_i, in the original full Cartan. -/
theorem alignedTorusHom_range :
    (alignedTorusHom Q split i hV μ n).range =
      (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i := by
  apply le_antisymm
  · rintro x ⟨a,rfl⟩
    refine ⟨alignedTorus_mem_cartan Q split i hV μ n a, ?_⟩
    rw [← alignedPinningHom_range Q split i hV μ n]
    exact ⟨tor a,rfl⟩
  · intro x hx
    exact exists_alignedTorus_of_mem Q split i hV μ n hx.1 hx.2

/-- The parameter unit group is the actual Cartan intersection, not an abstract tag. -/
def alignedCartanEquiv : Fˣ ≃* ↥((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i) :=
  (MonoidHom.ofInjective (alignedTorusHom_injective Q split i hV μ n)).trans
    (MulEquiv.subgroupCongr (alignedTorusHom_range Q split i hV μ n))

@[simp] theorem alignedCartanEquiv_coe (a : Fˣ) :
    (alignedCartanEquiv Q split i hV μ n a : X ⧸ Q.D) =
      alignedTorus Q split i hV μ n a := rfl

include hV μ n in
theorem rankOne_cartan_card :
    Nat.card ↥((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i) = Nat.card F - 1 := by
  rw [← Nat.card_congr (alignedCartanEquiv Q split i hV μ n).toEquiv, Nat.card_units]

/-- The specified reflection inverts its own actual Cartan factor. -/
theorem reflection_alignedTorus (a : Fˣ) :
    (n.val : X ⧸ Q.D) * alignedTorus Q split i hV μ n a * (n.val : X ⧸ Q.D)⁻¹ =
      alignedTorus Q split i hV μ n a⁻¹ := by
  have hw : weyl F * tor a * (weyl F)⁻¹ = tor a⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right weyl_sq]
    ext j k
    fin_cases j <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  simpa only [map_mul, map_inv, alignedPinningHom_weyl, alignedTorus] using
    congrArg (alignedPinningHom Q split i hV μ n) hw

/-- H_i is normal in the same full H, as in Fong--Seitz II (7A). -/
theorem cartan_normalizes_alignedTorus :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer ((alignedTorusHom Q split i hV μ n).range : Set _) := by
  rw [alignedTorusHom_range]
  exact (le_inf (Q.tits.B ⊓ Q.tits.N).le_normalizer (rankOne_torus_normalizes Q split i)).trans
    inf_normalizer_le_normalizer_inf

/-- The matrix Borel is the actual intersection R_i ∩ B. -/
theorem alignedPinningHom_borel_map :
    (Borel F).map (alignedPinningHom Q split i hV μ n) = rankOne Q split i ⊓ Q.tits.B := by
  ext x
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨alignedPinningHom_range Q split i hV μ n ▸ ⟨g,rfl⟩,
      (alignedPinningHom_mem_borel_iff Q split i hV μ n g).mpr hg⟩
  · intro hx
    obtain ⟨g,hg⟩ := (alignedPinningHom_range Q split i hV μ n).symm ▸ hx.1
    exact ⟨g, (alignedPinningHom_mem_borel_iff Q split i hV μ n g).mp (hg.symm ▸ hx.2), hg⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
