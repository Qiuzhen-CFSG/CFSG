module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.UnitCoefficient
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.RootParameters

/-!
# Compatible whole pinnings for the middle source equation

The actual middle coefficient determines a field automorphism σ. Precompose
the entire long SL₂ pinning with its entrywise field action, leaving the short
pinning fixed. The long upper roots, diagonal torus, and all Weyl transports
therefore use the same new labels. The actual source reflection is unchanged,
and the long Borel and the full H ∩ R_long are retained.

The six transported maps have the original root ranges and generate exactly U.
Their highest root is nontrivial, and their DC equation is now precisely the
consumer's normalized ordered equation. All fields of characteristic two,
including q=2 and q=4, and either source orientation are covered.

CommonFieldApplication pulls these coordinates and DC through the existing
full-overlap Sylow equivalence, with both endpoint maps and literal Q.q.
Transport of these new whole pinnings through the previously proved complete
Borel--Weyl relation construction remains to be integrated. In particular,
normalizedSourceRoots is not claimed definitionally equal to alignedSourceRoots
for the original independently supplied local labels.

Source: Fong--Seitz II (9.13)--(9.14), printed pp.215--216. Relabeling is on
an entire rank-one group, not on an isolated root. The generic field-matrix
and root-relabeling helpers keep elaboration independent of the large source
quotient context.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2 Theory.PSL2.SemilinearCoverage
open scoped Pointwise MatrixGroups commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hm : rotationOrder Q = 6)
  (hne : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥)

omit [Finite F] [CharP F 2] in
private theorem field_torus (τ : F ≃+* F) (a : Fˣ) :
    sl2FieldAut τ (tor a)=tor (Units.mapEquiv τ.toMulEquiv a) := by
  ext i j
  change τ ((tor a).val i j)=(tor (Units.mapEquiv τ.toMulEquiv a)).val i j
  fin_cases i <;> fin_cases j <;> simp [tor]

omit [Finite F] [CharP F 2] in
private theorem field_borel (τ : F ≃+* F) (g : SL2 F) :
    sl2FieldAut τ g ∈ Borel F ↔ g ∈ Borel F := by
  rw [mem_Borel_iff,mem_Borel_iff]
  change τ (g.val 1 0)=0 ↔ g.val 1 0=0
  exact map_eq_zero_iff τ τ.injective

omit [Finite F] [CharP F 2] in
private theorem parameter_surjective (τ : F ≃+* F) :
    Function.Surjective τ.toRingHom.toAddMonoidHom.toMultiplicative := by
  intro a
  exact ⟨.ofAdd (τ.symm a.toAdd),congrArg Multiplicative.ofAdd (τ.apply_symm_apply _)⟩

omit [Finite F] [CharP F 2] in
private theorem parameter_injective (τ : F ≃+* F) :
    Function.Injective τ.toRingHom.toAddMonoidHom.toMultiplicative := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  exact τ.injective (congrArg Multiplicative.toAdd hab)

omit [Finite F] [CharP F 2] in
/-- Relabel every long-root coordinate by the same field automorphism. -/
def relabelLongRoots {Y : Type*} [Group Y] (R : PositiveRoots F Y) (τ : F ≃+* F) :
    PositiveRoots F Y where
  root := ![(R.root 0).comp τ.toRingHom.toAddMonoidHom.toMultiplicative,
    (R.root 1).comp τ.toRingHom.toAddMonoidHom.toMultiplicative,
    R.root 2,R.root 3,
    (R.root 4).comp τ.toRingHom.toAddMonoidHom.toMultiplicative,R.root 5]

omit [Finite F] [CharP F 2] in
private theorem relabelLongRoots_x {Y : Type*} [Group Y] (R : PositiveRoots F Y)
    (τ : F ≃+* F) (k : Fin 6) (a : F) :
    (relabelLongRoots R τ).x k a = if k=0 ∨ k=1 ∨ k=4 then R.x k (τ a) else R.x k a := by
  fin_cases k <;> simp [relabelLongRoots,PositiveRoots.x]

omit [Finite F] [CharP F 2] in
private theorem relabelLongRoots_range {Y : Type*} [Group Y] (R : PositiveRoots F Y)
    (τ : F ≃+* F) (k : Fin 6) : ((relabelLongRoots R τ).root k).range=(R.root k).range := by
  have hs : τ.toRingHom.toAddMonoidHom.toMultiplicative.range=⊤ :=
    MonoidHom.range_eq_top.mpr (parameter_surjective τ)
  have hh (j : Fin 6) : ((R.root j).comp τ.toRingHom.toAddMonoidHom.toMultiplicative).range =
      (R.root j).range := by rw [MonoidHom.range_comp,hs,←MonoidHom.range_eq_map]
  fin_cases k
  · exact hh 0
  · exact hh 1
  · rfl
  · rfl
  · exact hh 4
  · rfl

omit [Finite F] [CharP F 2] in
private theorem relabelLongRoots_injective {Y : Type*} [Group Y] (R : PositiveRoots F Y)
    (τ : F ≃+* F) (k : Fin 6) (hi : Function.Injective (R.root k)) :
    Function.Injective ((relabelLongRoots R τ).root k) := by
  have hh (j : Fin 6) (hj : Function.Injective (R.root j)) : Function.Injective
      ((R.root j).comp τ.toRingHom.toAddMonoidHom.toMultiplicative) :=
    hj.comp (parameter_injective τ)
  fin_cases k
  · exact hh 0 hi
  · exact hh 1 hi
  · exact hi
  · exact hi
  · exact hh 4 hi
  · exact hi

/-- The field comparison is constructed from the actual source pairing. -/
def sourceFieldEquiv : F ≃+* F :=
  (exists_middleCoefficient_ringEquiv Q split hK μ n short hm hne).choose

theorem sourceFieldEquiv_spec (d c : F) :
    middleCoefficient Q split hK μ n short hm d c =
      sourceFieldEquiv Q split hK μ n short hm hne (d*c) :=
  (exists_middleCoefficient_ringEquiv Q split hK μ n short hm hne).choose_spec d c

local notation "σ" => sourceFieldEquiv Q split hK μ n short hm hne
local notation "L" => alignedSourceRoots Q split hK μ n short

/-- Change the entire long SL₂ pinning by the constructed field automorphism. -/
def normalizedLongPinning : SL2 F ≃* rankOne Q split (1-short) :=
  (sl2FieldAut σ).trans (alignedPinning Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)))

def normalizedLongPinningHom : SL2 F →* X ⧸ Q.D :=
  (alignedPinningHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))).comp
    (sl2FieldAut σ).toMonoidHom

@[simp] theorem normalizedLongPinning_coe (g : SL2 F) :
    (normalizedLongPinning Q split hK μ n short hm hne g : X ⧸ Q.D) =
      normalizedLongPinningHom Q split hK μ n short hm hne g := rfl

theorem normalizedLongPinningHom_injective :
    Function.Injective (normalizedLongPinningHom Q split hK μ n short hm hne) :=
  (alignedPinningHom_injective Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))).comp
    (sl2FieldAut σ).injective

theorem normalizedLongPinningHom_range :
    (normalizedLongPinningHom Q split hK μ n short hm hne).range = rankOne Q split (1-short) := by
  have hs : (sl2FieldAut σ).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (sl2FieldAut σ).surjective
  rw [normalizedLongPinningHom,MonoidHom.range_comp,hs,←MonoidHom.range_eq_map,
    alignedPinningHom_range]

@[simp] theorem normalizedLongPinningHom_weyl :
    normalizedLongPinningHom Q split hK μ n short hm hne (weyl F) = (n (1-short)).val := by
  rw [normalizedLongPinningHom,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    sl2FieldAut_weyl,alignedPinningHom_weyl]

/-- The diagonal parameters change by the same field automorphism as the root. -/
theorem normalizedLongPinningHom_torus (a : Fˣ) :
    normalizedLongPinningHom Q split hK μ n short hm hne (tor a) =
      alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
        (Units.mapEquiv (σ).toMulEquiv a) := by
  change alignedPinningHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
    (sl2FieldAut σ (tor a)) = alignedPinningHom Q split (1-short) (hK (1-short))
      (μ (1-short)) (n (1-short)) (tor (Units.mapEquiv (σ).toMulEquiv a))
  exact congrArg (alignedPinningHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)))
    (field_torus σ a)

/-- The whole rank-one Borel is preserved by the change of field labels. -/
theorem normalizedLongPinningHom_borel_iff (g : SL2 F) :
    normalizedLongPinningHom Q split hK μ n short hm hne g ∈ Q.tits.B ↔ g ∈ Borel F := by
  rw [normalizedLongPinningHom,MonoidHom.comp_apply,alignedPinningHom_mem_borel_iff]
  exact field_borel σ g

/-- The full long Cartan uses the same relabeled pinning. -/
def normalizedLongTorusHom : Fˣ →* X ⧸ Q.D :=
  (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))).comp
    (Units.mapEquiv (σ).toMulEquiv).toMonoidHom

theorem normalizedLongTorusHom_pinning (a : Fˣ) :
    normalizedLongTorusHom Q split hK μ n short hm hne a =
      normalizedLongPinningHom Q split hK μ n short hm hne (tor a) :=
  (normalizedLongPinningHom_torus Q split hK μ n short hm hne a).symm

/-- Relabeling preserves the entire original H ∩ R_long. -/
theorem normalizedLongTorusHom_range :
    (normalizedLongTorusHom Q split hK μ n short hm hne).range =
      (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split (1-short) := by
  have hs : (Units.mapEquiv (σ).toMulEquiv).toMonoidHom.range=⊤ :=
    MonoidHom.range_eq_top.mpr (Units.mapEquiv (σ).toMulEquiv).surjective
  rw [normalizedLongTorusHom,MonoidHom.range_comp,hs,←MonoidHom.range_eq_map,
    alignedTorusHom_range]

/-- The six maps use the unchanged whole short pinning and the new whole long pinning. -/
def normalizedSourceRoots : PositiveRoots F (X ⧸ Q.D) := relabelLongRoots L σ

theorem normalizedSourceRoots_x (k : Fin 6) (a : F) :
    (normalizedSourceRoots Q split hK μ n short hm hne).x k a =
      if k=0 ∨ k=1 ∨ k=4 then (L).x k (σ a) else (L).x k a :=
  relabelLongRoots_x L σ k a

theorem normalizedSourceRoots_range (k : Fin 6) :
    ((normalizedSourceRoots Q split hK μ n short hm hne).root k).range =
      positiveCarrier Q split short k := by
  change ((relabelLongRoots L σ).root k).range = _
  rw [relabelLongRoots_range]
  exact alignedSourceRoots_range Q split hK μ n short k

theorem normalizedSourceRoots_injective (k : Fin 6) :
    Function.Injective ((normalizedSourceRoots Q split hK μ n short hm hne).root k) :=
  relabelLongRoots_injective L σ k (alignedSourceRoots_injective Q split hK μ n short k)

/-- The new coordinates still generate the literal source unipotent group. -/
theorem normalizedSourceRoots_generated :
    (normalizedSourceRoots Q split hK μ n short hm hne).generated = split.U :=
  positive_generated_of_ranges Q split hm short _
    (normalizedSourceRoots_range Q split hK μ n short hm hne)

/-- The long simple root is the upper root of the whole relabeled pinning. -/
theorem normalizedSourceRoots_long_root (a : F) :
    normalizedLongPinningHom Q split hK μ n short hm hne (uni a) =
      (normalizedSourceRoots Q split hK μ n short hm hne).x 4 a := by
  rw [normalizedLongPinningHom,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,sl2FieldAut_uni]
  rfl

/-- The short simple root keeps its original whole pinning. -/
theorem normalizedSourceRoots_short_root (a : F) :
    alignedPinningHom Q split short (hK short) (μ short) (n short) (uni a) =
      (normalizedSourceRoots Q split hK μ n short hm hne).x 5 a := rfl

/-- The highest-root map uses the same two source Weyl lifts and the new long pinning. -/
theorem normalizedSourceRoots_highest_transport (a : F) :
    (normalizedSourceRoots Q split hK μ n short hm hne).x 0 a =
      MulAut.conj (((n short).val : X ⧸ Q.D)*(n (1-short)).val)⁻¹
        (normalizedLongPinningHom Q split hK μ n short hm hne (uni a)) := by
  rw [normalizedSourceRoots_long_root]
  rfl

theorem normalizedSourceRoots_highest_nontrivial :
    (normalizedSourceRoots Q split hK μ n short hm hne).x 0 1 ≠ 1 := by
  simpa only [normalizedSourceRoots_x,ite_true,true_or,Fin.reduceEq,map_one] using
    alignedSourceRoots_highest_nontrivial Q split hK μ n short

/-- The field automorphism is applied to all long-root labels, so DC is now
normalized with the actual whole rank-one pinnings. -/
theorem normalizedSourceRoots_dc (d c : F) :
    (normalizedSourceRoots Q split hK μ n short hm hne).x 3 d *
      (normalizedSourceRoots Q split hK μ n short hm hne).x 2 c =
        (normalizedSourceRoots Q split hK μ n short hm hne).x 0 (c*d) *
          (normalizedSourceRoots Q split hK μ n short hm hne).x 2 c *
            (normalizedSourceRoots Q split hK μ n short hm hne).x 3 d := by
  change (L).x 3 d*(L).x 2 c = (L).x 0 (σ (c*d))*(L).x 2 c*(L).x 3 d
  have hh := middleCoefficient_spec Q split hK μ n short hm d c
  rw [sourceFieldEquiv_spec Q split hK μ n short hm hne,mul_comm d c] at hh
  rw [←hh]
  simp only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
