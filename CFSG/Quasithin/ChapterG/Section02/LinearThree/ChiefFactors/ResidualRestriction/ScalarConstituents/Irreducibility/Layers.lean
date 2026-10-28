module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Irreducibility.SourceFlags

/-!
# Individual constituents in the original marked upper and lower layers

The original MarkedLayers equivalences, with the prescribed basis change,
identify the full scalar kernels and the literal quotients. Their actions
are restrictions and quotients of ambient conjugation. Every individual
copy has an injective, equivariant embedding, binary irreducibility,
noncentrality and its expected order. The upper scalar kernel is exactly
the original marked image of W in S/S₃. Zero multiplicities are allowed.

The earlier-source hypotheses remain precisely `MarkedLayers`, including
its relative normality, coordinate and marking premises. Their construction
belongs to the source-theorem assembly owner; no chief count is inferred.
Source: Aschbacher–Smith, G.2.5(6–8), printed pp.335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Irreducibility
open Matrix.PSL3.LinearThree
variable (F : Type*) [Field F]

def tailCopies (k : ℕ) : (Fin k → Fin 3 → F) →ₗ[F] (Fin k → Fin 2 → F) where
  toFun v i := tail F (v i)
  map_add' v w := by ext i j; exact congrFun ((tail F).map_add (v i) (w i)) j
  map_smul' a v := by ext i j; exact congrFun ((tail F).map_smul a (v i)) j

def headCopies (k : ℕ) : (Fin k → Fin 3 → F) →ₗ[F] (Fin k → F) where
  toFun v i := head F (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tailCopies_surjective (k : ℕ) : Function.Surjective (tailCopies F k) := by
  intro v
  refine ⟨fun i => planeVector F (v i), ?_⟩
  ext i j; fin_cases j <;> rfl

theorem headCopies_surjective (k : ℕ) : Function.Surjective (headCopies F k) :=
  fun v => ⟨fun i => lineVector F (v i), rfl⟩

def lineCopiesEquiv (k : ℕ) : (tailCopies F k).ker ≃ₗ[F] (Fin k → F) where
  toFun v i := v.val i 0
  invFun v := ⟨fun i => lineVector F (v i), by ext i j; fin_cases j <;> rfl⟩
  left_inv v := by
    apply Subtype.ext
    ext i j
    have hv : v.val i ∈ naturalLine F := congrFun v.property i
    have h := (mem_naturalLine F _).mp hv
    fin_cases j <;> simp [lineVector, h.1, h.2]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def planeCopiesEquiv (k : ℕ) : (headCopies F k).ker ≃ₗ[F] (Fin k → Fin 2 → F) where
  toFun v i := tail F (v.val i)
  invFun v := ⟨fun i => planeVector F (v i), rfl⟩
  left_inv v := by
    apply Subtype.ext
    ext i j
    have hv : v.val i 0 = 0 := congrFun v.property i
    fin_cases j <;> simp [planeVector, tail, hv]
  right_inv v := by ext i j; fin_cases j <;> rfl
  map_add' v w := by ext i j; exact congrFun ((tail F).map_add (v.val i) (w.val i)) j
  map_smul' a v := by ext i j; exact congrFun ((tail F).map_smul a (v.val i)) j

/-- A specified individual copy inside an actual marked product, including its embedding. -/
def copyEmbedding {M V : Type*} [Group M] [AddCommGroup V] {k : ℕ}
    (e : M ≃* Multiplicative (Fin k → V)) (i : Fin k) : Multiplicative V →* M where
  toFun v := e.symm (Multiplicative.ofAdd (fun j => if j = i then v.toAdd else 0))
  map_one' := by simp; rfl
  map_mul' v w := by
    apply e.injective
    simp only [e.apply_symm_apply, map_mul]
    apply Multiplicative.toAdd.injective
    funext j
    change (if j = i then v.toAdd + w.toAdd else 0) =
      (if j = i then v.toAdd else 0) + (if j = i then w.toAdd else 0)
    split <;> simp_all

theorem copyEmbedding_injective {M V : Type*} [Group M] [AddCommGroup V] {k : ℕ}
    (e : M ≃* Multiplicative (Fin k → V)) (i : Fin k) :
    Function.Injective (copyEmbedding e i) := by
  intro v w h
  apply Multiplicative.toAdd.injective
  have hh := congrArg (fun q => (e q).toAdd i) h
  simpa [copyEmbedding] using hh

/-- The range of a marked copy has exactly the cardinality of that constituent. -/
theorem copyEmbedding_card {M V : Type*} [Group M] [AddCommGroup V] {k : ℕ}
    (e : M ≃* Multiplicative (Fin k → V)) (i : Fin k) :
    Nat.card (copyEmbedding e i).range = Nat.card V :=
  (Nat.card_congr (MonoidHom.ofInjective (copyEmbedding_injective e i)).toEquiv).symm

/-- Reading back the action on an embedded individual source copy. -/
def copyAction {A M V : Type*} [Group M] [AddCommGroup V] {k : ℕ}
    (e : M ≃* Multiplicative (Fin k → V)) (act : A → M → M) (i : Fin k)
    (x : A) (v : V) : V :=
  (e (act x (copyEmbedding e i (Multiplicative.ofAdd v)))).toAdd i

/-- Coordinatewise action preserves each actual embedded copy. -/
theorem copyEmbedding_equivariant {A M V : Type*} [Group M] [AddCommGroup V] {k : ℕ}
    (e : M ≃* Multiplicative (Fin k → V)) (act : A → M → M) (ρ : A → V → V)
    (he : ∀ x v j, (e (act x v)).toAdd j = ρ x ((e v).toAdd j))
    (hz : ∀ x, ρ x 0 = 0) (i : Fin k) (x : A) (v : V) :
    act x (copyEmbedding e i (Multiplicative.ofAdd v)) =
      copyEmbedding e i (Multiplicative.ofAdd (ρ x v)) := by
  apply e.injective
  apply Multiplicative.toAdd.injective
  funext j
  rw [he]
  simp only [copyEmbedding, MonoidHom.coe_mk, OneHom.coe_mk, e.apply_symm_apply]
  by_cases hj : j = i
  · subst j; simp
  · simp [hj, hz]

variable {F} [Finite F] {G : Type*} [Group G] [Finite G] {D : Setup G}
  {n : ℕ} {g h : G} {d : Hypothesis D F n g h} (a : PointAlignment d)
  {hLI : D.L ≤ I D g h} {r s : ℕ}
  [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal]
  (c : MarkedLayers d hLI r s)

/-- All r natural source copies after the same determinant-one alignment. -/
def upperCoordinates : UpperQuotient D g h ≃* Multiplicative (Fin r → Fin 3 → F) :=
  c.upper.trans (LinearEquiv.piCongrRight fun _ : Fin r =>
    SpecialLinearGroup.toLin' a.basis⁻¹).toAddEquiv.toMultiplicative

/-- All s dual source copies; the basis change is the genuine transpose. -/
def lowerCoordinates : LowerQuotient D g h ≃* Multiplicative (Fin s → Fin 3 → F) :=
  c.lower.trans (LinearEquiv.piCongrRight fun _ : Fin s =>
    SpecialLinearGroup.toLin' a.basis.transpose).toAddEquiv.toMultiplicative

@[simp] theorem upperCoordinates_apply (v : UpperQuotient D g h) (i : Fin r) :
    (upperCoordinates a c v).toAdd i = alignedUpper a c v i := rfl

@[simp] theorem lowerCoordinates_apply (v : LowerQuotient D g h) (i : Fin s) :
    (lowerCoordinates a c v).toAdd i = alignedLower a c v i := rfl

def upperProjection : UpperQuotient D g h →* Multiplicative (Fin r → Fin 2 → F) :=
  (tailCopies F r).toAddMonoidHom.toMultiplicative.comp (upperCoordinates a c).toMonoidHom

def lowerProjection : LowerQuotient D g h →* Multiplicative (Fin s → F) :=
  (headCopies F s).toAddMonoidHom.toMultiplicative.comp (lowerCoordinates a c).toMonoidHom

theorem upperProjection_surjective : Function.Surjective (upperProjection a c) :=
  (tailCopies_surjective F r).comp (upperCoordinates a c).surjective

theorem lowerProjection_surjective : Function.Surjective (lowerProjection a c) :=
  (headCopies_surjective F s).comp (lowerCoordinates a c).surjective

/-- All scalar lines in the upper layer; no multiplicity is required to be positive. -/
def upperKernelEquiv : (upperProjection a c).ker ≃* Multiplicative (Fin r → F) :=
  (markedKernelCoordinates (upperCoordinates a c) (tailCopies F r)).trans
    (lineCopiesEquiv F r).toAddEquiv.toMultiplicative

/-- All annihilator planes in the lower layer. -/
def lowerKernelEquiv : (lowerProjection a c).ker ≃* Multiplicative (Fin s → Fin 2 → F) :=
  (markedKernelCoordinates (lowerCoordinates a c) (headCopies F s)).trans
    (planeCopiesEquiv F s).toAddEquiv.toMultiplicative

noncomputable def upperQuotientEquiv :
    (UpperQuotient D g h ⧸ (upperProjection a c).ker) ≃* Multiplicative (Fin r → Fin 2 → F) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (upperProjection_surjective a c)

noncomputable def lowerQuotientEquiv :
    (LowerQuotient D g h ⧸ (lowerProjection a c).ker) ≃* Multiplicative (Fin s → F) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (lowerProjection_surjective a c)

@[simp] theorem upperQuotientEquiv_mk (v : UpperQuotient D g h) :
    upperQuotientEquiv a c (QuotientGroup.mk' (upperProjection a c).ker v) =
      upperProjection a c v := rfl

@[simp] theorem lowerQuotientEquiv_mk (v : LowerQuotient D g h) :
    lowerQuotientEquiv a c (QuotientGroup.mk' (lowerProjection a c).ker v) =
      lowerProjection a c v := rfl

/-- The actual natural source-layer action in aligned coordinates. -/
def upperLayerAction (hn : 1 < n) (l : D.L₁) (v : UpperQuotient D g h) : UpperQuotient D g h :=
  (upperCoordinates a c).symm (Multiplicative.ofAdd
    (fun i => (localProjection a hn l).val.val *ᵥ (upperCoordinates a c v).toAdd i))

/-- The actual contragredient source-layer action in aligned coordinates. -/
def lowerLayerAction (hn : 1 < n) (l : D.L₁) (v : LowerQuotient D g h) : LowerQuotient D g h :=
  (lowerCoordinates a c).symm (Multiplicative.ofAdd
    (fun i => (localProjection a hn l).val⁻¹.val.transpose *ᵥ (lowerCoordinates a c v).toAdd i))

theorem upperLayerAction_mk (hn : 1 < n) (l : D.L₁) (v : S D g h) :
    upperLayerAction a c hn l (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) v) =
    QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (I_normalizes_core D g h
          (hLI (((map_subtype_le _).trans inf_le_left) l.property))) v).mp v.property⟩ := by
  apply (upperCoordinates a c).injective
  apply Multiplicative.toAdd.injective
  funext i
  exact (congrFun (congrArg Multiplicative.toAdd
    ((upperCoordinates a c).apply_symm_apply _)) i).trans (upper_action a c hn l v i).symm

theorem lowerLayerAction_mk (hn : 1 < n) (l : D.L₁) (v : S₃ D g h) :
    lowerLayerAction a c hn l (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) v) =
    QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h))
      ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (c.lower_normalizes
          (((map_subtype_le _).trans inf_le_left) l.property)) v).mp v.property⟩ := by
  apply (lowerCoordinates a c).injective
  apply Multiplicative.toAdd.injective
  funext i
  exact (congrFun (congrArg Multiplicative.toAdd
    ((lowerCoordinates a c).apply_symm_apply _)) i).trans (lower_action a c hn l v i).symm

def upperKernelAction (hn : 1 < n) (l : D.L₁) (v : (upperProjection a c).ker) :
    (upperProjection a c).ker :=
  (upperKernelEquiv a c).symm (Multiplicative.ofAdd
    (fun i => scalarAction F (localProjection a hn l) ((upperKernelEquiv a c v).toAdd i)))

def lowerKernelAction (hn : 1 < n) (l : D.L₁) (v : (lowerProjection a c).ker) :
    (lowerProjection a c).ker :=
  (lowerKernelEquiv a c).symm (Multiplicative.ofAdd
    (fun i => dualBlockAction F (localProjection a hn l) ((lowerKernelEquiv a c v).toAdd i)))

/-- The computed scalar action is the restriction of original conjugation. -/
theorem upperKernelAction_val (hn : 1 < n) (l : D.L₁) (v : (upperProjection a c).ker) :
    (upperKernelAction a c hn l v).val = upperLayerAction a c hn l v.val := by
  apply (upperCoordinates a c).injective
  apply Multiplicative.toAdd.injective
  have hleft := congrArg (fun q => (upperCoordinates a c q.val).toAdd)
    ((upperKernelEquiv a c).symm_apply_apply v)
  change (upperCoordinates a c ((upperCoordinates a c).symm _)).toAdd = _ at hleft
  rw [(upperCoordinates a c).apply_symm_apply] at hleft
  change (fun i => lineVector F ((upperCoordinates a c v.val).toAdd i 0)) = _ at hleft
  change (upperCoordinates a c ((upperCoordinates a c).symm _)).toAdd = _
  rw [(upperCoordinates a c).apply_symm_apply]
  change _ = (upperCoordinates a c ((upperCoordinates a c).symm _)).toAdd
  rw [(upperCoordinates a c).apply_symm_apply]
  funext i
  change lineVector F ((scalar F _ : F) * (upperCoordinates a c v.val).toAdd i 0) = _
  rw [← natural_line_action, congrFun hleft i]
  rfl

theorem lowerKernelAction_val (hn : 1 < n) (l : D.L₁) (v : (lowerProjection a c).ker) :
    (lowerKernelAction a c hn l v).val = lowerLayerAction a c hn l v.val := by
  apply (lowerCoordinates a c).injective
  apply Multiplicative.toAdd.injective
  have hleft := congrArg (fun q => (lowerCoordinates a c q.val).toAdd)
    ((lowerKernelEquiv a c).symm_apply_apply v)
  change (lowerCoordinates a c ((lowerCoordinates a c).symm _)).toAdd = _ at hleft
  rw [(lowerCoordinates a c).apply_symm_apply] at hleft
  change (fun i => planeVector F (tail F ((lowerCoordinates a c v.val).toAdd i))) = _ at hleft
  change (lowerCoordinates a c ((lowerCoordinates a c).symm _)).toAdd = _
  rw [(lowerCoordinates a c).apply_symm_apply]
  change _ = (lowerCoordinates a c ((lowerCoordinates a c).symm _)).toAdd
  rw [(lowerCoordinates a c).apply_symm_apply]
  funext i
  change planeVector F ((block F _⁻¹ : Matrix (Fin 2) (Fin 2) F).transpose *ᵥ
    tail F ((lowerCoordinates a c v.val).toAdd i)) = _
  rw [← dual_plane_action, congrFun hleft i]
  rfl

noncomputable def upperQuotientAction (hn : 1 < n) (l : D.L₁)
    (v : UpperQuotient D g h ⧸ (upperProjection a c).ker) :
    UpperQuotient D g h ⧸ (upperProjection a c).ker :=
  (upperQuotientEquiv a c).symm (Multiplicative.ofAdd
    (fun i => blockAction F (localProjection a hn l) ((upperQuotientEquiv a c v).toAdd i)))

noncomputable def lowerQuotientAction (hn : 1 < n) (l : D.L₁)
    (v : LowerQuotient D g h ⧸ (lowerProjection a c).ker) :
    LowerQuotient D g h ⧸ (lowerProjection a c).ker :=
  (lowerQuotientEquiv a c).symm (Multiplicative.ofAdd
    (fun i => inverseScalarAction F (localProjection a hn l) ((lowerQuotientEquiv a c v).toAdd i)))

theorem upperQuotientAction_mk (hn : 1 < n) (l : D.L₁) (v : UpperQuotient D g h) :
    upperQuotientAction a c hn l (QuotientGroup.mk' (upperProjection a c).ker v) =
      QuotientGroup.mk' (upperProjection a c).ker (upperLayerAction a c hn l v) := by
  apply (upperQuotientEquiv a c).injective
  apply Multiplicative.toAdd.injective
  change (upperQuotientEquiv a c ((upperQuotientEquiv a c).symm _)).toAdd = _
  rw [(upperQuotientEquiv a c).apply_symm_apply]
  simp only [upperQuotientEquiv_mk]
  funext i
  change blockAction F (localProjection a hn l) (tail F ((upperCoordinates a c v).toAdd i)) =
    tail F ((upperCoordinates a c (upperLayerAction a c hn l v)).toAdd i)
  unfold upperLayerAction
  rw [(upperCoordinates a c).apply_symm_apply]
  exact (natural_quotient_action F _ _).symm

theorem lowerQuotientAction_mk (hn : 1 < n) (l : D.L₁) (v : LowerQuotient D g h) :
    lowerQuotientAction a c hn l (QuotientGroup.mk' (lowerProjection a c).ker v) =
      QuotientGroup.mk' (lowerProjection a c).ker (lowerLayerAction a c hn l v) := by
  apply (lowerQuotientEquiv a c).injective
  apply Multiplicative.toAdd.injective
  change (lowerQuotientEquiv a c ((lowerQuotientEquiv a c).symm _)).toAdd = _
  rw [(lowerQuotientEquiv a c).apply_symm_apply]
  simp only [lowerQuotientEquiv_mk]
  funext i
  change inverseScalarAction F (localProjection a hn l) (head F ((lowerCoordinates a c v).toAdd i)) =
    head F ((lowerCoordinates a c (lowerLayerAction a c hn l v)).toAdd i)
  unfold lowerLayerAction
  rw [(lowerCoordinates a c).apply_symm_apply]
  exact (dual_quotient_action F _ _).symm

theorem upperKernelEquiv_action (hn : 1 < n) (l : D.L₁) (v : (upperProjection a c).ker)
    (i : Fin r) :
    (upperKernelEquiv a c (upperKernelAction a c hn l v)).toAdd i =
      scalarAction F (localProjection a hn l) ((upperKernelEquiv a c v).toAdd i) :=
  congrFun (congrArg Multiplicative.toAdd ((upperKernelEquiv a c).apply_symm_apply _)) i

theorem lowerKernelEquiv_action (hn : 1 < n) (l : D.L₁) (v : (lowerProjection a c).ker)
    (i : Fin s) :
    (lowerKernelEquiv a c (lowerKernelAction a c hn l v)).toAdd i =
      dualBlockAction F (localProjection a hn l) ((lowerKernelEquiv a c v).toAdd i) :=
  congrFun (congrArg Multiplicative.toAdd ((lowerKernelEquiv a c).apply_symm_apply _)) i

theorem upperQuotientEquiv_action (hn : 1 < n) (l : D.L₁)
    (v : UpperQuotient D g h ⧸ (upperProjection a c).ker) (i : Fin r) :
    (upperQuotientEquiv a c (upperQuotientAction a c hn l v)).toAdd i =
      blockAction F (localProjection a hn l) ((upperQuotientEquiv a c v).toAdd i) :=
  congrFun (congrArg Multiplicative.toAdd ((upperQuotientEquiv a c).apply_symm_apply _)) i

theorem lowerQuotientEquiv_action (hn : 1 < n) (l : D.L₁)
    (v : LowerQuotient D g h ⧸ (lowerProjection a c).ker) (i : Fin s) :
    (lowerQuotientEquiv a c (lowerQuotientAction a c hn l v)).toAdd i =
      inverseScalarAction F (localProjection a hn l) ((lowerQuotientEquiv a c v).toAdd i) :=
  congrFun (congrArg Multiplicative.toAdd ((lowerQuotientEquiv a c).apply_symm_apply _)) i

theorem upperScalarCopyAction_eq (hn : 1 < n) (i : Fin r) :
    copyAction (upperKernelEquiv a c) (upperKernelAction a c hn) i =
      fun l => scalarAction F (localProjection a hn l) := by
  funext l z
  rw [copyAction, upperKernelEquiv_action]
  simp [copyEmbedding]

theorem upperPlaneCopyAction_eq (hn : 1 < n) (i : Fin r) :
    copyAction (upperQuotientEquiv a c) (upperQuotientAction a c hn) i =
      fun l => blockAction F (localProjection a hn l) := by
  funext l z
  rw [copyAction, upperQuotientEquiv_action]
  simp [copyEmbedding]

theorem lowerPlaneCopyAction_eq (hn : 1 < n) (i : Fin s) :
    copyAction (lowerKernelEquiv a c) (lowerKernelAction a c hn) i =
      fun l => dualBlockAction F (localProjection a hn l) := by
  funext l z
  rw [copyAction, lowerKernelEquiv_action]
  simp [copyEmbedding]

theorem lowerScalarCopyAction_eq (hn : 1 < n) (i : Fin s) :
    copyAction (lowerQuotientEquiv a c) (lowerQuotientAction a c hn) i =
      fun l => inverseScalarAction F (localProjection a hn l) := by
  funext l z
  rw [copyAction, lowerQuotientEquiv_action]
  simp [copyEmbedding]

/-- Each individual copy is invariant inside the literal upper kernel. -/
theorem upperScalarCopy_equivariant (hn : 1 < n) (i : Fin r) (l : D.L₁) (v : F) :
    upperKernelAction a c hn l (copyEmbedding (upperKernelEquiv a c) i (Multiplicative.ofAdd v)) =
      copyEmbedding (upperKernelEquiv a c) i
        (Multiplicative.ofAdd (scalarAction F (localProjection a hn l) v)) :=
  copyEmbedding_equivariant _ _ _ (upperKernelEquiv_action a c hn)
    (fun _ => mul_zero _) i l v

theorem upperPlaneCopy_equivariant (hn : 1 < n) (i : Fin r) (l : D.L₁) (v : Fin 2 → F) :
    upperQuotientAction a c hn l (copyEmbedding (upperQuotientEquiv a c) i (Multiplicative.ofAdd v)) =
      copyEmbedding (upperQuotientEquiv a c) i
        (Multiplicative.ofAdd (blockAction F (localProjection a hn l) v)) :=
  copyEmbedding_equivariant _ _ _ (upperQuotientEquiv_action a c hn)
    (fun _ => mulVec_zero _) i l v

theorem lowerPlaneCopy_equivariant (hn : 1 < n) (i : Fin s) (l : D.L₁) (v : Fin 2 → F) :
    lowerKernelAction a c hn l (copyEmbedding (lowerKernelEquiv a c) i (Multiplicative.ofAdd v)) =
      copyEmbedding (lowerKernelEquiv a c) i
        (Multiplicative.ofAdd (dualBlockAction F (localProjection a hn l) v)) :=
  copyEmbedding_equivariant _ _ _ (lowerKernelEquiv_action a c hn)
    (fun _ => mulVec_zero _) i l v

theorem lowerScalarCopy_equivariant (hn : 1 < n) (i : Fin s) (l : D.L₁) (v : F) :
    lowerQuotientAction a c hn l (copyEmbedding (lowerQuotientEquiv a c) i (Multiplicative.ofAdd v)) =
      copyEmbedding (lowerQuotientEquiv a c) i
        (Multiplicative.ofAdd (inverseScalarAction F (localProjection a hn l) v)) :=
  copyEmbedding_equivariant _ _ _ (lowerQuotientEquiv_action a c hn)
    (fun _ => mul_zero _) i l v

/-- Binary irreducibility on each embedded copy of the original marked layers.
The full earlier-source MarkedLayers premises remain explicit. -/
theorem layer_constituents_irreducible (hn : 1 < n) :
    (∀ i : Fin r, AdditivelyIrreducible
      (copyAction (upperKernelEquiv a c) (upperKernelAction a c hn) i)) ∧
    (∀ i : Fin r, AdditivelyIrreducible
      (copyAction (upperQuotientEquiv a c) (upperQuotientAction a c hn) i)) ∧
    (∀ i : Fin s, AdditivelyIrreducible
      (copyAction (lowerKernelEquiv a c) (lowerKernelAction a c hn) i)) ∧
    (∀ i : Fin s, AdditivelyIrreducible
      (copyAction (lowerQuotientEquiv a c) (lowerQuotientAction a c hn) i)) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [upperScalarCopyAction_eq]
    exact scalar_irreducible F _ (localProjection_surjective a hn)
  · rw [upperPlaneCopyAction_eq]
    exact block_irreducible F _ (localProjection_surjective a hn)
  · rw [lowerPlaneCopyAction_eq]
    exact dualBlock_irreducible F _ (localProjection_surjective a hn)
  · rw [lowerScalarCopyAction_eq]
    exact inverseScalar_irreducible F _ (localProjection_surjective a hn)

theorem layer_constituents_noncentral (hn : 1 < n) :
    (∀ i : Fin r, Noncentral
      (copyAction (upperKernelEquiv a c) (upperKernelAction a c hn) i)) ∧
    (∀ i : Fin r, Noncentral
      (copyAction (upperQuotientEquiv a c) (upperQuotientAction a c hn) i)) ∧
    (∀ i : Fin s, Noncentral
      (copyAction (lowerKernelEquiv a c) (lowerKernelAction a c hn) i)) ∧
    (∀ i : Fin s, Noncentral
      (copyAction (lowerQuotientEquiv a c) (lowerQuotientAction a c hn) i)) := by
  have hc : 2 < Nat.card F := by
    rw [d.field_card]
    have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hs := scalar_noncentral F _ (localProjection_surjective a hn) hc
  have hp := plane_actions_noncentral F _ (localProjection_surjective a hn)
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [upperScalarCopyAction_eq]; exact hs.1
  · rw [upperPlaneCopyAction_eq]; exact hp.1
  · rw [lowerPlaneCopyAction_eq]; exact hp.2
  · rw [lowerScalarCopyAction_eq]; exact hs.2

/-- The upper scalar kernel is the image of the original marked W in S/S₃.
This uses the actual upper marking from the earlier source clause (7). -/
theorem upperProjection_kernel_marked :
    (upperProjection a c).ker = upperImage D g h (W D g h) := by
  have hp (v : Fin 3 → F) : a.basis⁻¹.val *ᵥ v ∈ naturalLine F ↔ v ∈ d.point := by
    change a.basis⁻¹ • v ∈ naturalLine F ↔ v ∈ (d.point : Set (Fin 3 → F))
    rw [a.point_eq]
    constructor
    · intro hv
      exact ⟨a.basis⁻¹ • v, (mem_naturalLine F _).mp hv, smul_inv_smul _ _⟩
    · rintro ⟨w,hw,rfl⟩
      rw [inv_smul_smul]
      exact (mem_naturalLine F _).mpr hw
  ext q
  have hm : q ∈ upperImage D g h (W D g h) ↔
      c.upper q ∈ ChiefFactors.lineCopies d.point r := by
    rw [← c.upper_mark]
    exact (Subgroup.mem_map_iff_mem c.upper.injective).symm
  rw [hm]
  change (fun i => tail F (a.basis⁻¹.val *ᵥ (c.upper q).toAdd i)) = 0 ↔
    ∀ i, (c.upper q).toAdd i ∈ d.point
  constructor
  · intro hq i
    exact (hp _).mp (congrFun hq i)
  · intro hq
    funext i
    exact (hp _).mpr (hq i)

/-- Orders of the actual embedded constituents in both original source layers. -/
theorem layer_constituents_card :
    (∀ i : Fin r, Nat.card (copyEmbedding (upperKernelEquiv a c) i).range = 2 ^ n) ∧
    (∀ i : Fin r, Nat.card (copyEmbedding (upperQuotientEquiv a c) i).range = 2 ^ (2*n)) ∧
    (∀ i : Fin s, Nat.card (copyEmbedding (lowerKernelEquiv a c) i).range = 2 ^ (2*n)) ∧
    (∀ i : Fin s, Nat.card (copyEmbedding (lowerQuotientEquiv a c) i).range = 2 ^ n) := by
  have hp : Nat.card (Fin 2 → F) = 2 ^ (2*n) := by
    rw [Nat.card_fun, Nat.card_fin, d.field_card, ← pow_mul, Nat.mul_comm n 2]
  exact ⟨fun _ => (copyEmbedding_card _ _).trans d.field_card,
    fun _ => (copyEmbedding_card _ _).trans hp,
    fun _ => (copyEmbedding_card _ _).trans hp,
    fun _ => (copyEmbedding_card _ _).trans d.field_card⟩

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Irreducibility
