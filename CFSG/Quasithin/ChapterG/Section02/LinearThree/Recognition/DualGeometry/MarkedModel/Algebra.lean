module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.Coordinates
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.Coordinates

/-!
# Direct sums of the three dual marks

Coordinatewise copies preserve the marked direct decomposition. Consequently
three subgroups spanning the homogeneous model and contained in its three
marked summands equal those summands. No positivity of the multiplicity is used.

Source: Aschbacher–Smith, G.2.5(6,8), printed pp.335–336.
-/
@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.MarkedModel
open Subgroup Matrix

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-- Tuples with every entry in the specified subspace, as a multiplicative subgroup. -/
def copies (P : Submodule F V) (s : ℕ) : Subgroup (Multiplicative (Fin s → V)) where
  carrier := {v | ∀ i, v.toAdd i ∈ P}
  one_mem' := fun _ => P.zero_mem
  mul_mem' hv hw i := P.add_mem (hv i) (hw i)
  inv_mem' hv i := P.neg_mem (hv i)

theorem copies_sup (P Q : Submodule F V) (s : ℕ) :
    copies (P ⊔ Q) s = copies P s ⊔ copies Q s := by
  apply le_antisymm
  · intro v hv
    have he (i : Fin s) := Submodule.mem_sup.mp (hv i)
    choose a ha b hb hab using he
    exact Subgroup.mem_sup.mpr ⟨Multiplicative.ofAdd a, ha,
      Multiplicative.ofAdd b, hb, congrArg Multiplicative.ofAdd (funext hab)⟩
  · exact sup_le (fun _ hv i => (show P ≤ P ⊔ Q from le_sup_left) (hv i))
      (fun _ hv i => (show Q ≤ P ⊔ Q from le_sup_right) (hv i))

theorem copies_disjoint {P Q : Submodule F V} (h : Disjoint P Q) (s : ℕ) :
    Disjoint (copies P s) (copies Q s) := by
  apply Subgroup.disjoint_def.mpr
  intro v hv hw
  apply Multiplicative.toAdd.injective
  exact funext (fun i => Submodule.disjoint_def.mp h _ (hv i) (hw i))

private theorem pair_eq {M : Type*} [CommGroup M] {A B P Q : Subgroup M}
    (hA : A ≤ P) (hB : B ≤ Q) (hspan : A ⊔ B = P ⊔ Q) (hdis : Disjoint P Q) :
    A = P ∧ B = Q := by
  constructor
  · apply eq_of_le_of_inf_le_of_le_sup hA (z := Q)
    · rw [hdis.eq_bot]; exact bot_le
    · exact le_sup_left.trans (hspan.ge.trans (sup_le_sup_left hB _))
  · apply eq_of_le_of_inf_le_of_le_sup hB (z := P)
    · rw [hdis.symm.eq_bot]; exact bot_le
    · have he : B ⊔ A = Q ⊔ P := by simpa only [sup_comm] using hspan
      exact le_sup_left.trans (he.ge.trans (sup_le_sup_left hA _))

/-- Containment and spanning identify each of the three literal summands. -/
theorem three_eq_of_span {M : Type*} [CommGroup M] {A B C : Subgroup M}
    {P Q R : Submodule F V} {s : ℕ}
    (e : M ≃* Multiplicative (Fin s → V))
    (hspan : (A ⊔ B) ⊔ C = ⊤)
    (hPQ : Disjoint P Q) (hR : IsCompl (P ⊔ Q) R)
    (hA : A.map e.toMonoidHom ≤ copies P s)
    (hB : B.map e.toMonoidHom ≤ copies Q s)
    (hC : C.map e.toMonoidHom ≤ copies R s) :
    A.map e.toMonoidHom = copies P s ∧
    B.map e.toMonoidHom = copies Q s ∧
    C.map e.toMonoidHom = copies R s := by
  have hs : (A.map e.toMonoidHom ⊔ B.map e.toMonoidHom) ⊔ C.map e.toMonoidHom =
      (copies P s ⊔ copies Q s) ⊔ copies R s := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, hspan,
      Subgroup.map_top_of_surjective _ e.surjective, ← copies_sup, ← copies_sup,
      hR.codisjoint.eq_top]
    ext v
    simp [copies]
  have hd : Disjoint (copies P s ⊔ copies Q s) (copies R s) := by
    rw [← copies_sup]
    exact copies_disjoint hR.disjoint s
  obtain ⟨hab, hc⟩ := pair_eq (sup_le_sup hA hB) hC hs hd
  obtain ⟨ha, hb⟩ := pair_eq hA hB hab (copies_disjoint hPQ s)
  exact ⟨ha, hb, hc⟩

/-- The genuine dot-product dual coordinates, applied in each copy. -/
def dotCoordinates (s : ℕ) : (Fin s → Module.Dual F (Fin 3 → F)) ≃ₗ[F]
    (Fin s → Fin 3 → F) :=
  LinearEquiv.piCongrRight (fun _ => (dotProductEquiv F (Fin 3)).symm)

/-- The annihilator line in ordinary vector coordinates. -/
def coordinateLine (P : Submodule F (Module.Dual F (Fin 3 → F))) :
    Submodule F (Fin 3 → F) := P.map (dotProductEquiv F (Fin 3)).symm.toLinearMap

theorem coordinateLine_dimension (P : Submodule F (Module.Dual F (Fin 3 → F))) :
    Module.finrank F (coordinateLine P) = Module.finrank F P :=
  (dotProductEquiv F (Fin 3)).symm.finrank_map_eq P

theorem copies_map_dotCoordinates (P : Submodule F (Module.Dual F (Fin 3 → F))) (s : ℕ) :
    (copies P s).map (dotCoordinates (F := F) s).toAddEquiv.toMultiplicative.toMonoidHom =
      ChiefFactors.lineCopies (coordinateLine P) s := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    exact Submodule.mem_map_of_mem (hw i)
  · intro hv
    refine ⟨Multiplicative.ofAdd ((dotCoordinates (F := F) s).symm v.toAdd), ?_, ?_⟩
    · intro i
      obtain ⟨f, hf, he⟩ := hv i
      change (dotProductEquiv F (Fin 3)) (v.toAdd i) ∈ P
      change (dotProductEquiv F (Fin 3)).symm f = v.toAdd i at he
      rw [← he, LinearEquiv.apply_symm_apply]
      exact hf
    · exact congrArg Multiplicative.ofAdd ((dotCoordinates (F := F) s).apply_symm_apply v.toAdd)

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.MarkedModel
