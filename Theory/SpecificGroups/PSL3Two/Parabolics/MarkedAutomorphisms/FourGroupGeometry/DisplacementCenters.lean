module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.FourGroupGeometry
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.FourGroupCoverage
/-!
# Four-groups determined by their displacement centers

On the natural three-space plus its literal contragredient dual, the common
nonidentity displacement image of the point four-group is its pure natural
line. The two marked translations give the upper bound; every nonidentity
point translation displaces onto that line.

A nonzero vector of this line can be displaced by a square-one matrix only
when that matrix belongs to the point four-group. The corresponding pure dual
vector detects the line four-group. Thus the existing two-class coverage and
conjugation transport prove that the displacement center determines every
four-group. We compare row coordinates with the literal dual by the dot
product, using inverse matrices and the square-one hypothesis explicitly.

The finite certificates test individual matrices and the four explicit line
translations. The intersection of displacement images is retained throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56(3–5), 15.3.58(3), and the proof of 15.3.59, printed pp.1147–1150.
-/

public section

namespace Matrix.PSL3Two.MarkedAutomorphisms.FourGroupGeometry
open Matrix Subgroup BinaryLinearThree
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

private def displacement (g : SL) (v : Vector × Vector) : Vector × Vector :=
  (g.val *ᵥ v.1 - v.1, v.2 ᵥ* g.val - v.2)

private def coordinates : (Vector × Vector) ≃ₗ[ZMod 2] NaturalDual :=
  (LinearEquiv.refl (ZMod 2) Vector).prodCongr (dotProductEquiv (ZMod 2) (Fin 3))

private lemma dual_coordinates (g : SL) (d : Vector) :
    W.dual g (dotProductEquiv (ZMod 2) (Fin 3) d) =
      dotProductEquiv (ZMod 2) (Fin 3) (d ᵥ* g⁻¹.val) := by
  apply LinearMap.ext
  intro w
  change d ⬝ᵥ (g⁻¹.val *ᵥ w) = (d ᵥ* g⁻¹.val) ⬝ᵥ w
  rw [Matrix.dotProduct_mulVec]

private lemma action_displacement (g : SL) (hg : g ^ 2 = 1) (v : Vector × Vector) :
    modelAction g (Multiplicative.ofAdd (coordinates v)) *
      (Multiplicative.ofAdd (coordinates v))⁻¹ =
        Multiplicative.ofAdd (coordinates (displacement g v)) := by
  have hi : g⁻¹ = g := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hg)
  change Multiplicative.ofAdd ((W.prod W.dual) g (coordinates v) + -(coordinates v)) = _
  rw [← sub_eq_add_neg]
  apply congrArg Multiplicative.ofAdd
  change (W g v.1 - v.1, W.dual g (dotProductEquiv (ZMod 2) (Fin 3) v.2) -
    dotProductEquiv (ZMod 2) (Fin 3) v.2) = _
  rw [dual_coordinates, hi, ← map_sub]
  rfl

private noncomputable def actionAut (g : SL) : MulAut (Multiplicative NaturalDual) :=
  AddEquiv.toMultiplicative
    { toFun := (W.prod W.dual) g
      invFun := (W.prod W.dual) g⁻¹
      left_inv := (W.prod W.dual).inv_self_apply g
      right_inv := (W.prod W.dual).self_inv_apply g
      map_add' := ((W.prod W.dual) g).map_add }

private noncomputable def actionHom : SL →* MulAut (Multiplicative NaturalDual) where
  toFun := actionAut
  map_one' := by
    apply MulEquiv.ext
    intro w
    change (W.prod W.dual) 1 w.toAdd = w.toAdd
    rw [map_one, Module.End.one_apply]
  map_mul' g h := by
    apply MulEquiv.ext
    intro w
    apply congrArg Multiplicative.ofAdd
    exact congrArg (fun f : Module.End (ZMod 2) NaturalDual => f w.toAdd)
      ((W.prod W.dual).map_mul g h)

private theorem center_conj (E : Subgroup SL) (g : SL) (w : Multiplicative NaturalDual) :
    modelAction g w ∈ modelCenter (E.map (MulAut.conj g).toMonoidHom) ↔
      w ∈ modelCenter E :=
  commonDisplacement_conj actionHom E g w

private def lineParam : Fin 4 → SL :=
  ![Bruhat.upper 0, Bruhat.upper 2, Bruhat.upper 4, Bruhat.upper 6]

private theorem line_detection : ∀ g : SL, g ^ 2 = 1 →
    (∃ v : Vector, v ᵥ* g.val - v = ![0,0,1]) → ∃ i : Fin 4, lineParam i = g := by
  decide +kernel

private theorem lineParam_mem : ∀ i, lineParam i ∈ lineV := by decide +kernel
private theorem lineParam_injective : Function.Injective lineParam := by decide +kernel
private theorem line_displacement_nonzero : ∀ i : Fin 4, lineParam i ≠ 1 →
    ∃ v : Vector, v ᵥ* (lineParam i).val - v = ![0,0,1] := by decide +kernel

private theorem point_displacement_intersection (v u : Vector × Vector)
    (h : displacement (Bruhat.upper 1) v = displacement (Bruhat.upper 2) u) :
    ∃ c : ZMod 2, displacement (Bruhat.upper 1) v = (c • ![1,0,0], 0) := by
  have ht := congrArg (fun p : Vector × Vector => p.2 1) h
  simp [displacement, Bruhat.upper, dotProduct, Fin.sum_univ_three, vecHead, vecTail] at ht
  refine ⟨v.1 1, ?_⟩
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [displacement, Bruhat.upper, dotProduct, Fin.sum_univ_three, vecHead, vecTail, ht]

private theorem point_detection : ∀ g : SL, g ^ 2 = 1 →
    (∃ v : Vector, g.val *ᵥ v - v = ![1,0,0]) → g ∈ pointV := by
  decide +kernel

private theorem point_exists : ∀ g : SL, g ∈ pointV → g ≠ 1 → ∀ c : ZMod 2,
    ∃ v : Vector, g.val *ᵥ v - v = c • ![1,0,0] := by
  decide +kernel

private theorem exists_lineParam (g : SL) (hg : g ∈ lineV) :
    ∃ i, lineParam i = g := by
  let f : Fin 4 → lineV := fun i => ⟨lineParam i, lineParam_mem i⟩
  have hi : Function.Injective f := fun i j h => lineParam_injective (congrArg Subtype.val h)
  have hc : Nat.card (Fin 4) = Nat.card lineV := by
    rw [BinaryLinearThree.FourGroupGeometry.Normalizers.card_lineV]
    simp
  obtain ⟨i, hi⟩ := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi, hc⟩).2 ⟨g, hg⟩
  exact ⟨i, congrArg Subtype.val hi⟩

private theorem line_square (g : SL) (hg : g ∈ lineV) : g ^ 2 = 1 := by
  apply diagram.injective
  rw [map_pow, map_one]
  exact pointV_square (diagram g) hg

private theorem exists_coordinates (w : Multiplicative NaturalDual) :
    ∃ v : Vector × Vector, Multiplicative.ofAdd (coordinates v) = w := by
  obtain ⟨v, hv⟩ := coordinates.surjective w.toAdd
  exact ⟨v, congrArg Multiplicative.ofAdd hv⟩

private theorem displacement_exists_iff (g : SL) (hg : g ^ 2 = 1)
    (w : Vector × Vector) :
    (∃ v, modelAction g v * v⁻¹ = Multiplicative.ofAdd (coordinates w)) ↔
      ∃ v, displacement g v = w := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨u, rfl⟩ := exists_coordinates v
    rw [action_displacement g hg u] at hv
    exact ⟨u, coordinates.injective (congrArg Multiplicative.toAdd hv)⟩
  · rintro ⟨v, hv⟩
    exact ⟨Multiplicative.ofAdd (coordinates v), by rw [action_displacement g hg, hv]⟩

private theorem point_center_coordinates (w : Vector × Vector) :
    Multiplicative.ofAdd (coordinates w) ∈ pointCenter ↔
      ∃ c : ZMod 2, w = (c • ![1,0,0], 0) := by
  change (∃ c : ZMod 2, coordinates w = (c • ![1,0,0], 0)) ↔ _
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, coordinates.injective ?_⟩
    simpa [coordinates] using hc
  · rintro ⟨c, rfl⟩
    exact ⟨c, by simp [coordinates]⟩

private theorem point_generators :
    (Bruhat.upper 1 ∈ pointV ∧ Bruhat.upper 1 ≠ 1) ∧
      (Bruhat.upper 2 ∈ pointV ∧ Bruhat.upper 2 ≠ 1) := by decide +kernel

/-- The common displacement image of the point four-group is the pure natural line. -/
theorem modelCenter_pointV : modelCenter pointV = pointCenter := by
  ext w
  obtain ⟨w, rfl⟩ := exists_coordinates w
  rw [point_center_coordinates]
  constructor
  · intro hw
    obtain ⟨v, hv⟩ := (displacement_exists_iff _
      (pointV_square _ point_generators.1.1) w).mp
      (hw _ point_generators.1.1 point_generators.1.2)
    obtain ⟨u, hu⟩ := (displacement_exists_iff _
      (pointV_square _ point_generators.2.1) w).mp
      (hw _ point_generators.2.1 point_generators.2.2)
    obtain ⟨c, hc⟩ := point_displacement_intersection v u (hv.trans hu.symm)
    exact ⟨c, hv.symm.trans hc⟩
  · rintro ⟨c, rfl⟩ g hg hne
    apply (displacement_exists_iff g (pointV_square g hg) _).mpr
    obtain ⟨v, hv⟩ := point_exists g hg hne c
    refine ⟨(v, 0), ?_⟩
    apply Prod.ext
    · exact hv
    · simp [displacement]

private theorem line_witness :
    Multiplicative.ofAdd (coordinates (0, ![0,0,1])) ∈ modelCenter lineV := by
  intro g hg hne
  apply (displacement_exists_iff g (line_square g hg) _).mpr
  obtain ⟨i, rfl⟩ := exists_lineParam g hg
  obtain ⟨v, hv⟩ := line_displacement_nonzero i hne
  refine ⟨(0, v), ?_⟩
  apply Prod.ext
  · simp [displacement]
  · exact hv

private theorem eq_point_of_center (E : Subgroup SL)
    (hE : ∀ g ∈ E, g ^ 2 = 1) (hcE : Nat.card E = 4)
    (he : modelCenter E = modelCenter pointV) : E = pointV := by
  apply eq_of_le_of_card_ge _ (by rw [hcE, card_pointV])
  intro g hg
  by_cases hne : g = 1
  · exact hne ▸ pointV.one_mem
  have hw : Multiplicative.ofAdd (coordinates (![1,0,0], 0)) ∈ modelCenter E := by
    rw [he, modelCenter_pointV, point_center_coordinates]
    exact ⟨1, by simp⟩
  obtain ⟨v, hv⟩ := (displacement_exists_iff g (hE g hg) _).mp (hw g hg hne)
  exact point_detection g (hE g hg) ⟨v.1, congrArg Prod.fst hv⟩

private theorem eq_line_of_center (E : Subgroup SL)
    (hE : ∀ g ∈ E, g ^ 2 = 1) (hcE : Nat.card E = 4)
    (he : modelCenter E = modelCenter lineV) : E = lineV := by
  apply eq_of_le_of_card_ge _
    (by rw [hcE, BinaryLinearThree.FourGroupGeometry.Normalizers.card_lineV])
  intro g hg
  have hw : Multiplicative.ofAdd (coordinates (0, ![0,0,1])) ∈ modelCenter E := by
    rw [he]
    exact line_witness
  by_cases hne : g = 1
  · exact hne ▸ lineV.one_mem
  obtain ⟨v, hv⟩ := (displacement_exists_iff g (hE g hg) _).mp (hw g hg hne)
  obtain ⟨i, rfl⟩ := line_detection g (hE g hg) ⟨v.2, congrArg Prod.snd hv⟩
  exact lineParam_mem i

private theorem elementary_of_square (E : Subgroup SL)
    (hE : ∀ g ∈ E, g ^ 2 = 1) : IsElementaryAbelian 2 E := by
  have h (g : E) : g ^ 2 = 1 := Subtype.ext (hE g g.property)
  exact { toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (h x)) a b).eq⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h }

/-- The actual displacement intersection determines a square-one subgroup of order four. -/
theorem modelCenter_injective_four (E F : Subgroup SL)
    (hE : ∀ g ∈ E, g ^ 2 = 1) (hcE : Nat.card E = 4)
    (hF : ∀ g ∈ F, g ^ 2 = 1) (hcF : Nat.card F = 4)
    (he : modelCenter E = modelCenter F) : E = F := by
  let : IsElementaryAbelian 2 E := elementary_of_square E hE
  obtain ⟨g, hg⟩ := BinaryLinearThree.FourGroupGeometry.Normalizers.fourGroup_coverage E hcE
  have hf : ∀ x ∈ F.map (MulAut.conj g).toMonoidHom, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hF x hx, map_one]
  have hc : Nat.card (F.map (MulAut.conj g).toMonoidHom) = 4 :=
    (Nat.card_congr ((MulAut.conj g).subgroupMap F).toEquiv).symm.trans hcF
  have he' : modelCenter (F.map (MulAut.conj g).toMonoidHom) =
      modelCenter (E.map (MulAut.conj g).toMonoidHom) := by
    ext w
    obtain ⟨v, rfl⟩ := (actionAut g).surjective w
    change modelAction g v ∈ modelCenter _ ↔ modelAction g v ∈ modelCenter _
    rw [center_conj, center_conj, he]
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective
  rcases hg with hg | hg
  · rw [hg] at he' ⊢
    exact (eq_point_of_center _ hf hc he').symm
  · rw [hg] at he' ⊢
    exact (eq_line_of_center _ hf hc he').symm

end Matrix.PSL3Two.MarkedAutomorphisms.FourGroupGeometry
