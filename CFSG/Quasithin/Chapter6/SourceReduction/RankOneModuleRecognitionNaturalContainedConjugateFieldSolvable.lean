module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFixedSpacesLines
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosure
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.SemilinearLineSolvability
public import Theory.GroupTheory.NormalizerActionSolvability

/-!
# Solvability of the central-line normalizer action

The natural SL₂ marking makes every common normalizer of L and its layer
semilinear. The Sylow fixed subgroup Z_S becomes a one-dimensional subspace
over the matrix field. Trivial intersection of the M-conjugates of the
layer puts N_M(Z_S) in its normalizer, so the actual action on Z_S restricts
the marked semilinear action. Its field-automorphism quotient and scalar
kernel are solvable.

This proves the solvability premise in the last paragraph of source
6.1.14(5), without the contained-centralizer or global-rank hypotheses.
Source: Aschbacher--Smith, printed pp.669 and 671--672.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces
universe u
variable {G : Type u} [Group G] {L B Z M : Subgroup G}
  {F : Type} [Field F] [Finite F] [CharP F 2]
local instance fieldSolvableAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

private def lineCoordinates (f : B ≃* Multiplicative (Fin 2 → F))
    (hZB : Z ≤ B) (X : Submodule F (Fin 2 → F))
    (hX : X.toAddSubgroup = coordinateSpace f Z) : Z ≃* Multiplicative X where
  toFun z := Multiplicative.ofAdd ⟨(f ⟨z,hZB z.property⟩).toAdd, by
    change (f ⟨z,hZB z.property⟩).toAdd ∈ X.toAddSubgroup
    rw [hX]
    simp⟩
  invFun v := ⟨f.symm (Multiplicative.ofAdd v.toAdd.val), by
    exact (show v.toAdd.val ∈ coordinateSpace f Z from hX ▸ v.toAdd.property)⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv v := by apply Multiplicative.toAdd.injective; apply Subtype.ext; simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (f (⟨a,hZB a.property⟩ * ⟨b,hZB b.property⟩)).toAdd = _
    rw [map_mul]
    rfl

/-- Common normalizers act solvably on an invariant natural field line. -/
theorem natural_line_normalizerAction_solvable
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : B ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (l : L) (v : B),
      (f.symm (Multiplicative.ofAdd
        ((e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (f v).toAdd)) : G) =
        (l : G) * (v : G) * (l : G)⁻¹)
    (hNL : M ⊓ normalizer (Z : Set G) ≤ normalizer (L : Set G))
    (hNB : M ⊓ normalizer (Z : Set G) ≤ normalizer (B : Set G))
    (hZB : Z ≤ B) (X : Submodule F (Fin 2 → F)) (hd : Module.finrank F X = 1)
    (hX : X.toAddSubgroup = coordinateSpace f Z) :
    Group.IsSolvable (normalizerAction M Z).range := by
  let j := lineCoordinates f hZB X hX
  let ρ : (normalizerAction M Z).range →* Multiplicative (AddAut X) :=
    (MulAutMultiplicative X).toMonoidHom.comp
      ((MulAut.congr j).toMonoidHom.comp (normalizerAction M Z).range.subtype)
  have hinj : Function.Injective ρ :=
    (MulAutMultiplicative X).injective.comp
      ((MulAut.congr j).injective.comp Subtype.val_injective)
  apply Representation.isSolvable_of_semilinear_line ρ hinj hd
  rintro ⟨a,t,rfl⟩
  let tL : normalizer (L : Set G) := ⟨t,hNL t.property⟩
  let tB : normalizer (B : Set G) := ⟨t,hNB t.property⟩
  obtain ⟨σ,hσ⟩ :=
    Representation.OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
      (Representation.specialLinearNatural 2 (k := F))
      (fun k hk => Representation.SL2NaturalOffenders.centralizer_scalar k hk)
      (quotientActor e tL) (vectorActor f tB)
      (vectorActor_intertwines e f hf tL (hNB t.property))
  have he (v : X) :
      ((ρ ⟨normalizerAction M Z t, ⟨t,rfl⟩⟩).toAdd v : Fin 2 → F) =
        vectorActor f tB v := rfl
  refine ⟨σ,fun c v => ?_⟩
  apply Subtype.ext
  change ((ρ ⟨normalizerAction M Z t, ⟨t,rfl⟩⟩).toAdd (c • v) : Fin 2 → F) =
    σ c • ((ρ ⟨normalizerAction M Z t, ⟨t,rfl⟩⟩).toAdd v : Fin 2 → F)
  rw [he,he]
  exact hσ c v

variable [Finite G] {κ : GroupClass.{u}} {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The literal action Aut_M(Z_S) in the final paragraph of 6.1.14 is solvable. -/
theorem natural_ZS_normalizerAction_solvable (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    Group.IsSolvable (normalizerAction M (ZS (T : Subgroup G) L V)).range := by
  have hzcard := (hnatural.sylow_intersection_geometry T h.sylow_normalizes_L).1
  have hZne : ZS (T : Subgroup G) L V ≠ ⊥ := by
    intro he
    change Nat.card (ZS (T : Subgroup G) L V) = 2 ^ n at hzcard
    rw [he,card_bot] at hzcard
    have hn := h.n_gt_one
    have hh : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
    omega
  have hNB : M ⊓ normalizer (ZS (T : Subgroup G) L V : Set G) ≤
      normalizer (layer L V : Set G) :=
    inf_normalizer_le_of_trivial_intersections
      (fun g hg => natural_layer_ti h hnatural hg) hZne inf_le_left
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnatural
  let X := sylowSpace (T : Subgroup G) e
  have hX : X.toAddSubgroup = coordinateSpace f (ZS (T : Subgroup G) L V) :=
    AddSubgroup.ext (mem_sylowSpace_iff (T : Subgroup G) e f hf)
  have hc : Nat.card X = Nat.card F := by
    change Nat.card X.toAddSubgroup = Nat.card F
    rw [hX,coordinateSpace_card f
      (show ZS (T : Subgroup G) L V ≤ layer L V from inf_le_left),hF]
    exact hzcard
  have hd : Module.finrank F X = 1 := by
    apply Nat.pow_right_injective (Finite.one_lt_card (α := F))
    change Nat.card F ^ Module.finrank F X = Nat.card F ^ 1
    rw [← Module.natCard_eq_pow_finrank (K := F) (V := X),hc,pow_one]
  apply natural_line_normalizerAction_solvable e f hf _ hNB inf_le_left X hd hX
  exact inf_le_left.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
