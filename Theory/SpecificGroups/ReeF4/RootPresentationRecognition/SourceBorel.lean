module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceAngular
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Cartan
public import Theory.GroupTheory.MarkedSemidirectProduct

/-!
# Full Borel comparison from finite positive and Cartan equations

The already constructed U comparison is equivariant under the entire Cartan:
the finite torus/root equations are checked on the generators of the proved
positive presentation and hence hold throughout U. The two actual internal
semidirect products then give an isomorphism of the entire native Borel with
the same source B. Its restrictions retain U and the full H = B ∩ N, with
literal root and torus formulas. The construction includes the binary field.

The source Cartan parametrization and the local action equations remain explicit
source obligations; no model map, global faithfulness or Borel isomorphism is an
input. Signed global Bruhat reduction and both parabolic comparisons are still
required for the full Ree recognition theorem.

Source: GLS3 2.3.4--8 and 2.4.5, `refs/KGroup/GLS3/chapter2.tex`;
DGS, *Groups and Graphs*, p.224.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SourceBorel
open Subgroup Theory.GroupTheory
open Parabolics CentralCovers.TwoPrimary CentralCovers.OddPrimary.Order
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable {m : ℕ} (d : SourcePositive.Charts Q split m) (E : SourceAngular.Equations Q split d)

/-- The actual full Cartan action on every native whole root group. -/
def rootAction (t : fixedTorus m) (i : PositiveTables.Root)
    (a : AngularPresentation.Parameter m i) : AngularPresentation.Parameter m i :=
  ⟨(t : Model m) * a * (t : Model m)⁻¹,
    (mem_normalizer_iff.mp (fixedTorus_normalizes_X m _ t.property) a).mp a.property⟩

/-- Full source Cartan parameters and finite torus/root equations. -/
structure TorusData where
  h : TorusParameter m →* X ⧸ Q.D
  range_eq : h.range = Q.tits.B ⊓ Q.tits.N
  injective : Function.Injective h
  action : ∀ t i a, h t * SourceAngular.sourceRoot Q split d i a * (h t)⁻¹ =
    SourceAngular.sourceRoot Q split d i (rootAction (fixedTorusEquiv m t) i a)

variable (T : TorusData Q split d)

/-- The Cartan comparison uses the entire two-dimensional torus. -/
def cartanEquiv : fixedTorus m ≃* (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  (fixedTorusEquiv m).symm.trans
    ((MonoidHom.ofInjective T.injective).trans (MulEquiv.subgroupCongr T.range_eq))

@[simp] theorem cartanEquiv_apply (t : fixedTorus m) :
    (cartanEquiv Q split d T t : X ⧸ Q.D) = T.h ((fixedTorusEquiv m).symm t) := rfl

/-- A native whole root, as an element of the entire U. -/
def rootU (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) : unipotent m :=
  ⟨a, ElementaryTwoBound.X_le_unipotent m _ a.property⟩

theorem comparison_symm_root (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    ((SourceAngular.comparison Q split d E).symm (rootU i a) : X ⧸ Q.D) =
      SourceAngular.sourceRoot Q split d i a := by
  let g := OrderedRootPresentation.root (AngularPresentation.table m) i a
  have he : AngularPresentation.nativeEquiv m g = rootU i a :=
    Subtype.ext (AngularPresentation.nativeEquiv_root m i a)
  rw [← he]
  change (SourceAngular.sourceEquiv Q split d E
    ((AngularPresentation.nativeEquiv m).symm (AngularPresentation.nativeEquiv m g)) : X ⧸ Q.D) = _
  rw [MulEquiv.symm_apply_apply]
  exact SourceAngular.eval_root Q split d E i a

theorem native_normalizes : fixedTorus m ≤ normalizer (unipotent m) :=
  (fixedTorus_le_borel m).trans (Parabolics.borel_le_unipotent_normalizer m)

/-- Conjugation of the full positive subgroup by its native Cartan. -/
abbrev nativeAction (m : ℕ) : fixedTorus m →* MulAut (unipotent m) :=
  (unipotent m).normalizerMonoidHom.comp (inclusion native_normalizes)

/-- Conjugation of the original U by the same original Cartan H = B ∩ N. -/
abbrev sourceAction : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) →* MulAut split.U :=
  split.U.normalizerMonoidHom.comp (inclusion (inf_le_left.trans split.normalizes))

private theorem nativeAction_root (t : fixedTorus m) (i : PositiveTables.Root)
    (a : AngularPresentation.Parameter m i) :
    nativeAction m t (rootU i a) = rootU i (rootAction t i a) := rfl

/-- The finite torus/root equations imply equivariance on the entire U.
The proof checks the generators of the constructed positive presentation. -/
theorem compatible (t : fixedTorus m) :
    (nativeAction m t).trans (SourceAngular.comparison Q split d E).symm =
      (SourceAngular.comparison Q split d E).symm.trans
        (sourceAction Q split (cartanEquiv Q split d T t)) := by
  let f : unipotent m →* X ⧸ Q.D :=
    split.U.subtype.comp (((SourceAngular.comparison Q split d E).symm.toMonoidHom).comp
      (nativeAction m t).toMonoidHom)
  let g : unipotent m →* X ⧸ Q.D :=
    (MulAut.conj (cartanEquiv Q split d T t : X ⧸ Q.D)).toMonoidHom.comp
      (split.U.subtype.comp (SourceAngular.comparison Q split d E).symm.toMonoidHom)
  have he : f.comp (AngularPresentation.nativeEquiv m).toMonoidHom =
      g.comp (AngularPresentation.nativeEquiv m).toMonoidHom := by
    apply PresentedGroup.ext
    rintro ⟨i,a⟩
    change f (AngularPresentation.nativeEquiv m
      (OrderedRootPresentation.root (AngularPresentation.table m) i a)) =
      g (AngularPresentation.nativeEquiv m
      (OrderedRootPresentation.root (AngularPresentation.table m) i a))
    have hr : AngularPresentation.nativeEquiv m
        (OrderedRootPresentation.root (AngularPresentation.table m) i a) = rootU i a :=
      Subtype.ext (AngularPresentation.nativeEquiv_root m i a)
    rw [hr]
    change ((SourceAngular.comparison Q split d E).symm
      (nativeAction m t (rootU i a)) : X ⧸ Q.D) =
        (cartanEquiv Q split d T t : X ⧸ Q.D) *
          ((SourceAngular.comparison Q split d E).symm (rootU i a) : X ⧸ Q.D) *
            (cartanEquiv Q split d T t : X ⧸ Q.D)⁻¹
    rw [nativeAction_root, comparison_symm_root, comparison_symm_root, cartanEquiv_apply]
    have ht := T.action ((fixedTorusEquiv m).symm t) i a
    rw [MulEquiv.apply_symm_apply] at ht
    exact ht.symm
  apply MulEquiv.ext
  intro u
  obtain ⟨a,rfl⟩ := (AngularPresentation.nativeEquiv m).surjective u
  apply Subtype.ext
  exact DFunLike.congr_fun he a

theorem native_disjoint : Disjoint (unipotent m) (fixedTorus m) :=
  disjoint_iff.mpr (SmallCompletion.unipotent_inf_fixedTorus m)

/-- The constructed positive and Cartan comparisons extend to the full Borel. -/
def comparison : borel m ≃* Q.tits.B :=
  (markedSemidirectEquiv (borel m) (unipotent m) (fixedTorus m)
    (SectionGeometry.BNPair.borel_eq_unipotent_sup_fixedTorus m).symm native_normalizes native_disjoint).symm.trans
    ((SemidirectProduct.congr (SourceAngular.comparison Q split d E).symm
      (cartanEquiv Q split d T) (compatible Q split d E T)).trans
        (markedSemidirectEquiv Q.tits.B split.U (Q.tits.B ⊓ Q.tits.N)
          split.factorization (inf_le_left.trans split.normalizes) (unipotent_disjoint_torus split)))

/-- The Borel map restricts to the already constructed full U comparison. -/
theorem comparison_unipotent (u : unipotent m) :
    (comparison Q split d E T ⟨u, unipotent_le_borel m u.property⟩ : X ⧸ Q.D) =
      ((SourceAngular.comparison Q split d E).symm u : X ⧸ Q.D) := by
  let J := markedSemidirectEquiv (borel m) (unipotent m) (fixedTorus m)
    (SectionGeometry.BNPair.borel_eq_unipotent_sup_fixedTorus m).symm native_normalizes native_disjoint
  have hu : J (SemidirectProduct.inl u) = ⟨u, unipotent_le_borel m u.property⟩ := by
    apply Subtype.ext
    simp only [J, markedSemidirectEquiv_apply, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, Subgroup.coe_one, mul_one]
  rw [← hu]
  change (markedSemidirectEquiv Q.tits.B split.U (Q.tits.B ⊓ Q.tits.N)
    split.factorization (inf_le_left.trans split.normalizes) (unipotent_disjoint_torus split)
    ((SemidirectProduct.congr (SourceAngular.comparison Q split d E).symm
      (cartanEquiv Q split d T) (compatible Q split d E T))
        (J.symm (J (SemidirectProduct.inl u)))) : X ⧸ Q.D) = _
  rw [MulEquiv.symm_apply_apply, markedSemidirectEquiv_apply]
  change ((SourceAngular.comparison Q split d E).symm u : X ⧸ Q.D) *
    (cartanEquiv Q split d T 1 : X ⧸ Q.D) = _
  rw [map_one, Subgroup.coe_one, mul_one]

/-- The Borel map also retains every element of the entire original Cartan. -/
theorem comparison_torus (t : fixedTorus m) :
    (comparison Q split d E T ⟨t, fixedTorus_le_borel m t.property⟩ : X ⧸ Q.D) =
      T.h ((fixedTorusEquiv m).symm t) := by
  let J := markedSemidirectEquiv (borel m) (unipotent m) (fixedTorus m)
    (SectionGeometry.BNPair.borel_eq_unipotent_sup_fixedTorus m).symm native_normalizes native_disjoint
  have ht : J (SemidirectProduct.inr t) = ⟨t, fixedTorus_le_borel m t.property⟩ := by
    apply Subtype.ext
    simp only [J, markedSemidirectEquiv_apply, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, Subgroup.coe_one, one_mul]
  rw [← ht]
  change (markedSemidirectEquiv Q.tits.B split.U (Q.tits.B ⊓ Q.tits.N)
    split.factorization (inf_le_left.trans split.normalizes) (unipotent_disjoint_torus split)
    ((SemidirectProduct.congr (SourceAngular.comparison Q split d E).symm
      (cartanEquiv Q split d T) (compatible Q split d E T))
        (J.symm (J (SemidirectProduct.inr t)))) : X ⧸ Q.D) = _
  rw [MulEquiv.symm_apply_apply, markedSemidirectEquiv_apply]
  change ((SourceAngular.comparison Q split d E).symm 1 : X ⧸ Q.D) *
    (cartanEquiv Q split d T t : X ⧸ Q.D) = _
  rw [map_one, Subgroup.coe_one, one_mul, cartanEquiv_apply]

/-- Field parameters of the full Cartan are preserved literally. -/
theorem comparison_torus_field (a : TorusParameter m) :
    (comparison Q split d E T
      ⟨fixedTorusEquiv m a, fixedTorus_le_borel m (fixedTorusEquiv m a).property⟩ : X ⧸ Q.D) =
        T.h a := by
  rw [comparison_torus, MulEquiv.symm_apply_apply]

/-- The entire unipotent subgroup has exactly its marked source image. -/
theorem comparison_unipotent_image :
    ((unipotent m).subgroupOf (borel m)).map (comparison Q split d E T).toMonoidHom =
      split.U.subgroupOf Q.tits.B := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    change (comparison Q split d E T x : X ⧸ Q.D) ∈ split.U
    have he := comparison_unipotent Q split d E T ⟨x,hx⟩
    change (comparison Q split d E T x : X ⧸ Q.D) = _ at he
    rw [he]
    exact ((SourceAngular.comparison Q split d E).symm ⟨x,hx⟩).property
  · intro y hy
    let u := SourceAngular.comparison Q split d E ⟨y,hy⟩
    refine ⟨⟨u, unipotent_le_borel m u.property⟩, u.property, ?_⟩
    apply Subtype.ext
    change (comparison Q split d E T ⟨u, unipotent_le_borel m u.property⟩ : X ⧸ Q.D) = y
    rw [comparison_unipotent]
    exact congrArg Subtype.val ((SourceAngular.comparison Q split d E).symm_apply_apply ⟨y,hy⟩)

/-- The whole two-dimensional Cartan, rather than one cyclic part, is marked. -/
theorem comparison_torus_image :
    ((fixedTorus m).subgroupOf (borel m)).map (comparison Q split d E T).toMonoidHom =
      (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.B := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    change (comparison Q split d E T x : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N
    have he := comparison_torus Q split d E T ⟨x,hx⟩
    change (comparison Q split d E T x : X ⧸ Q.D) = _ at he
    rw [he, ← T.range_eq]
    exact ⟨_,rfl⟩
  · intro y hy
    let t := (cartanEquiv Q split d T).symm ⟨y,hy⟩
    refine ⟨⟨t, fixedTorus_le_borel m t.property⟩, t.property, ?_⟩
    apply Subtype.ext
    change (comparison Q split d E T ⟨t, fixedTorus_le_borel m t.property⟩ : X ⧸ Q.D) = y
    rw [comparison_torus, ← cartanEquiv_apply]
    exact congrArg Subtype.val ((cartanEquiv Q split d T).apply_symm_apply ⟨y,hy⟩)

end ReeF4.RootPresentationRecognition.SourceBorel
