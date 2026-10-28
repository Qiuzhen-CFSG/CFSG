module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SuzukiPresentation
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceRankOne

/-!
# A local Suzuki comparison on the same marked source quotient

Bijective field coordinates on the marked negative simple root, coordinates
on the entire Cartan, the specified simple Weyl class and finite local
multiplication/conjugation/Gauss equations construct an evaluation of the
canonical local presentation. Its kernel is proved trivial using the source
split geometry: root--Cartan disjointness treats the short cell and the
selected simple class excludes the long cell. Composing the two constructed
realizations identifies the source root--Cartan--reflection subgroup with the
actual corresponding subgroup of `ReeF4.Model m`, for every `m`.

The source producer must supply `SuzukiData` and `Relations`. The theorem
`relationsOfSourceConvention` converts the source cocycle to the native one
through the checked field change. These are finite local inputs, with no
assumed ambient homomorphism or evaluation-kernel premise. This comparison
does not include the rest of a parabolic radical or the other relative roots.

Source: the twisted rank-one reduction of Steinberg, *Lectures on Chevalley
Groups*, Section 11, Lemmas 62--64; GLS3 Section 2.4; the original split
quotient and ordered endpoint conventions of DGS, *Groups and Graphs*,
Theorem D, p.224, as implemented in `SourceBinary.RootCoordinates`.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SourceSuzukiPresentation
open Subgroup SuzukiConvention SuzukiPresentation
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (n : Q.tits.N)
variable {m : ℕ} (d : SourceRankOne.SuzukiData Q split i n m)

/-- The remaining finite local equations, in native signed coordinates.
The Gauss relation and literal simple-class marking are already in `SuzukiData`. -/
structure Relations : Prop where
  root_mul : ∀ t u v w : CoefficientField m,
    (d.chart (t,u) : X ⧸ Q.D)*(d.chart (v,w) : X ⧸ Q.D) =
      d.chart (t+v,u+w+titsEnd m t*v)
  torus_root : ∀ a : TorusParameter m, ∀ t u : CoefficientField m,
    d.h a*(d.chart (t,u) : X ⧸ Q.D)*(d.h a)⁻¹ =
      d.chart ((signedScale a.2 false : CoefficientField m)*t,
        (signedScale (centralScale a.2) false : CoefficientField m)*u)
  weyl_torus : ∀ a, (n : X ⧸ Q.D)*d.h a*n = d.h (torusReflection m .suzuki a)

/-- A source-oriented multiplication calculation transports to the native
root convention by the proved cocycle change. The source chart here is
`a ↦ d.chart (change m a)` on the same marked negative root. -/
theorem relationsOfSourceConvention
    (hmul : ∀ a b : CoefficientField m × CoefficientField m,
      (d.chart (change m a) : X ⧸ Q.D)*(d.chart (change m b) : X ⧸ Q.D) =
        d.chart (change m (sourceMul a b)))
    (htorus : ∀ a : TorusParameter m, ∀ t u : CoefficientField m,
      d.h a*(d.chart (t,u) : X ⧸ Q.D)*(d.h a)⁻¹ =
        d.chart ((signedScale a.2 false : CoefficientField m)*t,
          (signedScale (centralScale a.2) false : CoefficientField m)*u))
    (hweyl : ∀ a, (n : X ⧸ Q.D)*d.h a*n = d.h (torusReflection m .suzuki a)) :
    Relations Q split i n d where
  root_mul t u v w := by
    simpa only [change_mul,Equiv.apply_symm_apply,nativeMul] using
      hmul ((change m).symm (t,u)) ((change m).symm (v,w))
  torus_root := htorus
  weyl_torus := hweyl

variable (r : Relations Q split i n d)

/-- The source root homomorphism is constructed from the field multiplication law. -/
def rootHom : Parameter m →* X ⧸ Q.D where
  toFun a := d.chart (SuzukiPresentation.coordinates a)
  map_one' := by rw [coordinates_one]; exact d.chart_zero
  map_mul' a b := by
    rw [coordinates_mul]
    exact (r.root_mul _ _ _ _).symm

@[simp] theorem rootHom_apply (a : Parameter m) :
    rootHom Q split i n d r a = d.chart (SuzukiPresentation.coordinates a) := rfl

@[simp] theorem rootHom_chart (a : CoefficientField m × CoefficientField m) :
    rootHom Q split i n d r (nativeChartEquiv m false a) = d.chart a := by
  rw [rootHom_apply,coordinates_root]

theorem rootHom_injective : Function.Injective (rootHom Q split i n d r) := by
  intro a b he
  exact (nativeChartEquiv m false).symm.injective (d.chart.injective (Subtype.ext he))

theorem rootHom_range : (rootHom Q split i n d r).range = SourceRankOne.negativeRoot Q split i n := by
  ext y
  constructor
  · rintro ⟨a,rfl⟩
    exact (d.chart (SuzukiPresentation.coordinates a)).property
  · intro hy
    obtain ⟨a,ha⟩ := d.chart.surjective ⟨y,hy⟩
    exact ⟨nativeChartEquiv m false a,(rootHom_chart Q split i n d r a).trans (congrArg Subtype.val ha)⟩

/-- The source finite equations construct a realization of the same local presentation. -/
theorem equations : LocalPresentation.Equations (table m)
    (rootHom Q split i n d r) d.h (n : X ⧸ Q.D) where
  involution := d.reflection_sq
  torus_root a t := by
    simp only [rootHom_apply,table_action]
    exact r.torus_root a _ _
  weyl_torus := r.weyl_torus
  gauss a ha := by
    have hn := norm_coordinates_ne_zero a ha
    have hL : SuzukiPresentation.coordinates ((table m).gaussLeft a) =
        (negativeFirst (SuzukiPresentation.coordinates a).1 (SuzukiPresentation.coordinates a).2,
          negativeSecond (SuzukiPresentation.coordinates a).1 (SuzukiPresentation.coordinates a).2) :=
      coordinates_root _
    have hR : SuzukiPresentation.coordinates ((table m).gaussRight a) =
        (positiveFirst (SuzukiPresentation.coordinates a).1 (SuzukiPresentation.coordinates a).2,
          positiveSecond (SuzukiPresentation.coordinates a).1 (SuzukiPresentation.coordinates a).2) :=
      coordinates_root _
    have ht : (table m).gaussTorus a = suzukiTau
        (Units.mk0 (norm (SuzukiPresentation.coordinates a).1 (SuzukiPresentation.coordinates a).2) hn) :=
      dif_pos hn
    change (n : X ⧸ Q.D)*(d.chart (SuzukiPresentation.coordinates a) : X ⧸ Q.D)*n =
      (d.chart (SuzukiPresentation.coordinates ((table m).gaussLeft a)) : X ⧸ Q.D)*
        d.h ((table m).gaussTorus a)*n*d.chart (SuzukiPresentation.coordinates ((table m).gaussRight a))
    rw [hL,hR,ht]
    exact SourceRankOne.gauss_conjugate Q split i n d
      (SuzukiPresentation.coordinates a).1 (SuzukiPresentation.coordinates a).2 hn

/-- The full Borel of the same quotient, conjugated by its selected simple lift. -/
def oppositeBorel : Subgroup (X ⧸ Q.D) := rightConjugate Q.tits.B (n : X ⧸ Q.D)

theorem root_le_oppositeBorel : (rootHom Q split i n d r).range ≤ oppositeBorel Q n := by
  rw [rootHom_range]
  exact Subgroup.comap_mono ((simpleRoot_le Q split i).trans split.U_le)

theorem torus_le_oppositeBorel : d.h.range ≤ oppositeBorel Q n := by
  rw [d.h_range,← torus_conjugate n]
  exact Subgroup.comap_mono inf_le_left

include d in
theorem reflection_not_mem_oppositeBorel : (n : X ⧸ Q.D) ∉ oppositeBorel Q n := by
  intro hn
  have hB : (n : X ⧸ Q.D) ∈ Q.tits.B := by
    change (n : X ⧸ Q.D)*n*(n : X ⧸ Q.D)⁻¹ ∈ Q.tits.B at hn
    simpa only [mul_inv_cancel_right] using hn
  have hq : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = 1 :=
    (QuotientGroup.eq_one_iff n).mpr ⟨hB,n.property⟩
  exact (Q.tits.involutions _ (Q.simple_mem i)).1 (d.reflection_class.symm.trans hq)

theorem root_torus_disjoint : Disjoint (rootHom Q split i n d r).range d.h.range := by
  rw [rootHom_range,d.h_range,← torus_conjugate n]
  apply Subgroup.disjoint_def.mpr
  intro y hy ht
  have hc : (n : X ⧸ Q.D)*y*(n : X ⧸ Q.D)⁻¹ = 1 :=
    Subgroup.disjoint_def.mp ((unipotent_disjoint_torus split).mono_left (simpleRoot_le Q split i)) hy ht
  apply (MulAut.conj (n : X ⧸ Q.D)).injective
  simpa only [map_one,MulAut.conj_apply] using hc

/-- Both surjectivity and the source kernel are discharged on the literal quotient. -/
def sourceEquiv : LocalPresentation.Presentation (table m) ≃*
    SourceRankOne.generated Q split i n :=
  (LocalPresentation.realization (table m) (equations Q split i n d r)
    (rootHom_injective Q split i n d r) d.h_injective (root_torus_disjoint Q split i n d r)
    (oppositeBorel Q n) (root_le_oppositeBorel Q split i n d r)
    (torus_le_oppositeBorel Q split i n d) (reflection_not_mem_oppositeBorel Q split i n d)).trans
    (MulEquiv.subgroupCongr (by rw [rootHom_range,d.h_range]; rfl))

@[simp] theorem sourceEquiv_root (a : CoefficientField m × CoefficientField m) :
    (sourceEquiv Q split i n d r (LocalPresentation.root (table m) (nativeChartEquiv m false a)) : X ⧸ Q.D) = d.chart a := by
  exact (LocalPresentation.eval_root (table m) (equations Q split i n d r)
    (nativeChartEquiv m false a)).trans (rootHom_chart Q split i n d r a)

@[simp] theorem sourceEquiv_torus (t : TorusParameter m) :
    (sourceEquiv Q split i n d r (LocalPresentation.torus (table m) t) : X ⧸ Q.D) = d.h t :=
  LocalPresentation.eval_torus (table m) (equations Q split i n d r) t

@[simp] theorem sourceEquiv_reflection :
    (sourceEquiv Q split i n d r (LocalPresentation.reflection (table m)) : X ⧸ Q.D) = n :=
  LocalPresentation.eval_reflection (table m) (equations Q split i n d r)

/-- The actual marked local comparison, for all m. This identifies the group
generated by this root, the full Cartan and the reflection, not the full Ree model. -/
def comparison : SourceRankOne.generated Q split i n ≃* SuzukiPresentation.generated m :=
  (sourceEquiv Q split i n d r).symm.trans (nativeEquiv m)

@[simp] theorem comparison_sourceEquiv (g : LocalPresentation.Presentation (table m)) :
    comparison Q split i n d r (sourceEquiv Q split i n d r g) = nativeEquiv m g := by
  simp only [comparison,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]

/-- Generator formulas retain every field coordinate and the literal source element. -/
theorem comparison_root (a : CoefficientField m × CoefficientField m)
    (ha : (d.chart a : X ⧸ Q.D) ∈ SourceRankOne.generated Q split i n) :
    (comparison Q split i n d r ⟨d.chart a,ha⟩ : Model m) = suzuki m false a.1 a.2 := by
  have he : (⟨d.chart a,ha⟩ : SourceRankOne.generated Q split i n) =
      sourceEquiv Q split i n d r (LocalPresentation.root (table m) (nativeChartEquiv m false a)) :=
    Subtype.ext (sourceEquiv_root Q split i n d r a).symm
  rw [he,comparison_sourceEquiv,nativeEquiv_root,nativeChartEquiv_apply]

theorem comparison_torus (t : TorusParameter m)
    (ht : d.h t ∈ SourceRankOne.generated Q split i n) :
    (comparison Q split i n d r ⟨d.h t,ht⟩ : Model m) = torus m t := by
  have he : (⟨d.h t,ht⟩ : SourceRankOne.generated Q split i n) =
      sourceEquiv Q split i n d r (LocalPresentation.torus (table m) t) :=
    Subtype.ext (sourceEquiv_torus Q split i n d r t).symm
  rw [he,comparison_sourceEquiv,nativeEquiv_torus]

theorem comparison_reflection (hn : (n : X ⧸ Q.D) ∈ SourceRankOne.generated Q split i n) :
    (comparison Q split i n d r ⟨n,hn⟩ : Model m) = reflection m .suzuki := by
  have he : (⟨n,hn⟩ : SourceRankOne.generated Q split i n) =
      sourceEquiv Q split i n d r (LocalPresentation.reflection (table m)) :=
    Subtype.ext (sourceEquiv_reflection Q split i n d r).symm
  rw [he,comparison_sourceEquiv,nativeEquiv_reflection]

end ReeF4.RootPresentationRecognition.SourceSuzukiPresentation
