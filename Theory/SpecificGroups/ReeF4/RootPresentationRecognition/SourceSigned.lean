module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SignedCharts
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceNormalizer

/-!
# Signed-root comparisons on the same marked source quotient

The longest word in the already constructed full source normalizer transports
the eight positive field charts to negative charts. Their root laws and local
kernels are proved, and each whole signed root is compared with its native
carrier. Only the finite two-reflection equations are additional source
obligations. A group induction gives all Weyl conjugation equations; at each
simple root it places the entire opposite root inside the oriented endpoint.
The finite ascent table sends each ascending simple-root factor into the same
source U. Transporting the full Cartan through opposition derives its action
on every negative root without an additional source equation.

There is no supplied global model map, kernel condition, or simplicity premise.
The source owner must still construct the charts and verify the finite equations;
the presentation owner still owes global Bruhat collection and both whole-group
kernels. Binary type alternatives are not identified with these marked data.
Source: GLS3 2.3.6--8, Table 2.4, and DGS Groups and Graphs, Theorem D, p.224.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SourceSigned
open Subgroup SignedGeometry WeylPresentation
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable {m : ℕ} (d : SourcePositive.Charts Q split m)
variable (T : SourceBorel.TorusData Q split d) (W : SourceNormalizer.WeylData Q split d T)

def weyl : Weyl →* X ⧸ Q.D := Q.tits.N.subtype.comp (SourceNormalizer.weyl Q split d T W)

@[simp] theorem weyl_simple (s : Bool) : weyl Q split d T W (simple s) = W.n s :=
  congrArg Subtype.val (SourceNormalizer.weyl_simple Q split d T W s)

def signConj (p : Bool) : MulAut (X ⧸ Q.D) :=
  if p then 1 else MulAut.conj (weyl Q split d T W opposition)

def pair (r : Index) (a : CoefficientField m) : X ⧸ Q.D :=
  signConj Q split d T W r.1 (d.chart (.inl r.2) a)

def quartet (r : Index) (a b : CoefficientField m) : X ⧸ Q.D :=
  signConj Q split d T W r.1 (d.chart (.inr r.2) (a,b))

@[simp] theorem pair_positive (i : Fin 4) (a : CoefficientField m) :
    pair Q split d T W (true,i) a = d.chart (.inl i) a := rfl
@[simp] theorem quartet_positive (i : Fin 4) (a b : CoefficientField m) :
    quartet Q split d T W (true,i) a b = d.chart (.inr i) (a,b) := rfl

theorem pair_injective (r : Index) : Function.Injective (pair Q split d T W r) := by
  intro a b he
  exact (d.chart (.inl r.2)).injective (Subtype.ext ((signConj Q split d T W r.1).injective he))

theorem quartet_injective (r : Index) : Function.Injective
    (fun a : CoefficientField m × CoefficientField m => quartet Q split d T W r a.1 a.2) := by
  intro a b he
  exact (d.chart (.inr r.2)).injective (Subtype.ext ((signConj Q split d T W r.1).injective he))

/-- The remaining source obligations are local equations on two reflections
and sixteen signed root charts, with the same original full normalizer. -/
structure Equations : Prop where
  pair : ∀ s r a, (W.n s : X ⧸ Q.D) * pair Q split d T W r a * (W.n s : X ⧸ Q.D)⁻¹ =
    pair Q split d T W (step false s r) a
  quartet : ∀ s r a b,
    (W.n s : X ⧸ Q.D) * quartet Q split d T W r a b * (W.n s : X ⧸ Q.D)⁻¹ =
      quartet Q split d T W (step true s r) a b

variable (R : Equations Q split d T W)

include R in
/-- The finite simple equations extend to all sixteen literal source Weyl words. -/
theorem weyl_pair (w : Weyl) (r : Index) (a : CoefficientField m) :
    weyl Q split d T W w * pair Q split d T W r a * (weyl Q split d T W w)⁻¹ =
      pair Q split d T W (action false w r) a :=
  equivariant false (weyl Q split d T W) (pair Q split d T W)
    (by simpa only [weyl_simple] using R.pair) w r a

include R in
theorem weyl_quartet (w : Weyl) (r : Index) (a b : CoefficientField m) :
    weyl Q split d T W w * quartet Q split d T W r a b * (weyl Q split d T W w)⁻¹ =
      quartet Q split d T W (action true w r) a b :=
  equivariant true (weyl Q split d T W)
    (fun r (v : CoefficientField m × CoefficientField m) => quartet Q split d T W r v.1 v.2)
    (by intro s r v; simpa only [weyl_simple] using R.quartet s r v.1 v.2) w r (a,b)

include R in
/-- The negative linear chart is the literal simple-reflection conjugate of
its positive chart, preserving the actual opposite marking. -/
theorem pair_negative_simple (a : CoefficientField m) :
    pair Q split d T W (false,0) a =
      (W.n false : X ⧸ Q.D) * (d.chart (.inl 0) a : X ⧸ Q.D) * (W.n false : X ⧸ Q.D)⁻¹ := by
  simpa only [step, next, Bool.false_eq_true, Bool.not_true, if_true, Matrix.cons_val_zero,
    pair_positive, and_self] using (R.pair false (true,0) a).symm

include R in
theorem quartet_negative_simple (a b : CoefficientField m) :
    quartet Q split d T W (false,0) a b =
      (W.n true : X ⧸ Q.D) * (d.chart (.inr 0) (a,b) : X ⧸ Q.D) * (W.n true : X ⧸ Q.D)⁻¹ := by
  simpa only [step, next, Bool.not_true, if_true, Matrix.cons_val_zero,
    quartet_positive, and_self] using (R.quartet true (true,0) a b).symm

private theorem simple_mem_endpoint (s : Bool) :
    (W.n s : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple (SourceNormalizer.index d.orientation s)} :=
  Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
    (Q.tits.representative_mem_bruhatCell _ (W.n s) (W.placement s))

include R in
theorem pair_negative_mem_endpoint (a : CoefficientField m) :
    pair Q split d T W (false,0) a ∈
      Q.tits.standardParabolic {Q.simple (SourceNormalizer.index d.orientation false)} := by
  rw [pair_negative_simple Q split d T W R]
  exact mul_mem (mul_mem (simple_mem_endpoint Q split d T W false)
    (Q.tits.B_le_standardParabolic _ (split.U_le
      (SourcePositive.root_le_unipotent Q split d _ (d.chart (.inl 0) a).property))))
    (inv_mem (simple_mem_endpoint Q split d T W false))

include R in
theorem quartet_negative_mem_endpoint (a b : CoefficientField m) :
    quartet Q split d T W (false,0) a b ∈
      Q.tits.standardParabolic {Q.simple (SourceNormalizer.index d.orientation true)} := by
  rw [quartet_negative_simple Q split d T W R]
  exact mul_mem (mul_mem (simple_mem_endpoint Q split d T W true)
    (Q.tits.B_le_standardParabolic _ (split.U_le
      (SourcePositive.root_le_unipotent Q split d _ (d.chart (.inr 0) (a,b)).property))))
    (inv_mem (simple_mem_endpoint Q split d T W true))

/-- Signed root evaluation uses the already proved local positive homomorphism. -/
def rootHom (p : Bool) (i : PositiveTables.Root) :
    AngularPresentation.Parameter m i →* X ⧸ Q.D :=
  (signConj Q split d T W p).toMonoidHom.comp (SourceAngular.sourceRoot Q split d i)

theorem rootHom_injective (p : Bool) (i : PositiveTables.Root) :
    Function.Injective (rootHom Q split d T W p i) :=
  (signConj Q split d T W p).injective.comp
    (Subtype.val_injective.comp (SourceAngular.parameterEquiv Q split d i).injective)

@[simp] theorem rootHom_pair (p : Bool) (i : Fin 4) (a : CoefficientField m) :
    rootHom Q split d T W p (.inl i) (PositiveTables.rootChartEquiv m (.inl i) a) =
      pair Q split d T W (p,i) a := by
  change signConj Q split d T W p (SourceAngular.sourceRoot Q split d _ _) = _
  rw [SourceAngular.sourceRoot_field]
  rfl

@[simp] theorem rootHom_quartet (p : Bool) (i : Fin 4) (a b : CoefficientField m) :
    rootHom Q split d T W p (.inr i) (PositiveTables.rootChartEquiv m (.inr i) (a,b)) =
      quartet Q split d T W (p,i) a b := by
  change signConj Q split d T W p (SourceAngular.sourceRoot Q split d _ _) = _
  rw [SourceAngular.sourceRoot_field]
  rfl

/-- Comparison of every whole signed root, constructed from its field charts;
this is a local root isomorphism and is not a whole-group recognition claim. -/
def comparison (p : Bool) (i : PositiveTables.Root) :
    SignedCharts.rootGroup m p i ≃* (rootHom Q split d T W p i).range :=
  (SignedCharts.rootEquiv m p i).symm.trans
    (MonoidHom.ofInjective (rootHom_injective Q split d T W p i))

@[simp] theorem comparison_root (p : Bool) (i : PositiveTables.Root)
    (a : AngularPresentation.Parameter m i) :
    (comparison Q split d T W p i (SignedCharts.rootEquiv m p i a) : X ⧸ Q.D) =
      rootHom Q split d T W p i a := by
  change (MonoidHom.ofInjective (rootHom_injective Q split d T W p i)
    ((SignedCharts.rootEquiv m p i).symm (SignedCharts.rootEquiv m p i a)) : X ⧸ Q.D) = _
  rw [MulEquiv.symm_apply_apply]
  rfl


theorem pair_mul (r : Index) (a b : CoefficientField m) :
    pair Q split d T W r a * pair Q split d T W r b = pair Q split d T W r (a+b) := by
  have h : PositiveTables.rootChartEquiv m (.inl r.2) a *
      PositiveTables.rootChartEquiv m (.inl r.2) b =
        PositiveTables.rootChartEquiv m (.inl r.2) (a+b) :=
    by
      apply Subtype.ext
      change (PositiveTables.pair m r.2 a : Model m) * PositiveTables.pair m r.2 b =
        (PositiveTables.pair m r.2 (a+b) : Model m)
      exact congrArg (fun z : Parabolics.unipotent m => (z : Model m))
        (PositiveTables.pair_mul r.2 a b)
  have he := congrArg (rootHom Q split d T W r.1 (.inl r.2)) h
  rw [map_mul, rootHom_pair Q split d T W r.1 r.2 a,
    rootHom_pair Q split d T W r.1 r.2 b,
    rootHom_pair Q split d T W r.1 r.2 (a+b)] at he
  exact he

theorem quartet_mul (r : Index) (a b c f : CoefficientField m) :
    quartet Q split d T W r a b * quartet Q split d T W r c f =
      quartet Q split d T W r (a+c) (b+f+ReeF4.titsEnd m a*c) := by
  have h : PositiveTables.rootChartEquiv m (.inr r.2) (a,b) *
      PositiveTables.rootChartEquiv m (.inr r.2) (c,f) =
        PositiveTables.rootChartEquiv m (.inr r.2) (a+c,b+f+ReeF4.titsEnd m a*c) :=
    by
      apply Subtype.ext
      change (PositiveTables.quartet m r.2 a b : Model m) * PositiveTables.quartet m r.2 c f =
        (PositiveTables.quartet m r.2 (a+c) (b+f+titsEnd m a*c) : Model m)
      exact congrArg (fun z : Parabolics.unipotent m => (z : Model m))
        (PositiveTables.quartet_mul r.2 a b c f)
  have he := congrArg (rootHom Q split d T W r.1 (.inr r.2)) h
  rw [map_mul, rootHom_quartet Q split d T W r.1 r.2 a b,
    rootHom_quartet Q split d T W r.1 r.2 c f,
    rootHom_quartet Q split d T W r.1 r.2 (a+c) (b+f+titsEnd m a*c)] at he
  exact he

@[simp] theorem comparison_pair (p : Bool) (i : Fin 4) (a : CoefficientField m) :
    (comparison Q split d T W p (.inl i)
      (SignedCharts.rootEquiv m p (.inl i) (PositiveTables.rootChartEquiv m (.inl i) a)) : X ⧸ Q.D) =
        pair Q split d T W (p,i) a := by
  rw [comparison_root, rootHom_pair]

@[simp] theorem comparison_quartet (p : Bool) (i : Fin 4) (a b : CoefficientField m) :
    (comparison Q split d T W p (.inr i)
      (SignedCharts.rootEquiv m p (.inr i) (PositiveTables.rootChartEquiv m (.inr i) (a,b))) : X ⧸ Q.D) =
        quartet Q split d T W (p,i) a b := by
  rw [comparison_root, rootHom_quartet]

abbrev simpleIndex := SignedCharts.simpleIndex

include R in
/-- Whole opposite simple root groups lie in the correctly oriented endpoints. -/
theorem rootHom_negative_le_endpoint (s : Bool) :
    (rootHom Q split d T W false (simpleIndex s)).range ≤
      Q.tits.standardParabolic {Q.simple (SourceNormalizer.index d.orientation s)} := by
  rintro _ ⟨a,rfl⟩
  obtain ⟨v,rfl⟩ := (PositiveTables.rootChartEquiv m (simpleIndex s)).surjective a
  cases s
  · change CoefficientField m at v
    change rootHom Q split d T W false (.inl 0) (PositiveTables.rootChartEquiv m (.inl 0) v) ∈ _
    rw [rootHom_pair]
    exact pair_negative_mem_endpoint Q split d T W R v
  · change CoefficientField m × CoefficientField m at v
    change rootHom Q split d T W false (.inr 0) (PositiveTables.rootChartEquiv m (.inr 0) (v.1,v.2)) ∈ _
    rw [rootHom_quartet]
    exact quartet_negative_mem_endpoint Q split d T W R v.1 v.2

end ReeF4.RootPresentationRecognition.SourceSigned

namespace ReeF4.RootPresentationRecognition.SourceSigned
open Subgroup SignedGeometry WeylPresentation
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable {m : ℕ} (d : SourcePositive.Charts Q split m)
variable (T : SourceBorel.TorusData Q split d) (W : SourceNormalizer.WeylData Q split d T)
variable (R : Equations Q split d T W)

include R in
/-- All linear ascent steps land in the same original U, by the finite
signed equations, rather than by a supplied global comparison. -/
theorem pair_ascent (k : Fin 8) (a : CoefficientField m) :
    (weyl Q split d T W (alternating true k))⁻¹ * (d.chart (.inl 0) a : X ⧸ Q.D) *
      weyl Q split d T W (alternating true k) ∈ split.U := by
  apply ascent_mem false (weyl Q split d T W) (pair Q split d T W)
    (by simpa only [weyl_simple] using R.pair) split.U
  intro i a
  exact SourcePositive.root_le_unipotent Q split d (.inl i) (d.chart (.inl i) a).property

include R in
/-- The complete nonabelian Suzuki root satisfies every ascent step as well. -/
theorem quartet_ascent (k : Fin 8) (a b : CoefficientField m) :
    (weyl Q split d T W (alternating false k))⁻¹ * (d.chart (.inr 0) (a,b) : X ⧸ Q.D) *
      weyl Q split d T W (alternating false k) ∈ split.U := by
  refine ascent_mem true (weyl Q split d T W)
    (fun r (v : CoefficientField m × CoefficientField m) => quartet Q split d T W r v.1 v.2)
    (by intro s r v; simpa only [weyl_simple] using R.quartet s r v.1 v.2) split.U ?_ k (a,b)
  intro i v
  exact SourcePositive.root_le_unipotent Q split d (.inr i) (d.chart (.inr i) v).property

end ReeF4.RootPresentationRecognition.SourceSigned

namespace ReeF4.RootPresentationRecognition.SourceSigned
open Subgroup SignedGeometry WeylPresentation
open Theory.AlgebraicGroup.TitsSystem.SourceBinary

/-- Transport the full Cartan through opposition before acting on a negative
root parameter. This is a fixed native table on individual root groups. -/
def torusRootAction {m : ℕ} (p : Bool) (t : Parabolics.fixedTorus m)
    (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    AngularPresentation.Parameter m i :=
  SourceBorel.rootAction (if p then t else NormalizerPresentation.action m opposition⁻¹ t) i a

/-- The native signed table retains the entire Cartan, including both field units. -/
theorem native_torus_root {m : ℕ} (p : Bool) (t : Parabolics.fixedTorus m)
    (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    (t : Model m) * SignedCharts.rootHom m p i a * (t : Model m)⁻¹ =
      SignedCharts.rootHom m p i (torusRootAction p t i a) := by
  cases p
  · change (t : Model m) * (NormalizerPresentation.weyl m opposition * a *
        (NormalizerPresentation.weyl m opposition)⁻¹) * (t : Model m)⁻¹ =
      NormalizerPresentation.weyl m opposition *
        ((NormalizerPresentation.action m opposition⁻¹ t : Model m) * a *
          (NormalizerPresentation.action m opposition⁻¹ t : Model m)⁻¹) *
        (NormalizerPresentation.weyl m opposition)⁻¹
    rw [NormalizerPresentation.action_apply, map_inv]
    group
  · rfl

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable {m : ℕ} (d : SourcePositive.Charts Q split m)
variable (T : SourceBorel.TorusData Q split d) (W : SourceNormalizer.WeylData Q split d T)

/-- The previously proved full-normalizer equations give the same torus
transport in the source, for every Weyl word. -/
theorem weyl_torus (w : Weyl) (t : Parabolics.fixedTorus m) :
    weyl Q split d T W w * SourceNormalizer.torus Q split d T t *
      (weyl Q split d T W w)⁻¹ =
        SourceNormalizer.torus Q split d T (NormalizerPresentation.action m w t) := by
  exact (congrArg Subtype.val
    (DFunLike.congr_fun (SourceNormalizer.compatible Q split d T W w) t)).symm

private theorem positive_torus_root (t : Parabolics.fixedTorus m)
    (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    SourceNormalizer.torus Q split d T t * SourceAngular.sourceRoot Q split d i a *
      (SourceNormalizer.torus Q split d T t)⁻¹ =
        SourceAngular.sourceRoot Q split d i (SourceBorel.rootAction t i a) := by
  have he := T.action ((CentralCovers.OddPrimary.Order.fixedTorusEquiv m).symm t) i a
  rw [MulEquiv.apply_symm_apply] at he
  exact he

/-- Negative torus equations follow from the already required positive root
and normalizer equations; they introduce no additional source premise. -/
theorem torus_root (p : Bool) (t : Parabolics.fixedTorus m)
    (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    SourceNormalizer.torus Q split d T t * rootHom Q split d T W p i a *
      (SourceNormalizer.torus Q split d T t)⁻¹ =
        rootHom Q split d T W p i (torusRootAction p t i a) := by
  cases p
  · change SourceNormalizer.torus Q split d T t *
        (weyl Q split d T W opposition * SourceAngular.sourceRoot Q split d i a *
          (weyl Q split d T W opposition)⁻¹) * (SourceNormalizer.torus Q split d T t)⁻¹ =
      weyl Q split d T W opposition *
        SourceAngular.sourceRoot Q split d i
          (SourceBorel.rootAction (NormalizerPresentation.action m opposition⁻¹ t) i a) *
        (weyl Q split d T W opposition)⁻¹
    rw [← positive_torus_root Q split d T, ← weyl_torus Q split d T W, map_inv]
    group
  · exact positive_torus_root Q split d T t i a

end ReeF4.RootPresentationRecognition.SourceSigned
