module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Setup
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.LocalClosure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Central
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.PResidual.FiniteImage


/-!
# The original SL₃ seed and the literal G.2.5 maps

The central-cover theorem for the given chosen quotient action kills C_V(L).
Its original quotient projection is consequently a group equivalence from V
to the natural module. Independently, restricting LT/O₂(LT) to L has kernel
O₂(L), so the given model induces the required starred model. Both coordinate
and group maps retain their representative-level conjugation equations.

The solvable residual of N_L(V₁) lies in its two-residual; it is not identified
with it. Thus the preceding irreducibility under the former implies the G.2.1
interval condition for the latter. Nonabelianness of the actual closure forces
its starred image to be nontrivial. A supplied direct point frame then constructs
all fields of the genuine G.2.5 hypothesis.

This module does not choose the frame in N_L(X) or prove layer generation.
The explicit point, Sylow invariance and local irreducibility inputs are preceding
Chapter 11 geometry, owned by the chosen-natural and Cartan assembly tasks.
Source: Aschbacher--Smith, 11.0.3(3), 11.5.5 and 11.5.7, pp.760,780--782;
G.2.1 and G.2.5, pp.332,335--336.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open LocalGeometry
open ChapterG.Section02.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The solvable residual is contained in O² of the same point normalizer. -/
theorem pointResidual_le_setup_residual : E.L₁ ≤ (setup E).L₁ := by
  apply map_mono
  let N := L ⊓ E.G₁
  let : Group.IsNilpotent (N ⧸ pResidual 2 N) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  exact solvableResidual_le_of_solvable_quotient (pResidual 2 N)

/-- Construct G.2.1 for the original L, using preceding local irreducibility. -/
theorem setup_hypothesis (hp : E.point ≠ ⊥) (hne : E.V₁ ≠ V)
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ V →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = V) :
    (setup E).Hypothesis := by
  have hlocal : (setup E).L₁ ≤ L ⊓ E.G₁ := map_subtype_le _
  refine {
    elementary := D.elementary
    point_ne_bot := D.centralQuotientPreimage_ne_bot E.point hp
    point_le := E.V₁_le
    residual := (pResidual_eq_top_iff 2 L).mpr E.input.source.maximal_faithful.2.1.2.1
    V_le_T := D.le_sylow
    T_normalizes_point := hT
    T_normalizes_V := E.input.sylow_normalizes
    T_normalizes_L := D.sylow_normalizes_component
    sylow_LT := ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩
    H_le := le_rfl
    local_le := sup_le (hlocal.trans inf_le_right) hT
    sylow_H := ⟨T.subtype hT, map_subgroupOf_eq_of_le hT⟩
    characteristic_two := E.local_characteristic_two hp E.G₁ hT le_rfl
    local_normalizes_V := sup_le ((hlocal.trans inf_le_left).trans D.normalizes)
      E.input.sylow_normalizes
    quotient_nonzero := hne
    irreducible := ?_ }
  intro A hA hAV hN
  exact hirr A hA hAV ((sup_le_sup_right (pointResidual_le_setup_residual E) _).trans hN)

variable (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))

/-- Coordinates on V itself, via vanishing of the original central kernel. -/
def naturalCoordinates : V ≃* Multiplicative (Fin 3 → E.input.field.Carrier) :=
  MulEquiv.ofBijective (Coordinates.sl3 m).projection ⟨by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact (show (v : G) ∈ (⊥ : Subgroup G) from
      (Preliminary.sl3_centralizer_eq_bot D E.input m) ▸
        (show (v : G) ∈ V ⊓ centralizer (L : Set G) from
          ⟨v.property, ((Coordinates.sl3 m).projection_eq_one_iff v).mp hv⟩)),
    (Coordinates.sl3 m).projection_surjective⟩

theorem naturalCoordinates_apply (v : V) :
    naturalCoordinates E m v = (Coordinates.sl3 m).projection v := rfl

theorem naturalCoordinates_conjugation (l : L) (v : V) :
    (naturalCoordinates E m (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd =
      (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)).val *ᵥ
        (naturalCoordinates E m v).toAdd :=
  (Coordinates.sl3 m).projection_component_conjugation l v

omit m in
/-- The kernel of the literal star projection restricted to L. -/
theorem starProjection_ker : (starProjection (setup E)).ker = pCore 2 L := by
  have hmono : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  ext l
  have hmem : l ∈ (starProjection (setup E)).ker ↔
      (l : G) ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    change starProjection (setup E) l = 1 ↔ _
    rw [Subtype.ext_iff]
    change QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
      (inclusion le_sup_left l) = 1 ↔ _
    constructor
    · intro h
      exact ⟨_, (QuotientGroup.eq_one_iff _).mp h, rfl⟩
    · rintro ⟨a, ha, he⟩
      apply (QuotientGroup.eq_one_iff _).mpr
      have hh : a = inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l :=
        Subtype.ext he
      rwa [hh] at ha
  rw [hmem]
  constructor
  · intro h
    obtain ⟨a, ha, he⟩ := inf_pCoreIn_le_of_le 2
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) ⟨l.property, h⟩
    have hh : a = l := Subtype.ext he
    rwa [hh] at ha
  · intro h
    exact hmono ⟨l, h, rfl⟩

/-- Compare the star image with the original quotient L/O₂(L). -/
def starCoreQuotientEquiv : (setup E).star L ≃* (L ⧸ pCore 2 L) := by
  let p : L →* (setup E).star L := starProjection (setup E)
  exact (QuotientGroup.quotientKerEquivOfSurjective p
    (starProjection_surjective (setup E))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq
        (show p.ker = pCore 2 L from starProjection_ker E))

theorem starCoreQuotientEquiv_projection (l : L) :
    starCoreQuotientEquiv E (starProjection (setup E) l) =
      QuotientGroup.mk' (pCore 2 L) l := by
  let p : L →* (setup E).star L := starProjection (setup E)
  let e := QuotientGroup.quotientKerEquivOfSurjective p (starProjection_surjective (setup E))
  have he : e (QuotientGroup.mk' p.ker l) =
      starProjection (setup E) l := rfl
  change QuotientGroup.quotientMulEquivOfEq (show p.ker = pCore 2 L from starProjection_ker E)
    (e.symm (starProjection (setup E) l)) = _
  rw [← he, e.symm_apply_apply]
  rfl

/-- The full SL₃ model on the original star image. -/
def starModel : (setup E).star L ≃* SL(3, E.input.field.Carrier) :=
  (starCoreQuotientEquiv E).trans m.groupEquiv

theorem starModel_projection (l : L) :
    starModel E m (starProjection (setup E) l) =
      m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) := by
  exact congrArg m.groupEquiv (starCoreQuotientEquiv_projection E l)

theorem naturalCoordinates_equivariant (l : L) (v : V) :
    (naturalCoordinates E m (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd =
      (starModel E m (starProjection (setup E) l)).val *ᵥ
        (naturalCoordinates E m v).toAdd := by
  rw [starModel_projection]
  exact naturalCoordinates_conjugation E m l v

include E m in
/-- Nonzero-vector transitivity proves irreducibility on the original seed. -/
theorem seed_irreducible (A : Subgroup G) (hAV : A ≤ V)
    (hLA : L ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = V := by
  by_cases hA : A = ⊥
  · exact Or.inl hA
  right
  apply le_antisymm hAV
  obtain ⟨a, ha1⟩ := ne_bot_iff_exists_ne_one.mp hA
  have ha := a.property
  have ha1 : (a : G) ≠ 1 := fun he => ha1 (Subtype.ext he)
  have hca : (naturalCoordinates E m ⟨a, hAV ha⟩).toAdd ≠ 0 := by
    intro he
    have hh : (⟨a, hAV ha⟩ : V) = 1 := (naturalCoordinates E m).injective
      (he.trans (naturalCoordinates E m).map_one.symm)
    exact ha1 (congrArg Subtype.val hh)
  intro v hv
  by_cases hv1 : v = 1
  · simp [hv1]
  have hcv : (naturalCoordinates E m ⟨v, hv⟩).toAdd ≠ 0 := by
    intro he
    have hh : (⟨v, hv⟩ : V) = 1 := (naturalCoordinates E m).injective
      (he.trans (naturalCoordinates E m).map_one.symm)
    exact hv1 (congrArg Subtype.val hh)
  obtain ⟨u, hu⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hca hcv
  obtain ⟨l, hl⟩ := (m.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)) u
  change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = u at hl
  have he := (naturalCoordinates_conjugation E m l ⟨a, hAV ha⟩).trans
    (by simpa only [hl] using hu)
  have he' : (l : G) * a * (l : G)⁻¹ = v :=
    congrArg Subtype.val ((naturalCoordinates E m).injective he)
  exact he' ▸ (mem_normalizer_iff.mp (hLA l.property) a).mp ha

include m in
/-- The original nonzero point generates V under L. -/
theorem seed_span (hp : E.point ≠ ⊥) : (setup E).VL = V := by
  have hAV : (setup E).VL ≤ V := conjugateSpanBy_le E.V₁_le D.normalizes
  exact (seed_irreducible E m _ hAV (le_normalizer_conjugateSpanBy _ _)).resolve_left
    (fun he => D.centralQuotientPreimage_ne_bot E.point hp
      (bot_unique ((le_conjugateSpanBy E.V₁ L).trans he.le)))

theorem point_nonzero (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P) : E.point ≠ ⊥ := by
  intro hp
  have hle : (Coordinates.sl3 m).binarySubspace P ≤
      (Coordinates.sl3 m).binarySubspace ⊥ := by
    rw [← hpoint, hp]
    exact bot_le
  have he : P = ⊥ := bot_unique
    (((Coordinates.sl3 m).binarySubspace_le_iff P ⊥).mp hle)
  have hz : Module.finrank E.input.field.Carrier P = 0 := Submodule.finrank_eq_zero.mpr he
  omega

theorem point_ne_seed (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P) : E.V₁ ≠ V := by
  intro he
  have hpre : (Coordinates.sl3 m).preimage P = (Coordinates.sl3 m).preimage ⊤ := by
    rw [(Coordinates.sl3 m).preimage_top]
    exact (show (Coordinates.sl3 m).preimage P = E.V₁ from
      congrArg D.centralQuotientPreimage hpoint.symm).trans he
  have hP : P = (⊤ : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier)) :=
    (Coordinates.sl3 m).preimage_injective hpre
  have hdim' : Module.finrank E.input.field.Carrier P = 3 := by
    rw [hP]
    exact (finrank_top _ _).trans (Module.finrank_fin_fun _)
  omega

theorem naturalCoordinates_point
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P) (v : V) :
    (v : G) ∈ E.V₁ ↔ (naturalCoordinates E m v).toAdd ∈ P := by
  change (v : G) ∈ D.centralQuotientPreimage E.point ↔ _
  rw [hpoint]
  exact (Coordinates.sl3 m).mem_preimage P v

omit m in
/-- A trivial starred closure would centralize its seed and hence all its conjugates. -/
theorem star_closure_ne_bot_of_nonabelian
    (hUT : E.W ≤ (T : Subgroup G)) (hn : ¬ IsMulCommutative E.W) :
    (setup E).star E.W ≠ ⊥ := by
  intro hstar
  have hcore : E.W ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    intro w hw
    let w' : ↥(L ⊔ (T : Subgroup G)) := ⟨w, mem_sup_right (hUT hw)⟩
    have hm : QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) w' ∈
        (setup E).star E.W := ⟨w', hw, rfl⟩
    rw [hstar] at hm
    exact ⟨w', (QuotientGroup.eq_one_iff w').mp hm, rfl⟩
  apply hn
  apply le_centralizer_iff_isMulCommutative.mp
  exact le_centralizer_conjugateSpanBy_of_normalizes E.W V E.G₁
    (le_normalizer_conjugateSpanBy _ _) (hcore.trans D.core_centralizes)

/-- Construct the genuine marked hypothesis from a direct frame of original points.
The choice of x,y in the Cartan normalizer is a separate obligation. -/
def hypothesis_of_frame
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P)
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ V →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = V)
    (hUT : E.W ≤ (T : Subgroup G)) (hn : ¬ IsMulCommutative E.W)
    (x y : G) (hx : x ∈ L) (hy : y ∈ L)
    (hdisj : Disjoint E.V₁ (ChapterG.Section02.Setup.conjugate E.V₁ x))
    (hthird : Disjoint (E.V₁ ⊔ ChapterG.Section02.Setup.conjugate E.V₁ x)
      (ChapterG.Section02.Setup.conjugate E.V₁ y))
    (hspan : (E.V₁ ⊔ ChapterG.Section02.Setup.conjugate E.V₁ x) ⊔
      ChapterG.Section02.Setup.conjugate E.V₁ y = V) :
    Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y where
  setup := setup_hypothesis E (point_nonzero E m P hdim hpoint)
    (point_ne_seed E m P hdim hpoint) hT hirr
  exponent_pos := E.input.field.degree_pos
  field_card := E.input.field.card_eq
  span_eq := seed_span E m (point_nonzero E m P hdim hpoint)
  model := starModel E m
  coordinates := naturalCoordinates E m
  equivariant := naturalCoordinates_equivariant E m
  point := P
  point_dimension := hdim
  point_mem := naturalCoordinates_point E m P hpoint
  star_U_ne_bot := star_closure_ne_bot_of_nonabelian E hUT hn
  g_mem := hx
  h_mem := hy
  points_disjoint := hdisj
  third_disjoint := hthird
  points_span := hspan

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
