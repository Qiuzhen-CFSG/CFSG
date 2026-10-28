module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.Sp4.Seed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.Component
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The symplectic fixed-summand argument

Put Q=O₂(LT). The literal point-core quotient is abelian, so the proved
product R₁=O₂(L₁)Q gives [R₁,R₁]≤Q. Shortness gives [Q,L]=V, and
perfectness of L₁ therefore gives [Q,L₁]≤[V,L₁]=V₃. Conversely,
[V,O₂(L₁)]=V₃ and [V₃,L₁]=V₃. Hence
V₃=[[R₁,R₁],L₁], intrinsically inside the original ambient group.

When the fixed center is nontrivial, the preceding component argument
makes Y=N_G(R₁) normalize L₁, hence V₃. Source 11.1.4 contradicts escape.
This proves the actual Sp₄ fixed-summand conclusion directly, and supplies
the symplectic branch of `ExceptionalBlockActions`, including q=4 and
all possible nonsplit central kernels. The only retained preceding inputs
are actual shortness, the corrected center identity and source 11.1.4;
qt-d-1222-natural-normalizer-source owns their final source assembly.
The SL₃ TI centralizer argument remains with the fixed-summand owner.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
11.1.5, printed p.766. The intrinsic commutator identity spells out the
normalization step in its final symplectic sentence.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative commutatorElement
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Sp4
open PointCohomology.PointGeometry.Sp4Core
open WeakClosure.Nonnormalization.RootParabolic
open Representation.SymplecticFourOrthogonalCover
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
  (f : InvariantFlag (Coordinates.sp4 m))

private theorem first_twoPerfect : IsPPerfect 2 (f.Li 0) := by
  let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  intro N hN hp
  let := hN
  have hs : Subsingleton (f.Li 0 ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (f.Li 0 ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem first_normalizes_seed : f.Li 0 ≤ normalizer (V : Set G) :=
  ((localResidual_le _).trans inf_le_left).trans D.normalizes

/-- The original third space is fully moved by the original first residual. -/
theorem third_commutator : ⁅f.Vi 2,f.Li 0⁆ = f.Vi 2 := by
  let := D.elementary
  rw [←seed_first_commutator D S m f]
  exact commutator_isPPerfect_idempotent _ _ (first_twoPerfect D S m f)
    (IsElementaryAbelian.isPGroup 2 V) (first_normalizes_seed D S m f)

private theorem local_core_derived_le :
    ⁅(f.Li 0).pCoreIn 2,(f.Li 0).pCoreIn 2⁆ ≤ L.pCoreIn 2 := by
  let P := (f.Li 0).pCoreIn 2
  have hPL : P ≤ L := (pCoreIn_le _ _).trans ((localResidual_le _).trans inf_le_left)
  have hi : ⁅modelImage D S m P,modelImage D S m P⁆ = ⊥ := by
    rw [modelImage_core D S m (f.Li 0) ((localResidual_le _).trans inf_le_left),
      modelImage_point,←map_pCoreIn_of_injective 2 _ _
        (MulAut.conj (LocalGeometry.Sp4.alignment m)).injective]
    change ⁅((pCore 2 (pointLocal (F := S.field.Carrier))).map pointLocal.subtype).map _,
      ((pCore 2 (pointLocal (F := S.field.Carrier))).map pointLocal.subtype).map _⁆ = ⊥
    rw [pointLocal_core_eq S.field.card_eq S.nonbinary,←map_commutator,←map_commutator,
      commutator_self_eq_bot_iff.mpr (pointRadical_elementaryAbelian (F := S.field.Carrier)).toIsMulCommutative,
      Subgroup.map_bot,Subgroup.map_bot]
  apply commutator_le.mpr
  intro x hx y hy
  let x' : L := ⟨x,hPL hx⟩
  let y' : L := ⟨y,hPL hy⟩
  have hz : (Coordinates.sp4 m).quotientMap ⁅x',y'⁆ = 1 := by
    rw [map_commutatorElement]
    exact mem_bot.mp (hi ▸ commutator_mem_commutator
      (mem_map_of_mem _ hx) (mem_map_of_mem _ hy))
  have hk : ⁅x',y'⁆ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply m.groupEquiv.injective
    exact hz.trans (map_one _).symm
  exact mem_map_of_mem L.subtype hk

/-- The actual radical has abelian quotient by O₂(LT), including the outer
Sylow supplement. -/
theorem radical_derived_le_core :
    ⁅f.Ri 0,f.Ri 0⁆ ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let P := (f.Li 0).pCoreIn 2
  have hPQ : P ≤ normalizer (Q : Set G) :=
    (pCoreIn_le _ _).trans (((localResidual_le _).trans inf_le_left).trans
      (le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))))
  have hn : P ⊔ Q ≤ normalizer (Q : Set G) := sup_le hPQ Q.le_normalizer
  have hPP : ⁅P,P⁆ ≤ Q := (local_core_derived_le D S m f).trans
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component))
  have hRP : ⁅P ⊔ Q,P⁆ ≤ Q :=
    commutator_sup_le_of_relative_normal (P ⊔ Q) P Q P Q hn
      le_sup_left le_sup_right hPP (le_normalizer_iff_commutator_le_left.mp hPQ)
  have hRQ : ⁅P ⊔ Q,Q⁆ ≤ Q := le_normalizer_iff_commutator_le_right.mp hn
  rw [PointCohomology.PointGeometry.Sp4Core.core_product D S m f]
  exact commutator_sup_le_of_relative_normal (P ⊔ Q) P Q (P ⊔ Q) Q hn
    le_sup_left le_sup_right (by rwa [commutator_comm]) (by rwa [commutator_comm])

/-- The point residual moves the outer two-core inside V₃; perfectness
removes the possible displacement in the trivial quotient V/V₃. -/
theorem core_first_commutator_le (hb : ChapterC.IsShort L) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,f.Li 0⁆ ≤ f.Vi 2 := by
  have hn : f.Li 0 ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    ((localResidual_le _).trans inf_le_left).trans
      (le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))
  have hv : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,f.Li 0⁆ ≤ V :=
    (commutator_mono le_rfl ((localResidual_le _).trans inf_le_left)).trans
      (PointCohomology.core_commutator_eq_seed D hb).le
  rw [←commutator_isPPerfect_idempotent _ _ (first_twoPerfect D S m f)
    (isPGroup_pCoreIn 2 _) hn]
  exact (commutator_mono hv le_rfl).trans (seed_first_commutator_le D S m f)

/-- An intrinsic description of the original V₃, valid on the whole
possibly nonsplit cover. -/
theorem third_eq_radical_derived_commutator (hb : ChapterC.IsShort L) :
    f.Vi 2 = ⁅⁅f.Ri 0,f.Ri 0⁆,f.Li 0⁆ := by
  apply le_antisymm
  · have hP : (f.Li 0).pCoreIn 2 ≤ f.Ri 0 :=
      pCoreIn_mono_of_normalizes le_sup_left
        (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0))
    have hthree : f.Vi 2 ≤ ⁅f.Ri 0,f.Ri 0⁆ :=
      (seed_core_commutator D S m f).symm.le.trans
        (commutator_mono (f.seed_le_Ri S 0) hP)
    exact (third_commutator D S m f).symm.le.trans (commutator_mono hthree le_rfl)
  · exact (commutator_mono (radical_derived_le_core D S m f) le_rfl).trans
      (core_first_commutator_le D S m f hb)

/-- The original point-radical normalizer preserves V₃ whenever it
preserves L₁. The action is literal ambient conjugation. -/
theorem normalizes_third_of_normalizes_first (hb : ChapterC.IsShort L)
    (hn : normalizer (f.Ri 0 : Set G) ≤ normalizer (f.Li 0 : Set G)) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (f.Vi 2 : Set G) := by
  intro y hy
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [third_eq_radical_derived_commutator D S m f hb,map_commutator,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp hy,mem_normalizer_iff_map_conj_eq.mp (hn hy)]

/-- The caller's point residual has the literal rank-one quotient. -/
theorem first_isPSL :
    ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) := by
  have hf : f.space 0 = LocalGeometry.Sp4.space m 1 :=
    LocalGeometry.Sp4.space_inner_unique m 0 (f.space 0) (f.dimension 0)
      (inf_le_left.trans (f.invariant 0))
  change ClassicalGroup.IsPSL
    (localResidual L ((Coordinates.sp4 m).preimage (f.space 0)) ⧸ pCore 2
      (localResidual L ((Coordinates.sp4 m).preimage (f.space 0)))) 2 _
  rw [hf]
  exact ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
    ⟨LocalGeometry.Sp4.localCoreQuotientEquiv m S.nonbinary 0⟩⟩

/-- The first residual fixes the whole original line, including central lifts. -/
theorem first_centralizes_line : f.Li 0 ≤ centralizer (f.Vi 0 : Set G) := by
  apply le_centralizer_iff.mpr
  intro v hv l hl
  let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
  let l' : L := ⟨l,((localResidual_le _).trans inf_le_left) hl⟩
  let g := LocalGeometry.Sp4.alignment m
  let x : Vector S.field.Carrier := ((Coordinates.sp4 m).projection v').toAdd
  have hf : f.space 0 = LocalGeometry.Sp4.space m 1 :=
    LocalGeometry.Sp4.space_inner_unique m 0 (f.space 0) (f.dimension 0)
      (inf_le_left.trans (f.invariant 0))
  have hx : g⁻¹ • x ∈ point S.field.Carrier := by
    have hh := ((Coordinates.sp4 m).mem_preimage _ v').mp hv
    rw [hf] at hh
    exact (LocalGeometry.Sp4.ModelFlag.mem_movedStage g 1 x).mp hh
  have hi : (Coordinates.sp4 m).quotientMap l' ∈ modelImage D S m (f.Li 0) :=
    mem_map_of_mem _ hl
  rw [modelImage_point] at hi
  obtain ⟨b,hb,he⟩ := hi
  have hbfix : b • (g⁻¹ • x) = g⁻¹ • x := by
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hx
    rw [←ht]
    change toLinear b (t • e 0) = t • e 0
    rw [map_smul]
    exact congrArg (t • ·) ((mem_pointLocal_iff_fixed b).mp hb)
  have hproj : (Coordinates.sp4 m).modelAction ((Coordinates.sp4 m).quotientMap l')
      ((Coordinates.sp4 m).projection v').toAdd = ((Coordinates.sp4 m).projection v').toAdd := by
    change (show Sp S.field.Carrier from (Coordinates.sp4 m).quotientMap l') • x = x
    rw [←he]
    change (g*b*g⁻¹) • x = x
    rw [mul_smul,mul_smul,hbfix,smul_inv_smul]
  have hh := congrArg Subtype.val ((projection_fixed_iff D S m l' v').mp hproj)
  change l*v*l⁻¹=v at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- In the symplectic row the whole fixed center controls the original
third space; the intrinsic commutator identity supplies its invariance. -/
theorem radical_normalizer_normalizes_third (hb : ChapterC.IsShort L)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (f.Vi 2 : Set G) :=
  normalizes_third_of_normalizes_first D S m f hb
    (radical_normalizer_normalizes_first D S f (first_isPSL D S m f)
      (first_centralizes_line D S m f) hcenter hne)

/-- The actual Sp₄ fixed-summand target. The source 11.1.4 input has its
original third-space and first-residual arguments. No TI premise remains
in this branch. Its preceding source inputs are assembled by
qt-d-1222-natural-normalizer-source. -/
theorem normalizes_fixed (hb : ChapterC.IsShort L)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hcontrol : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0)
      (normalizer (L : Set G))) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G) := by
  by_cases hz : radicalFixedCenter (f.Ri 0) L = ⊥
  · rw [hz,Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))]
    exact le_top
  have hn := radical_normalizer_normalizes_first D S f (first_isPSL D S m f)
    (first_centralizes_line D S m f) hcenter hz
  exact (exceptional_escape_contradiction D S f hescape hcontrol
    (Or.inr (le_inf (normalizes_third_of_normalizes_first D S m f hb hn) hn))).elim

open Representation.BinaryOffender Representation.GoldschmidtONan
/-- The symplectic branch of the published exceptional-action contract. -/
theorem exceptional_normalizes_third_and_first (hb : ChapterC.IsShort L)
    (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (f.Vi 2 : Set G) ⊓ normalizer (f.Li 0 : Set G) := by
  have hn := chosen_exceptional_normalizes_first D S f (first_isPSL D S m f)
    (first_centralizes_line D S m f) X hcenter hfixed he
  exact le_inf (normalizes_third_of_normalizes_first D S m f hb hn) hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Sp4
