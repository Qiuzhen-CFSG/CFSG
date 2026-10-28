module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.SteinbergObstruction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Kernel
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Bar

/-!
# Original barred coordinates and the two L-side section maps

The actual natural V action and source bar map have the same centralizer
kernel. Their quotient-range identifications construct compatible barred
coordinates. The point residual joined to the Sylow subgroup is the whole
original point parabolic. In the ordinary A₆ case the action kernel is
O₂(LT); restricting its projection constructs the actual parabolic quotient.
The original V coordinates likewise restrict to the outer-marked cubic
natural section. No chief-factor count or abelianness of U_L is assumed.

The ordinary quotient, parabolic image and common actor marking remain
explicit source inputs. CaseOne.SteinbergComparison applies these maps
to the original nonabelian branch. Earlier setup is owned by
qt-d-138-six-g2-source; final 13.8.33 remains with qt-d-138-a6-endgame-source.
Source: Aschbacher--Smith, 13.8.6 and 13.8.33, printed pp.948,966--968.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension
open A6Endgame.ActionAnalysis33.ChiefModels
open Section07.NaturalAction
open TransvectionQuotients.FiveSeed TransvectionQuotients.FiveSeed.BarMarking
open TransvectionQuotients.FourLocalFactors
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

private noncomputable def original_bar_range_equiv
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).range ≃*
      (permutation (localNaturalSetup d)).range := by
  letI := barKernel_normal (L ⊔ (T : Subgroup G)) V d.normalizes_V
  have hk : (permutation (localNaturalSetup d)).ker = barKernel (L ⊔ (T : Subgroup G)) V := by
    ext x
    exact Section07.permutation_eq_one_iff (localNaturalSetup d) x
  exact (barEquivImage (L ⊔ (T : Subgroup G)) V d.normalizes_V).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivRange (permutation (localNaturalSetup d))))

private theorem original_bar_range_equiv_apply
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    original_bar_range_equiv d ((barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict x) =
      (permutation (localNaturalSetup d)).rangeRestrict x := by
  let := barKernel_normal (L ⊔ (T : Subgroup G)) V d.normalizes_V
  have hb : barEquivImage (L ⊔ (T : Subgroup G)) V d.normalizes_V
      (QuotientGroup.mk' (barKernel (L ⊔ (T : Subgroup G)) V) x) =
      (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict x := by
    apply Subtype.ext
    rfl
  rw [← hb]
  simp only [original_bar_range_equiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rfl

/-- A symmetric bar image has canonical coordinates compatible with the original V action. -/
noncomputable def original_bar_equiv
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).range ≃* Equiv.Perm (Fin 6)) :
    (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).range ≃* Equiv.Perm (Fin 6) := by
  have hr : (permutation (localNaturalSetup d)).range = ⊤ := by
    apply eq_top_of_card_eq
    exact (Nat.card_congr (original_bar_range_equiv d).symm.toEquiv).trans (Nat.card_congr e.toEquiv)
  exact (original_bar_range_equiv d).trans ((MulEquiv.subgroupCongr hr).trans topEquiv)

theorem original_bar_equiv_apply
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    original_bar_equiv d e ((barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict x) =
      permutation (localNaturalSetup d) x := by
  change (original_bar_range_equiv d
    ((barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict x)).val = _
  rw [original_bar_range_equiv_apply]
  rfl

/-- The bar coordinates agree on every literal local subgroup image. -/
theorem original_bar_local_image
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (R : Subgroup G) :
    ((R.subgroupOf (L ⊔ (T : Subgroup G))).map
      (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict).map
      (original_bar_equiv d e).toMonoidHom =
      (R.subgroupOf (L ⊔ (T : Subgroup G))).map (permutation (localNaturalSetup d)) := by
  rw [map_map]
  congr 1
  exact MonoidHom.ext (original_bar_equiv_apply d e)

/-- The source residual and Sylow subgroup give the whole point parabolic. -/
theorem original_point_parabolic_eq
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (hH : H = G₁) :
    sourceOne L T V₁ ⊔ (T : Subgroup G) = (L ⊔ (T : Subgroup G)) ⊓ H := by
  rw [hH, d.first_normalizer]
  let P := (L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G)
  have ht : (T : Subgroup G) ≤ P := le_inf le_sup_right d.line_stable
  have hs := congrArg (fun A : Subgroup P => A.map P.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype ht))
  change (pResidual 2 P).map P.subtype ⊔ (T : Subgroup G) = P
  simpa only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le ht,
    ← MonoidHom.range_eq_map, range_subtype] using hs

/-- The genuine ordinary quotient determines the entire natural action kernel. -/
theorem ordinary_natural_kernel
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    (permutation (localNaturalSetup d)).ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let n := localNaturalSetup d
  let α := n.local_quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hα : Function.Surjective α := n.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : (permutation n).ker = actorKernel (L ⊔ (T : Subgroup G)) V := by
    ext x
    exact Section07.permutation_eq_one_iff n x
  have hCT := centralizer_le_sylow_of_natural_action L V T n.normalizes_L
    (permutation n) hk α hα (permutation_L n) eL
  ext x
  constructor
  · intro hx
    have hc : x.val ∈ centralizer (V : Set G) := (Section07.permutation_eq_one_iff n x).mp hx
    have ht : x.val ∈ (T : Subgroup G) := hCT ⟨hc,x.property⟩
    have hm : x.val ∈ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 :=
      h.sylow_centralizer ▸ ⟨ht,hc⟩
    obtain ⟨y,hy,he⟩ := hm
    exact (Subtype.ext he : y=x) ▸ hy
  · intro hx
    apply (Section07.permutation_eq_one_iff n x).mpr
    exact n.chosen.core_centralizes (mem_map_of_mem _ hx)

/-- Restrict the original V coordinates to the common marked cubic actor. -/
noncomputable def original_natural_section
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (A : Subgroup G) (hAL : A ≤ L ⊔ (T : Subgroup G)) (f : A →* cubicActor)
    (hmark : ∀ a : A, permutation (localNaturalSetup d) (inclusion hAL a) =
      (cubicActorEquiv (f a) : Equiv.Perm (Fin 6))) :
    OppositeSection A ⊥ V f .natural := by
  let _ := Representation.BinaryFixedPoints.action ModuleShape.natural.opposite
  refine ⟨bot_le, hAL.trans d.normalizes_V, d.coordinate.toMonoidHom,
    d.coordinate.surjective, ?_, ?_⟩
  · ext v
    change d.coordinate v = 1 ↔ (v : G) = 1
    rw [← map_one d.coordinate, d.coordinate.injective.eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  · let _ := conjMulDistribMulActionOfLeNormalizer A V (hAL.trans d.normalizes_V)
    intro a v
    exact (conjugation (localNaturalSetup d) (inclusion hAL a) v).trans
      (congrArg (fun g => BinaryPermutation.naturalRepresentation (Fin 6) g (d.coordinate v).toAdd)
        (hmark a))

/-- The L-side local quotient is the restriction of the original natural action.
Its exact kernel is O₂(LT), and its actor marking is retained. -/
noncomputable def original_parabolic_quotient
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hpar : ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
      (permutation (localNaturalSetup d))) = H1)
    (A : Subgroup G) (hAP : A ≤ (L ⊔ (T : Subgroup G)) ⊓ H) (f : A →* cubicActor)
    (hmark : ∀ a : A, permutation (localNaturalSetup d) (inclusion (hAP.trans inf_le_left) a) =
      (cubicActorEquiv (f a) : Equiv.Perm (Fin 6))) :
    LocalCoreQuotient A ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      ((L ⊔ (T : Subgroup G)) ⊓ H) duadCubicActor H1 (cubicActorEquiv.toMonoidHom.comp f) := by
  let X := L ⊔ (T : Subgroup G)
  let P := X ⊓ H
  let π := permutation (localNaturalSetup d)
  let φ : P →* H1 := (π.comp (inclusion inf_le_left)).codRestrict H1
    (fun x => hpar ▸ mem_map_of_mem π x.property)
  have hφ : Function.Surjective φ := by
    rintro ⟨y,hy⟩
    obtain ⟨x,hx,hxy⟩ := show y ∈ (P.subgroupOf X).map π from hpar.symm ▸ hy
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  have hk : φ.ker = (X.pCoreIn 2).subgroupOf P := by
    ext x
    change φ x = 1 ↔ (x : G) ∈ X.pCoreIn 2
    rw [← Subtype.coe_inj]
    change inclusion inf_le_left x ∈ π.ker ↔ _
    rw [ordinary_natural_kernel d h eL]
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow X (T.subtype le_sup_right)).trans_eq (map_subgroupOf_eq_of_le le_sup_right)
  exact ⟨hAP, le_inf (pCoreIn_le 2 X) (hQT.trans h.T_le_H), φ, hφ, hk, hmark⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
