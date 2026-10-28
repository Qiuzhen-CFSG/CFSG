module
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.CoveredConclusion
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.KernelPlacement
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.NaturalNormalization
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Standing

/-!
# The covered13.3.9 branch and its original13.8.12 consumer

The literal local setup constructs the covered flag over its prescribed
six-letter projection. Natural-module irreducibility proves the required
12.2.6 normalization. The actual two-group point-action kernel and the
genuine theta identity give cubic generation and placement inside L₁.
The native covered recovery then supplies every Conclusion1339 clause.
The final theorem applies this universal implication to the actual residual
O²(O₂,F(H)∩M), using the independently proved standing-data adapter.

The genuinely earlier theta(M)=L, central-kernel control of13.3.7 and
normalizer bound13.2.2(9) are explicit; this does not assert their original
ambient proofs. No global13.3.2, component-placement, cubic-order, model,
Source1339 or conclusion-normality premise is used.
Source: Aschbacher--Smith13.3.9, p.887, and13.8.12(2), p.950.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.PointResidualImage
open Section08
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
open SolvableExclusion.Residual
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ J Y : Subgroup G}

/-- Choose the actual covered flag over the prescribed source projection. -/
theorem covered_flag_of_triple (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) :
    Nonempty (NaturalSetup L (T : Subgroup G) V V₁ V₃) := by
  rcases SourceCompletion.local_quotient_alternatives d with ⟨e,_⟩ | ⟨e,he⟩
  · obtain ⟨f⟩ := hcover.2.2
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center (L ⧸ pCore 2 L))
    rw [Nat.card_congr e.toEquiv,Nat.card_congr f.toEquiv,hcover.2.1,
      nat_card_alternatingGroup,Nat.card_fin] at hc
    norm_num at hc
  · exact SourceCompletion.local_covered_flag_model d e he

/-- Genuine theta and normalization inputs recover placement from the actual
point and its two-group action kernel; no13.3.8 placement conclusion is assumed. -/
theorem source_point_placement (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (htheta : closure {x:G | x∈M ∧ orderOf x=3} = L)
    (hY : Y ≤ M ⊓ normalizer (V:Set G)) (hp : IsPPerfect 2 Y)
    (hk : IsPGroup 2 (Y ⊓ centralizer (V:Set G) : Subgroup G))
    (v : G) (hv : v∈V₁) (hne : v∉V⊓centralizer (L:Set G))
    (hc : Y ≤ centralizer ({v}:Set G)) : Y ≤ one L (T:Subgroup G) V₁ := by
  let := SourceCompletion.local_elementary d
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hα : Function.Surjective α := d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  let e : Additive V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    d.coordinate.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  have hLP : L ≤ M ⊓ normalizer (V:Set G) :=
    le_inf (d.local_normalizer.symm ▸ L.le_normalizer) (le_sup_left.trans d.normalizes_V)
  have hPL : M ⊓ normalizer (V:Set G) ≤ normalizer (L:Set G) := by
    rw [←d.local_normalizer]; exact inf_le_left
  have hvV : v∈V := (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) hv
  have hv0 : v≠1 := by intro he; exact hne (he ▸ one_mem _)
  let w : Additive V := Additive.ofMul ⟨v,hvV⟩
  have hw : w≠0 := by
    intro he
    exact hv0 (congrArg (fun z:Additive V => z.toMul.val) he)
  have hYL : Y ≤ L := le_component_of_theta_point_two_kernel M L V Y hLP hPL α hα e
    (fun l w => d.conjugation l w.toMul) htheta hY hp hk w hw hc
  have hline : zpowers v = V₁ := by
    have he : zpowers (⟨v,hv⟩:V₁) = ⊤ :=
      zpowers_eq_top_of_prime_card d.line_card (by intro hh; exact hv0 (congrArg Subtype.val hh))
    have hh := congrArg (Subgroup.map V₁.subtype) he
    simpa only [MonoidHom.map_zpowers,subtype_apply,←MonoidHom.range_eq_map,range_subtype] using hh
  have hYC : Y ≤ centralizer (V₁:Set G) := by
    rw [←hline,zpowers_eq_closure,centralizer_closure]
    exact hc
  have hYP : Y ≤ parabolic L (T:Subgroup G) V₁ :=
    le_inf (hYL.trans le_sup_left) (hYC.trans (centralizer_le_normalizer _))
  have hr : residual Y = Y := by
    change (pResidual 2 Y).map Y.subtype = Y
    rw [(pResidual_eq_top_iff 2 Y).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  exact hr ▸ embedded_pResidual_mono 2 hYP

/-- Literal covered13.3.9 from the original standing setup. Placement in L₁,
two-group centralizer kernel and the 13.2.2(9) normalizer bound are the
three genuine preceding source inputs; every model and cubic calculation
is discharged internally. -/
theorem source_covered_conclusion (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hYJ : Y ≤ J) (hp : IsPPerfect 2 Y) (hn : (Y.subgroupOf J).Normal)
    (hplace : Y ≤ one L (T : Subgroup G) V₁)
    (hkernel : IsPGroup 2 (Y ⊓ centralizer (V : Set G) : Subgroup G))
    (hzero : normalizer (zero L : Set G) ≤ M) :
    Conclusion1339 L (one L (T : Subgroup G) V₁) (plus L (T : Subgroup G) V₁) M V Y := by
  obtain ⟨a⟩ := covered_flag_of_triple d hcover
  have hLM : L ≤ M := by rw [d.local_normalizer]; exact L.le_normalizer
  exact covered_conclusion_of_central_kernel T a hLM hJ hYJ hp hn hplace hkernel hzero

/-- The exact universal covered source consumer. The surviving earlier gates
are theta(M)=L,13.3.7 two-group central kernel, and the
13.2.2(9) normalizer bound. Point normalization and component placement
are proved from the actual natural action. -/
theorem source_covered_1339 (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (htheta : closure {x:G | x∈M ∧ orderOf x=3} = L)
    (hzero : normalizer (zero L : Set G) ≤ M)
    (hkernel : ∀ J Y : Subgroup G, J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) →
      Y ≤ J → IsPPerfect 2 Y → (Y.subgroupOf J).Normal →
      (∃ v ∈ V₁, v ∉ V ⊓ centralizer (L : Set G) ∧ Y ≤ M ⊓ centralizer ({v} : Set G)) →
      IsPGroup 2 (Y ⊓ centralizer (V : Set G) : Subgroup G)) :
    Source1339 L (one L (T : Subgroup G) V₁) (plus L (T : Subgroup G) V₁) T M V V₁ := by
  intro _ J Y hJ hY hp hn hv
  have hk := hkernel J Y hJ hY hp hn hv
  obtain ⟨v,hv,hne,hfix⟩ := hv
  have hnorm : Y ≤ M ⊓ normalizer (V:Set G) :=
    le_inf (hfix.trans inf_le_left) (hfix.trans (source_point_normalizes d hv hne))
  have hplace := source_point_placement d htheta hnorm hp hk v hv hne (hfix.trans inf_le_right)
  exact source_covered_conclusion d hcover hJ hY hp hn hplace hk hzero

/-- Actual13.8.12(2) on its original outside overgroup and Fitting residual.
All standing local fields are supplied by the proved original setup adapter;
only the named earlier ambient source gates of13.3.9 remain. -/
theorem source_covered_residual_alternative (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (htheta : closure {x:G | x∈M ∧ orderOf x=3} = L)
    (hzero : normalizer (zero L : Set G) ≤ M)
    (hkernel : ∀ J Y : Subgroup G, J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) →
      Y ≤ J → IsPPerfect 2 Y → (Y.subgroupOf J).Normal →
      (∃ v ∈ V₁, v ∉ V ⊓ centralizer (L : Set G) ∧ Y ≤ M ⊓ centralizer ({v} : Set G)) →
      IsPGroup 2 (Y ⊓ centralizer (V : Set G) : Subgroup G))
    {H : Subgroup G} (hH : H ∈ Source.Hz (one L T V₁) T G₁ M) :
    SolvableExclusion.ResidualAlternative L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) (SolvableExclusion.residualInM H M) := by
  obtain ⟨z,localData⟩ := SourceCompletion.LocalFitting.residual_local_data d hH
  exact residual_alternative localData
    (source_covered_1339 d hcover htheta hzero hkernel)
end CFSG.Quasithin.Chapter13.Section03.PointResidualImage
