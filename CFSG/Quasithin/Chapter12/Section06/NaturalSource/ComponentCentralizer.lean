module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentAction
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Components.ActionTransport
public import Theory.GroupTheory.NormalizerAction.Centralizer

/-!
# Condition (*) in the actual component action

The center of K-star has odd order. Coprime lifting therefore identifies
centralizers inside K-hat with the image of the original centralizer in
K-star. Since L₁-star and V-star centralize V-star, the equality extends
to X-hat. The original centralizer normalizes L₁-star, so the full
centralizer in X-hat normalizes L₁-hat. Its two-by-three quotient then
puts L₁-hat in the intrinsic O₂,₃ of that centralizer.

The original earlier geometry remains explicit. Component exclusions,
12.6.26 and the universal natural reduction remain subsequent obligations.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Centralizer transport through the selected component's odd center makes
L₁-hat normal in the full faithful-action centralizer. -/
theorem SourceHypothesis.original_action_centralizer_normalizes_residual
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    a.action.range ⊓ centralizer ((V.subgroupOf c.localActor).map a.action : Set (MulAut (Nonabelian.Setup.star H c.K))) ≤
      normalizer (((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action : Set (MulAut (Nonabelian.Setup.star H c.K))) := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let A := Nonabelian.Setup.star H E.L₁
  let U := Nonabelian.Setup.star H V
  let N := normalizer (B : Set (Nonabelian.Setup.Hstar H))
  let f := B.normalizerMonoidHom
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hVH : V ≤ H := S.chosen.le_sylow.trans (fun x hx => hH.1.2 (Or.inr hx))
  have hAN : A ≤ N := S.original_residual_star_normalizes_selectedComponent D hZ z hz hH c
  have hAC : A ≤ centralizer (U : Set (Nonabelian.Setup.Hstar H)) :=
    S.original_point_residual_star_centralizes D hZ z hz hTV hTz hbound hH hn
  have hUC : U ≤ centralizer (U : Set (Nonabelian.Setup.Hstar H)) := by
    let : IsCyclic U := isCyclic_of_prime_card
      (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.1
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hcop : Nat.Coprime (Nat.card U) (Nat.card (center B)) := by
    rw [(S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.1]
    exact c.star_center_coprime_two
  have hgen : Nonabelian.Setup.star H c.localActor = B ⊔ (A ⊔ U) := by
    change ((c.K ⊔ E.L₁ ⊔ V).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) = _
    rw [subgroupOf_sup (sup_le c.le_H hAH) hVH,subgroupOf_sup c.le_H hAH,
      Subgroup.map_sup,Subgroup.map_sup,sup_assoc]
    rfl
  rw [a.range_eq_star_normalizer_map,a.map_eq_star_normalizer_map V le_sup_right,
    a.map_eq_star_normalizer_map E.L₁ (le_sup_right.trans le_sup_left),hgen]
  rw [←NormalizerAction.centralizer_supplement_image B U (A ⊔ U) c.normalized
    (sup_le hAN c.normalized) (sup_le hAC hUC) hcop]
  apply (map_mono (f := f) ?_).trans ((A.subgroupOf N).le_normalizer_map f)
  intro x hx
  exact A.le_normalizer_comap N.subtype
    (S.original_star_centralizer_normalizes_residual D hZ z hz hTV hTz hbound hH hn hx.2)

/-- Condition (*) uses the intrinsic two-three core of the actual
centralizer in X-hat, not the image of the larger H-star centralizer. -/
theorem SourceHypothesis.original_action_residual_le_centralizer_twoThreeCore
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    let A := (((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let C := centralizer (U : Set a.action.range)
    A.subgroupOf C ≤ (pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C)) := by
  let E := D.fullSetup hZ T z
  let A₀ := (E.L₁.subgroupOf c.localActor).map a.action
  let U₀ := (V.subgroupOf c.localActor).map a.action
  let A := A₀.subgroupOf a.action.range
  let U := U₀.subgroupOf a.action.range
  let C := centralizer (U : Set a.action.range)
  have hAC : A ≤ C := by
    intro x hx u hu
    exact Subtype.ext (a.residual_centralizes hx u.val hu)
  have hCN : C ≤ normalizer (A : Set a.action.range) := by
    intro x hx
    apply A₀.le_normalizer_comap a.action.range.subtype
    apply S.original_action_centralizer_normalizes_residual D hZ z hz hTV hTz hbound hH hn c a
    refine ⟨x.property,?_⟩
    intro u hu
    have huR : u ∈ a.action.range := (map_le_range _ _) hu
    exact congrArg Subtype.val (hx ⟨u,huR⟩ hu)
  let : (A.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hCN
  apply le_twoThreeCore_of_normal
  let e₁ := (subgroupOfEquivOfLe (show E.L₁ ≤ c.localActor from le_sup_right.trans le_sup_left)).symm
  let f := (a.action.subgroupMap (E.L₁.subgroupOf c.localActor)).comp e₁.toMonoidHom
  have hf : Function.Surjective f := (MonoidHom.subgroupMap_surjective _ _).comp e₁.surjective
  have hp : IsPGroup 3 (E.L₁ ⧸ pCore 2 E.L₁) := by
    obtain ⟨_,_,_,e,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
    exact (IsElementaryAbelian.isPGroup 3 BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9).of_equiv e.symm
  have hpA₀ : IsPGroup 3 (A₀ ⧸ pCore 2 A₀) := quotient_twoCore_isThreeGroup_of_surjective f hf hp
  let e₂ := (subgroupOfEquivOfLe (show A₀ ≤ a.action.range from map_le_range _ _)).symm
  let e₃ := (subgroupOfEquivOfLe hAC).symm
  exact quotient_twoCore_isThreeGroup_of_surjective (e₂.trans e₃).toMonoidHom
    (e₂.trans e₃).surjective hpA₀

end CFSG.Quasithin.Chapter12.Section06
