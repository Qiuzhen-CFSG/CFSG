module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallModule
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallRadicalAction
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalizerQuotient

public import Theory.GroupTheory.RadicalNormalizerModule

/-!
# Normalizers in the remaining small-Mathieu Hall configurations

The full radical commutator identifies the auxiliary C.2.8 module W with
original V. The C.2.12 normalizer theorem identifies the literal native
residual normalizer with the image of H ∩ N_G(L), including its
self-centralizing two-core. Radical saturation and [U,B] = [E,B] = E
then prove that this whole normalizer preserves the original module image.
For M₁₂ the radical is elementary, giving the full core and centralizer
identities as well. Its module centralizer in the residual normalizer is
exactly that radical. Full displacement also lifts module normalization
back through the complete original central cover.

The Hall consumer retains the escaping odd actor, the original pushing-up
and cubic witnesses, and the strict gap with the complete covering center.
It uses W = V only after proving equality for that same witness. The
M₁₂/M₂₂ exclusions and final Hall faithfulness remain open.

Source: Aschbacher–Smith C.2.12, 4.2.13 and 4.4.14,
printed pp.148,611–612 and624–625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original radical displacement and C.2.8 commutator recover the
whole auxiliary module as the original chosen module. -/
theorem sourceOrbit_pushingUp_small_module_eq
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) : W = V := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let M := H ⊓ normalizer (L : Set G)
  have hc := hw.2.2.2.2.2.2.1
  have hFM : F ≤ M := hc.component_le
  have hMF : M ≤ normalizer (F : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hFM).mp hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy F M = F :=
    le_antisymm (conjugateSpanBy_le le_rfl hMF) (le_conjugateSpanBy F M)
  have hW := hc.module_commutator
  rw [hspan] at hW
  have hWR := hc.module_le_center_radical.trans (map_subtype_le _)
  have hcomm := D.sourceOrbit_pushingUp_small_radical_commutator h hV hfix hm hw K hK e
  apply eq_of_le_of_card_ge
  · exact hW.le.trans ((commutator_mono hWR le_rfl).trans_eq hcomm)
  · exact hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- C.2.12 determines the full native residual normalizer through the
literal central quotient, and gives its self-centralizing two-core. -/
theorem sourceOrbit_pushingUp_native_normalizer
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let B := (F.comap j).map q
    let C := ((H ⊓ normalizer (L : Set G)).comap j).map q
    normalizer (B : Set Janko4.Model) = C ∧
      centralizer (pCore 2 C : Set C) ≤ pCore 2 C := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let M := H ⊓ normalizer (L : Set G)
  have hc := hw.2.2.2.2.2.2.1
  have hMF : M ≤ normalizer (F : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy F M = F :=
    le_antisymm (conjugateSpanBy_le le_rfl hMF) (le_conjugateSpanBy F M)
  have hn := hc.ordinary_image_normalizer K hK
  dsimp only at hn
  rw [hspan] at hn
  let B := ((F.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))
  let C := ((M.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))
  have heN : normalizer (B.map e.toMonoidHom : Set Janko4.Model) = C.map e.toMonoidHom := by
    rw [←map_equiv_normalizer_eq, hn.1]
  refine ⟨?_,?_⟩
  · simpa only [B,C,F,M,map_map,subgroupOf,comap_comap] using heN
  · let C' := ((H ⊓ normalizer (L : Set G)).comap (H.subtype.comp K.subtype)).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    have heC : C.map e.toMonoidHom = C' := by
      simp only [C,C',M,map_map,subgroupOf,comap_comap]
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      ((e.subgroupMap C).trans (MulEquiv.subgroupCongr heC))).mp hn.2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule


namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- In the M₁₂ case the native elementary radical is the entire
normalizer core and is self-centralizing in the containing J₄ model. -/
theorem sourceOrbit_pushingUp_m12_native_radical_normalizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := ((J.pCoreIn 2).comap j).map q
    let B := (F.comap j).map q
    (normalizer (B : Set Janko4.Model)).pCoreIn 2 = U ∧
      normalizer (U : Set Janko4.Model) = normalizer (B : Set Janko4.Model) ∧
      centralizer (U : Set Janko4.Model) = U := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let B := (F.comap j).map q
  let C := ((H ⊓ normalizer (L : Set G)).comap j).map q
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  let : IsElementaryAbelian 2 U := (D.sourceOrbit_pushingUp_m12_radical_elementary h hV hfix hm hw K hK e).1
  have hc := sourceOrbit_pushingUp_native_normalizer hw K hK e
  change normalizer (B : Set Janko4.Model) = C ∧ _ at hc
  apply Subgroup.abelian_radical_in_constrained U (normalizer (B : Set Janko4.Model)) hn.2.1
    (U.le_normalizer.trans hn.2.2.1) hn.2.2.1
  rw [hc.1]
  exact hc.2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule


namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The same full-cover maps identify the module image with the
commutator of the native normalizer core and its residual. -/
theorem sourceOrbit_pushingUp_native_normalizer_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    let Q := (normalizer (B : Set Janko4.Model)).pCoreIn 2
    E ≤ Q ∧ Q ≤ U ∧ ⁅Q,B⁆ = E ∧
      normalizer (B : Set Janko4.Model) ≤ normalizer (E : Set Janko4.Model) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Ek := V.comap j
  let Bk := F.comap j
  let U := ((J.pCoreIn 2).comap j).map q
  let E := Ek.map q
  let B := Bk.map q
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hc := hw.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK := hc.ordinary_component_contains_original K hK
  have hEV : Ek.map j = V := map_comap_eq_self
    ((D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).1.trans
      inf_le_right |>.trans_eq hjr.symm)
  have hBF : Bk.map j = F := by
    apply map_comap_eq_self
    rw [hjr]
    intro f hf
    exact ⟨⟨f,hFH hf⟩,hFK hf,rfl⟩
  have hmove : ⁅E,B⁆ = E := by
    have hk : ⁅Ek,Bk⁆ = Ek := map_injective hj (by
      rw [map_commutator,hEV,hBF]
      exact hw.2.2.2.2.2.2.2.2.2.1.symm)
    rw [←map_commutator,hk]
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  have hN := sourceOrbit_pushingUp_native_normalizer hw K hK e
  have hchar : centralizer (pCore 2 (normalizer (B : Set Janko4.Model)) :
      Set (normalizer (B : Set Janko4.Model))) ≤ pCore 2 (normalizer (B : Set Janko4.Model)) := by
    rw [hN.1]
    exact hN.2
  exact Subgroup.radical_normalizer_core_displacement U E B hn.2.1 hn.2.2.1 hchar
    hn.2.2.2.2.2.1
    (D.sourceOrbit_pushingUp_small_radical_centralizes h hV hfix hm hw K hK e)
    (D.sourceOrbit_pushingUp_small_radical_displacement h hV hfix hm hw K hK e) hmove
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Theory.GroupTheory Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original M₁₂ module has precisely the native radical as its
centralizer inside the full native residual normalizer. -/
theorem sourceOrbit_pushingUp_m12_module_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    normalizer (B : Set Janko4.Model) ⊓ centralizer (E : Set Janko4.Model) = U := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  let B := (F.comap j).map q
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  have hc := D.sourceOrbit_pushingUp_m12_native_radical_normalizer h hV hfix hm hw K hK e
  have hi := (D.sourceOrbit_pushingUp_m12_radical_elementary h hV hfix hm hw K hK e).2.2
  have hNE := (D.sourceOrbit_pushingUp_native_normalizer_core h hV hfix (.inl hm) hw K hK e).2.2.2
  refine le_antisymm (Subgroup.centralizer_le_core_of_fixed_index_le_two
    (normalizer (B : Set Janko4.Model)) U E hc.1 hc.2.2.le hn.2.2.2.2.2.1 hi hNE) ?_
  exact le_inf (U.le_normalizer.trans hn.2.2.1)
    (D.sourceOrbit_pushingUp_small_radical_centralizes h hV hfix (.inl hm) hw K hK e)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Theory.GroupTheory Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Lift the native module normalization to the original containing
component, using full displacement to remove the central-kernel ambiguity. -/
theorem sourceOrbit_pushingUp_cover_module_normalizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    normalizer (F.comap j : Set K) ≤ normalizer (V.comap j : Set K) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Ek := V.comap j
  let Bk := F.comap j
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hc := hw.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK := hc.ordinary_component_contains_original K hK
  have hEV : Ek.map j = V := map_comap_eq_self
    ((D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).1.trans
      inf_le_right |>.trans_eq hjr.symm)
  have hBF : Bk.map j = F := by
    apply map_comap_eq_self
    rw [hjr]
    intro f hf
    exact ⟨⟨f,hFH hf⟩,hFK hf,rfl⟩
  have hmove : ⁅Ek,Bk⁆ = Ek := map_injective hj (by
    rw [map_commutator,hEV,hBF]
    exact hw.2.2.2.2.2.2.2.2.2.1.symm)
  have hker : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  exact Subgroup.normalizer_le_of_moved_map_normalizer_le q hker.le Ek Bk
    (comap_mono hw.2.2.2.2.2.2.2.2.2.2.1) hmove
    (D.sourceOrbit_pushingUp_native_normalizer_core h hV hfix hm hw K hK e).2.2.2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original Hall obstruction has the original module in its full source
witness, and its literal native residual normalizer controls that same module.
The M12 radical is the entire self-centralizing normalizer core. -/
theorem sourceOrbit_mathieu_hall_native_normalizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H₀ : Subgroup G} (hH : H₀ ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H₀)
    (B₀ : Subgroup H₀) (hBN : B₀ ≤ (normalizer (L : Set G)).subgroupOf H₀)
    (hHall : IsHallSubgroup oddPrimes
      (B₀.subgroupOf ((normalizer (L : Set G)).subgroupOf H₀)))
    (hker : B₀.map H₀.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    Nat.card V = 1024 ∧
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H₀ ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
        Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
      MathieuPushingUpFactoredCase T L V A ∧
      ∃ J H : Subgroup G, Witness L V A J H V ∧
        ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
          ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
          ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K ∧
          ∃ (e : (K ⧸ center K) ≃* Janko4.Model) (x : K) (r : G),
            orderOf x = 3 ∧ CubicPumpupFullResolution H K x r ∧
            ((T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
              V ⊔ (center K).map (H.subtype.comp K.subtype) < J.pCoreIn 2 ⊓ K.map H.subtype) ∧
            ⁅J.pCoreIn 2,(solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype⁆ = V ∧
            let j := H.subtype.comp K.subtype
            let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
            let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
            let U := ((J.pCoreIn 2).comap j).map q
            let E := (V.comap j).map q
            let B := (F.comap j).map q
            let C := ((H ⊓ normalizer (L : Set G)).comap j).map q
            let Q := (normalizer (B : Set Janko4.Model)).pCoreIn 2
            q.ker ≤ (J.pCoreIn 2).comap j ∧ IsPRadical 2 U ∧
              normalizer (U : Set Janko4.Model) ≤ normalizer (B : Set Janko4.Model) ∧
              E ≤ U ∧ Nat.card E = Nat.card V ∧ U ≤ centralizer (E : Set Janko4.Model) ∧
              ⁅U,B⁆ = E ∧
              (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) →
                IsElementaryAbelian 2 U ∧ Nat.card U ≤ 2048 ∧ E.relIndex U ≤ 2 ∧
                  ¬ 2 ∣ Nat.card (centralizer (B : Set Janko4.Model))) ∧
              (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22) →
                Nat.card U ≤ 16384 ∧ E.relIndex U ≤ 16) ∧
              normalizer (B : Set Janko4.Model) = C ∧
              centralizer (pCore 2 C : Set C) ≤ pCore 2 C ∧
              E ≤ Q ∧ Q ≤ U ∧ ⁅Q,B⁆ = E ∧
              normalizer (B : Set Janko4.Model) ≤ normalizer (E : Set Janko4.Model) ∧
              (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) →
                Q = U ∧ normalizer (U : Set Janko4.Model) = normalizer (B : Set Janko4.Model) ∧
                  centralizer (U : Set Janko4.Model) = U ∧
                  normalizer (B : Set Janko4.Model) ⊓ centralizer (E : Set Janko4.Model) = U) ∧
              normalizer (F.comap j : Set K) ≤ normalizer (V.comap j : Set K) := by
  have hsize := (@sourceOrbit_mathieu_hall_small_module G instG finG T L V D
    h hmany hV hm hnon H₀ hH hlarge B₀ hBN hHall hker).2.1
  have hsource := @sourceOrbit_mathieu_hall_small_radical_action G instG finG T L V D
    h hmany hV hm hnon H₀ hH hlarge B₀ hBN hHall hker
  refine ⟨hsize,?_⟩
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hsmall,hfact,hgap⟩ := hA
  obtain ⟨J,H,W,hw,K,hK,hn,hout,hFK,e,x,r,hx,hfull,hgap,hcomm,hdata⟩ := hgap
  obtain ⟨hZ,hrad,hNB,hEU,hcard,hcent,hdisp,h12,h22⟩ := hdata
  have hfix := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hWV := D.sourceOrbit_pushingUp_small_module_eq h.toHypothesis1221 hV hfix hsmall hw K hK e
  subst W
  have hnorm := sourceOrbit_pushingUp_native_normalizer hw K hK e
  have hcore := D.sourceOrbit_pushingUp_native_normalizer_core h.toHypothesis1221 hV hfix hsmall hw K hK e
  refine ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hsmall,hfact,
    J,H,hw,K,hK,hn,hout,hFK,e,x,r,hx,hfull,hgap,hcomm,
    hZ,hrad,hNB,hEU,hcard,hcent,hdisp,h12,h22,hnorm.1,hnorm.2,
    hcore.1,hcore.2.1,hcore.2.2.1,hcore.2.2.2,?_,?_⟩
  · intro hm12
    have hn12 := D.sourceOrbit_pushingUp_m12_native_radical_normalizer h.toHypothesis1221 hV hfix hm12 hw K hK e
    exact ⟨hn12.1,hn12.2.1,hn12.2.2,
      D.sourceOrbit_pushingUp_m12_module_centralizer h.toHypothesis1221 hV hfix hm12 hw K hK e⟩
  · exact D.sourceOrbit_pushingUp_cover_module_normalizer h.toHypothesis1221 hV hfix hsmall hw K hK e
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
