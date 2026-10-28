module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondLinearCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Radical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SourceCatalogue
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondCartanCatalogue
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction.FixedLifting

/-!
# Linear-three exclusions and the non-field-four component assembly

Centralization of the entire original V₂ by O₂(L₂), together with its
nontrivial natural quotient action, forces O₂(L₂) into O₂(K) for either
linear-three containing quotient. The literal parabolic comparison in
SecondLinearCore rules this out. No recognition of the K-module is needed.
The SL₃ and Sp₄ applications discharge these action premises using their
unchanged flag markings and the proved full-plane fixed-lifting results.

The complete second-normalizer catalogue consequently leaves only equality
or the field-four nilpotent odd-kernel SL₂(5) extension. Away from field four,
combine this with the first-normalizer sieve and full-radical uniqueness to
obtain both relatively normal components, their He membership, and the exact
UniqueNoncentralComponent statement on full V₂.

The remaining preceding flag, Cartan, natural-plane and radical-action
inputs belong to qt-d-1222-natural-flag-cartan and
qt-d-1222-natural-preliminary-source, with their ultimate discharge by
qt-d-1222-natural-local-geometry. In particular, quotient naturality alone
does not replace the stated full-plane core or radical centralization.
The odd-radical signalizer at field four, both field-four triangle
orientations and the full 11.1.1--3 assembly remain with
qt-d-1222-natural-relative-components. These results do not assert that
remaining field-four source theorem.

Source: Aschbacher--Smith 11.1.2--3, printed pp.761--765, combined
manuscript of 1 March 2004; the preceding full-cover action is I.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Both linear-three rows contradict the original plane-core action.
Normality and every two-core in the comparison are relative to the
original second flag normalizer. -/
theorem second_not_linear_of_core_centralizing
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 < K)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G))
    (hnon : ¬ f.Li 1 ≤ centralizer (f.Vi 1 : Set G)) :
    ¬ (Source.IsSL (K ⧸ pCore 2 K) 3 (2^S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2^S.field.degree)) := by
  intro hmodel
  have hq : IsQuasisimple (K ⧸ pCore 2 K) := by
    rcases hmodel with ⟨F,_,_,_,⟨e⟩⟩ | ⟨F,_,_,_,⟨e⟩⟩
    · exact IsQuasisimple.of_mulEquiv e.symm
    · exact IsQuasisimple.of_mulEquiv e.symm
  let := hq
  let H := normalizer (f.Vi 1 : Set G)
  let : Group.IsPerfect (K.subgroupOf H) := hK.2.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom) (subgroupOfEquivOfLe hK.1).surjective
  have hc := SecondLinear.core_le_of_centralizing hK.1 hLK.le hcore hnon
  have hAH : f.Li 1 ≤ H := hLK.le.trans hK.1
  have hT : (T : Subgroup G) ≤ H := f.invariant 1
  let P := T.subtype hT
  have hlocal : (f.Li 1).subgroupOf H ∈ ChapterA.Section03.localCComponents P := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hT hAH).mp
      ⟨hAH,flag_mem_local_of_model D S f 1 hm⟩
    exact hh.1
  have hlt : (f.Li 1).subgroupOf H < K.subgroupOf H := by
    refine lt_of_le_of_ne (comap_mono hLK.le) ?_
    intro hh
    apply hLK.ne
    simpa only [map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le (show K ≤ H from hK.1)] using
      congrArg (map H.subtype) hh
  let a := subgroupOfEquivOfLe hAH
  let b := subgroupOfEquivOfLe hK.1
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hmodel' : Source.IsSL ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) 3
        (2^S.field.degree) ∨
      ClassicalGroup.IsPSL ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) 3
        (2^S.field.degree) := by
    rcases hmodel with ⟨F,hfield,hfin,hF,⟨e⟩⟩ | h
    · exact .inl ⟨F,hfield,hfin,hF,⟨bq.trans e⟩⟩
    · exact .inr (h.of_mulEquiv bq)
  apply SecondLinear.core_not_le_of_linear P hlocal hK.2 hlt S.nonbinary
    (hm.of_mulEquiv aq) hmodel'
  rw [pCoreIn_subgroupOf 2 _ H hAH,pCoreIn_subgroupOf 2 K H hK.1]
  exact comap_mono hc

/-- The literal natural-plane maps supply noncentrality; centralization
of the whole original plane by its smaller two-core excludes SL₃ and PSL₃. -/
theorem second_not_linear_of_core_and_natural_action
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 < K)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v)) :
    ¬ (Source.IsSL (K ⧸ pCore 2 K) 3 (2^S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2^S.field.degree)) := by
  apply second_not_linear_of_core_centralizing D S f hm hK hLK hcore
  intro hfix
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq S.field.Carrier
    (![1,0]) (![0,1]) (by simp) (by simp)
  obtain ⟨a,rfl⟩ := hπ g
  obtain ⟨v,hv⟩ := hp (![1,0])
  have he : flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v = v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hfix a.property v.toMul v.toMul.property).symm
  have ha := hact a v
  rw [he,hv] at ha
  have hg' : specialLinearNatural 2 (π a) (![1,0]) = (![0,1]) := hg
  rw [hg'] at ha
  have hz := congrFun ha 0
  simp at hz

/-- After the linear-three exclusions, the actual second-normalizer
catalogue leaves only equality or the field-four odd nilpotent extension. -/
theorem second_equal_or_nilpotent_from_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K) (hLK : f.Li 1 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) ⊓ centralizer (f.Vi 1 : Set G) = ⊥)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    f.Li 1 = K ∨ (S.field.degree = 2 ∧
      HasExtension (K ⧸ pCore 2 K)
        (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
        (fun Q _ => Source.IsSL Q 2 5)) := by
  by_cases he : f.Li 1 = K
  · exact .inl he
  have hlin := second_not_linear_of_core_and_natural_action D S f hm hK.1
    (lt_of_le_of_ne hLK he) hcore π hπ p hp hact
  rcases second_linear_or_nilpotent_from_cartan D S f hu hm hX hK hLK
    hXcard hfaith π hπ p hp hact hk with h | h | h | h
  · exact .inl h
  · exact (hlin (.inl h)).elim
  · exact (hlin (.inr h)).elim
  · exact .inr h

/-- Construct the original relatively normal component and apply the
sieve, retaining its He membership and literal smaller two-core. -/
theorem second_exists_normal_component_equal_or_nilpotent
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {X : Subgroup G} (hX : IsCartan T L X)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) ⊓ centralizer (f.Vi 1 : Set G) = ⊥)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K ∧
      f.Li 1 ≤ K ∧ K ∈ Chapter1.He G ∧
      (f.Li 1 = K ∨ (S.field.degree = 2 ∧
        HasExtension (K ⧸ pCore 2 K)
          (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
          (fun Q _ => Source.IsSL Q 2 5))) := by
  obtain ⟨K,hK,hLK,hHe,_⟩ := flag_exists_unique_normal_component_of_model D S f 1 hm
  exact ⟨K,hK,hLK,hHe,second_equal_or_nilpotent_from_cartan D S f hu hm hX hK hLK
    hXcard hfaith hcore π hπ p hp hact hk⟩

private theorem model_of_plane_projection
    {A : Type*} [Group A] [Finite A]
    (π : A →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (hk : π.ker = pCore 2 A) : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2^S.field.degree) := by
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  exact ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
    ⟨e.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv S.field.Carrier)⟩⟩

/-- The original SL₃ flag discharges every plane-action premise in the
linear-three exclusion, using its actual actor projection and vector marking. -/
theorem second_not_linear_sl3_flag
    (m : ActionEquiv D.centralQuotientAction (ChapterB.QuasisimpleSource.linearNatural S.field 3))
    {K : Subgroup G}
    (hK : Source.ComponentIn (normalizer ((SL3.flag D S m).Vi 1 : Set G)) K)
    (hLK : (SL3.flag D S m).Li 1 < K) :
    ¬ (Source.IsSL (K ⧸ pCore 2 K) 3 (2^S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2^S.field.degree)) :=
  second_not_linear_of_core_and_natural_action D S (SL3.flag D S m)
    (model_of_plane_projection D S (SL3.PlaneAction.planeProjection D S m)
      (SL3.PlaneAction.planeProjection_surjective D S m) (SL3.PlaneAction.planeProjection_ker D S m))
    hK hLK (SL3.PlaneAction.plane_core_centralizes D S m)
    (SL3.PlaneAction.planeProjection D S m) (SL3.PlaneAction.planeProjection_surjective D S m)
    (SL3.PlaneAction.planeEquiv D S m).toLinearMap (SL3.PlaneAction.planeEquiv D S m).surjective
    (SL3.PlaneAction.planeEquiv_intertwines D S m)

/-- The original Sp₄ central cover discharges every plane-action premise;
its full V₂, including C_V(L), is kept by the fixed-lifting theorem. -/
theorem second_not_linear_sp4_flag
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    {K : Subgroup G}
    (hK : Source.ComponentIn (normalizer ((Sp4.flag m S).Vi 1 : Set G)) K)
    (hLK : (Sp4.flag m S).Li 1 < K) :
    ¬ (Source.IsSL (K ⧸ pCore 2 K) 3 (2^S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2^S.field.degree)) :=
  second_not_linear_of_core_and_natural_action D S (Sp4.flag m S)
    (model_of_plane_projection D S (Sp4.PlaneAction.planeProjection S m)
      (Sp4.PlaneAction.planeProjection_surjective S m) (Sp4.PlaneAction.planeProjection_ker S m))
    hK hLK (Sp4.PlaneAction.planeCore_centralizes S m)
    (Sp4.PlaneAction.planeProjection S m) (Sp4.PlaneAction.planeProjection_surjective S m)
    (Sp4.PlaneAction.planeMap S m) (Sp4.PlaneAction.planeMap_surjective S m)
    (Sp4.PlaneAction.planeMap_intertwines S m)

/-- Away from field four the source-derived catalogue proves that L₂
itself is the relatively normal component, and proves its literal unique
noncentrality on full V₂. Only preceding flag, Cartan and radical facts remain. -/
theorem second_component_and_unique_of_nonfour
    (hn : S.field.degree ≠ 2) (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {X : Subgroup G} (hX : IsCartan T L X)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) ⊓ centralizer (f.Vi 1 : Set G) = ⊥)
    (hR : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1) ∧
      f.Li 1 ∈ Chapter1.He G ∧
      Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  have hc : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G) := by
    apply le_trans (pCoreIn_mono_of_normalizes
      (show f.Li 1 ≤ f.Li 1 ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le (f.Li 1).le_normalizer (f.sylow_normalizes_Li 1))) hR
  obtain ⟨K,hK,hLK,hHe,he⟩ := second_exists_normal_component_equal_or_nilpotent D S f hu hm
    hX hXcard hfaith hc π hπ p hp hact hk
  have heq : f.Li 1 = K := he.resolve_right (fun h => hn h.1)
  have hK' : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1) := heq.symm ▸ hK
  exact ⟨hK',heq.symm ▸ hHe,uniqueNoncentral_second_of_radical_and_natural_action
    S f hK'.1 hm hR π hπ p hp hact⟩

/-- The complete 11.1.2--3 conclusions outside field four, conditional
only on the preceding flag, Cartan and full-radical action inputs. Both
original local residuals themselves are the relatively normal components. -/
theorem components_and_unique_of_nonfour
    (hn : S.field.degree ≠ 2) (hu : f.IsInnerUnique)
    (hm : ∀ i : Fin 2, ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2
      (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    {X : Subgroup G} (hX : IsCartan T L X)
    (hXcard : ∀ i : Fin 2,
      Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li i)) = 2 ^ S.field.degree - 1)
    (hfaith : ∀ i : Fin 2,
      (X ⊓ Closure.coreQuotientCentralizer (f.Li i)) ⊓ centralizer (f.Vi i.castSucc : Set G) = ⊥)
    (hR : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    (∀ i : Fin 2, Source.NormalComponentIn (normalizer (f.Vi i.castSucc : Set G)) (f.Li i) ∧
      f.Li i ∈ Chapter1.He G) ∧
      Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  obtain ⟨hsecond,hHe₂,hu₂⟩ := second_component_and_unique_of_nonfour D S f hn hu (hm 1)
    hX (hXcard 1) (hfaith 1) hR π hπ p hp hact hk
  obtain ⟨K,hK,hLK,hHe,href⟩ := first_exists_normal_component_reduction D S f hu (hm 0)
    hfix hNT hX (hXcard 0) (hfaith 0)
  have heq : f.Li 0 = K := by
    cases href with
    | equal he => simpa using he
    | sl2 _ hf _ _ _ => exact (hn hf).elim
    | psl2 _ hf _ _ _ _ _ => exact (hn hf).elim
    | pgl3 _ hf _ => exact (hn hf).elim
  refine ⟨?_,hu₂⟩
  intro i
  fin_cases i
  · exact ⟨heq.symm ▸ hK,heq.symm ▸ hHe⟩
  · exact ⟨hsecond,hHe₂⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
