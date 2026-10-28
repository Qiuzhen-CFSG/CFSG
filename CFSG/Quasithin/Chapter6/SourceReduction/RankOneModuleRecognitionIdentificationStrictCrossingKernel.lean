module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictBinaryModule
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PlaneConjugateSpan

/-!
# The exact crossing-action kernel

Put N = C_H(U/Z(U)) and R = T ∩ N. Frattini's argument gives
H = N N_H(R). The preimage F of the R-fixed space in U/⟨z⟩ contains
the source plane. Its product with Z(U) is H-invariant, because N acts
trivially modulo Z(U); source orbit generation therefore gives F Z(U)=U.

The original X lies in the original Sylow subgroup T. An element of
X ∩ N thus fixes modulo ⟨z⟩ an element of F outside C_U(Z_S). The
natural crossing-module fixed bound puts it in E. The reverse inclusion
follows from E ≤ U, yielding C_X(U/Z(U))=E and hence source 6.2.17(6).
The induced X/E ≃ X-dot is constructed with its literal quotient formula.

Source: Aschbacher--Smith, 6.2.17, printed pp.689--690. The Chapter12
StrictCrossingKernel application retains the whole reduced layer.
The fixed bound on U/Z(U), rank identity and final elimination remain with
qt-d-1222-recognition-strict-elimination. The allowed LocalAnalysis premise
is discharged by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The fixed subgroup modulo the original point supplements Z(U).
This is the source Frattini argument with the original Sylow group. -/
theorem LocalAnalysis.strict_fixed_lift_sup_center
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let U := sourceClosure (T : Subgroup G) L R z
    let N := (strictQuotientAction (T : Subgroup G) L R z).ker.map
      (centralizer ({z} : Set G)).subtype
    commutatorPreimage U ((T : Subgroup G) ⊓ N) (zpowers z) ⊔ (center U).map U.subtype = U := by
  let U := sourceClosure (T : Subgroup G) L R z
  let H := centralizer ({z} : Set G)
  let K := (strictQuotientAction (T : Subgroup G) L R z).ker
  let N := K.map H.subtype
  let R₀ := (T : Subgroup G) ⊓ N
  let C := (center U).map U.subtype
  let F := commutatorPreimage U R₀ (zpowers z)
  have hUH : U ≤ H := A.closure_le_core.trans (H.pCoreIn_le 2)
  have hHZ : H ≤ normalizer (zpowers z : Set G) := by
    apply (show H ≤ centralizer (zpowers z : Set G) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    apply le_centralizer_iff.mp
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hUZ := hUH.trans hHZ
  have hHU : H ≤ normalizer (U : Set G) := sourceClosure_normalized _ _ _ _
  have hHC : H ≤ normalizer (C : Set G) := hHU.trans
    (normalizer_le_normalizer_characteristic_image U (center U))
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow (T.subtype hTH) K
    le_normalizer_of_normal
  let Rₕ := (P : Subgroup K).map K.subtype
  have hRₕ : Rₕ.map H.subtype = R₀ := by
    change ((P : Subgroup K).map K.subtype).map H.subtype = _
    rw [hP, subgroupOf_map_subtype, map_inf _ _ _ H.subtype_injective,
      Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]
  let B := (normalizer (Rₕ : Set H)).map H.subtype
  have hBH : B ≤ H := map_subtype_le _
  have hBR : B ≤ normalizer (R₀ : Set G) := by
    rw [← hRₕ]
    exact le_normalizer_map _
  have hBF : B ≤ normalizer (F : Set G) := commutatorPreimage_normalized
    U R₀ (zpowers z) B hUZ (hBH.trans hHU) hBR (hBH.trans hHZ)
  have hBFC : B ≤ normalizer ((F ⊔ C : Subgroup G) : Set G) :=
    (le_inf hBF (hBH.trans hHC)).trans (normalizer_inf_normalizer_le_normalizer_sup F C)
  have hUC : ⁅U,N⁆ ≤ C := by
    rw [commutator_comm]
    apply commutator_le.mpr
    rintro a ⟨a, ha, rfl⟩ u hu
    exact (strictQuotientAction_mem_ker _ _ _ _ a).mp ha u hu
  have hFCU : F ⊔ C ≤ U := sup_le (commutatorPreimage_le _ _ _) (map_subtype_le _)
  have hNFC : N ≤ normalizer ((F ⊔ C : Subgroup G) : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hFCU le_rfl).trans hUC).trans le_sup_right)
  have hHBN : H = B ⊔ N := by
    have hh := congrArg (Subgroup.map H.subtype) P.normalizer_sup_eq_top
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] using hh.symm
  have hHFC : H ≤ normalizer ((F ⊔ C : Subgroup G) : Set G) := by
    rw [hHBN]
    exact sup_le hBFC hNFC
  have hSF : ZS (T : Subgroup G) L R ≤ F := le_commutatorPreimage
    ((ZS_le_sourceClosure_intersection h611 hz).trans inf_le_left)
    (plane_line_commutator _ _ _ (zpowers_le.mpr hz)
      (h611.natural_ZS_geometry hnatural).2.1 ((Nat.card_zpowers z).trans horder)
      (inf_le_left.trans h611.sylow_normalizes_ZS) (inf_le_left.trans (hTH.trans hHZ)))
  apply le_antisymm hFCU
  change sourceClosure (T : Subgroup G) L R z ≤ _
  rw [strict_sourceClosure_eq_span h611 hz]
  exact conjugateSpanBy_le (hSF.trans le_sup_left) hHFC

/-- The original crossing subgroup lies in the original Sylow two-subgroup. -/
theorem LocalAnalysis.strict_crossing_le_sylow
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G)) :
    strictCrossingGroup (T : Subgroup G) L R z d ≤ (T : Subgroup G) := by
  obtain ⟨heU, _, _, hI, hP, _⟩ :=
    A.strict_binary_crossing_module h611 hnatural hz horder hTH hstrict hdres hdH
  let D := strictBinarySetup (T : Subgroup G) L R z
  have hXI : strictCrossingGroup (T : Subgroup G) L R z d ≤ D.I d :=
    (le_sup_right.trans hP.ge).trans ((D.I d).pCoreIn_le 2)
  have hIL : D.I d ≤ L ⊔ (T : Subgroup G) := by
    rw [hI]
    exact sup_le (((map_subtype_le _).trans inf_le_left).trans le_sup_left)
      ((A.strict_binary_closure h611 hz hTH).1.ge.trans
        ((A.strict_binary_closure h611 hz hTH).2.trans le_sup_right))
  exact (le_inf (hXI.trans hIL) (strictCrossingGroup_le_centralizer _ _ _ _ _ hz)).trans
    (A.strict_point_stabilizer_in_join h611 hnatural hTH).le

/-- The actual U/Z(U)-action kernel on X is exactly E. In particular it
satisfies the source kernel formula of 6.2.17(6). -/
theorem LocalAnalysis.strict_crossing_action_kernel
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G)) :
    strictCrossingGroup (T : Subgroup G) L R z d ⊓
      (strictQuotientAction (T : Subgroup G) L R z).ker.map (centralizer ({z} : Set G)).subtype =
      strictCrossingIntersection (T : Subgroup G) L R z d := by
  let U := sourceClosure (T : Subgroup G) L R z
  let N := (strictQuotientAction (T : Subgroup G) L R z).ker.map (centralizer ({z} : Set G)).subtype
  let R₀ := (T : Subgroup G) ⊓ N
  let F := commutatorPreimage U R₀ (zpowers z)
  let C := (center U).map U.subtype
  have hFC : F ⊔ C = U := A.strict_fixed_lift_sup_center h611 hnatural hz horder hTH
  have hnot : ¬ F ≤ centralizer (ZS (T : Subgroup G) L R : Set G) := by
    intro hF
    have hC : C ≤ centralizer (ZS (T : Subgroup G) L R : Set G) := by
      rintro c ⟨c, hc, rfl⟩ s hs
      exact congrArg Subtype.val (mem_center_iff.mp hc ⟨s, (hstrict.le hs).1⟩)
    have hU : U ≤ centralizer (ZS (T : Subgroup G) L R : Set G) :=
      hFC ▸ sup_le hF hC
    apply A.strict_closure_noncommutative h611 hnatural hz horder hstrict
    rw [strict_sourceClosure_eq_span h611 hz]
    apply (conjugateSpanBy_commutative_iff _ _).mpr
    change sourceClosure (T : Subgroup G) L R z ≤ _ at hU
    rw [strict_sourceClosure_eq_span h611 hz] at hU
    exact le_centralizer_iff.mp hU
  obtain ⟨u, hu, huw⟩ := SetLike.not_le_iff_exists.mp hnot
  have hUH : U ≤ centralizer ({z} : Set G) := A.closure_le_core.trans ((centralizer ({z} : Set G)).pCoreIn_le 2)
  have hUZ : U ≤ normalizer (zpowers z : Set G) := by
    apply (show U ≤ centralizer (zpowers z : Set G) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    apply le_centralizer_iff.mp
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hUH hx)
  apply le_antisymm
  · intro x hx
    have hxR : x ∈ R₀ := ⟨A.strict_crossing_le_sylow h611 hnatural hz horder hTH hstrict hdres hdH hx.1, hx.2⟩
    have hfix : ⁅x,u⁆ ∈ zpowers z := by
      rw [← commutatorElement_inv]
      exact inv_mem (commutator_commutatorPreimage_le U R₀ (zpowers z) hUZ
        (commutator_mem_commutator hu hxR))
    exact A.strict_crossing_tilde_fixed_bound h611 hnatural hz horder hTH hstrict hdres hdH
      hx.1 (commutatorPreimage_le _ _ _ hu) huw hfix
  · refine le_inf (A.strict_crossing_le_group h611 hnatural hz horder hstrict
        (((map_subtype_le _) hdres).2) hdH) ?_
    have hh := map_mono (f := (centralizer ({z} : Set G)).subtype)
      (A.strict_closure_le_dotted_kernel h611 hnatural hz horder hstrict)
    rw [map_subgroupOf_eq_of_le hUH] at hh
    exact inf_le_left.trans hh

/-- The first-isomorphism identification for the actual crossing actor,
with the original H-quotient map on every representative. -/
theorem LocalAnalysis.strict_crossing_quotient_equiv
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G)) :
    let X := strictCrossingGroup (T : Subgroup G) L R z d
    let E := strictCrossingIntersection (T : Subgroup G) L R z d
    ∃ hN : (E.subgroupOf X).Normal,
      let := hN
      ∃ e : (X ⧸ E.subgroupOf X) ≃* strictCrossingImage (T : Subgroup G) L R z d,
        ∀ x : X, (e (QuotientGroup.mk' (E.subgroupOf X) x) : StrictActor (T : Subgroup G) L R z) =
          QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
            ⟨x, strictCrossingGroup_le_centralizer _ _ _ _ _ hz x.property⟩ := by
  let H := centralizer ({z} : Set G)
  let K := (strictQuotientAction (T : Subgroup G) L R z).ker
  let X := strictCrossingGroup (T : Subgroup G) L R z d
  let E := strictCrossingIntersection (T : Subgroup G) L R z d
  let i : X →* H := inclusion (strictCrossingGroup_le_centralizer _ _ _ _ _ hz)
  let f := (QuotientGroup.mk' K).comp i
  have hker : f.ker = E.subgroupOf X := by
    ext x
    change QuotientGroup.mk' K (i x) = 1 ↔ (x : G) ∈ E
    change ((i x : H) : H ⧸ K) = 1 ↔ (x : G) ∈ E
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact (A.strict_crossing_action_kernel h611 hnatural hz horder hTH hstrict hdres hdH).le
        ⟨x.property, mem_map_of_mem H.subtype hx⟩
    · intro hx
      obtain ⟨y, hy, he⟩ := ((A.strict_crossing_action_kernel h611 hnatural hz horder hTH hstrict hdres hdH).ge hx).2
      exact (Subtype.ext he : y = i x) ▸ hy
  have hrange : f.range = strictCrossingImage (T : Subgroup G) L R z d := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨i x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hN : (E.subgroupOf X).Normal := hker ▸ inferInstance
  let := hN
  let e : (X ⧸ E.subgroupOf X) ≃* strictCrossingImage (T : Subgroup G) L R z d :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
  exact ⟨hN, e, fun _ => rfl⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
