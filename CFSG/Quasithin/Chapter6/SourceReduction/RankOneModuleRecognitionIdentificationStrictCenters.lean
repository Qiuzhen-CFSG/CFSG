module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCrossingNormality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCrossingSymplectic
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore

/-!
# Crossing centers and the original fixed subgroup

The common center is normalized by the original Sylow group. Its intersection
with the central omega line is trivial because the moving conjugator displaces
that line, so the common center vanishes. Double orthogonality in the actual
commutator form gives Z(C_U(Z_S)) = Z(U) Z_S. Conjugation and the two Frattini
lines then compute Z(X), both center cuts, and C_E(X) = Z_S.

Source: Aschbacher--Smith, 6.2.17(1)--(2),(8), printed pp.689--690.
The literal quotient fixed space and full transvection action are supplied by
StrictTransvections. The strict contradiction remains with
qt-d-1222-recognition-strict-elimination; LocalAnalysis is discharged by
qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Source 6.2.17(1): the two embedded centers are disjoint. -/
theorem LocalAnalysis.strict_crossing_centers_disjoint
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdL : d ∈ L)
    (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G)) :
    Disjoint ((center (sourceClosure (T : Subgroup G) L R z)).map
      (sourceClosure (T : Subgroup G) L R z).subtype)
      (strictCrossingCenter (T : Subgroup G) L R z d) := by
  let U := sourceClosure (T : Subgroup G) L R z
  let C := (center U).map U.subtype
  let C' := strictCrossingCenter (T : Subgroup G) L R z d
  let J := C ⊓ C'
  let f := (MulAut.conj d⁻¹).toMonoidHom
  have hCH : centralizer ({z} : Set G) ≤ normalizer (C : Set G) :=
    (sourceClosure_normalized (T : Subgroup G) L R z).trans
      (normalizer_le_normalizer_characteristic_image U (center U))
  have hJC : centralizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (J : Set G) := by
    have hH : centralizer (ZS (T : Subgroup G) L R : Set G) ≤ centralizer ({z} : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr (hx z hz).symm
    exact (le_inf (hH.trans hCH)
      (strict_plane_centralizer_normalizes_crossing h611 hz hdZ).2).trans
        inf_normalizer_le_normalizer_inf
  have hJU : U ≤ normalizer (J : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro u hu x hx
    obtain ⟨c, hc, rfl⟩ := hx.1
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨u, hu⟩).symm
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) := by
    apply (le_inf hTH h611.sylow_le).trans
    rw [A.strict_plane_stabilizer_factorization h611 hnatural hz horder hstrict]
    exact sup_le hJC hJU
  have hUT : U ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (centralizer ({z} : Set G)) (T.subtype hTH)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hh
    exact A.closure_le_core.trans hh
  have hCZ : C' ⊓ layer L R = (zpowers z).map f := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural.2.1
    have hV : (layer L R).map f = layer L R :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (layer L R : Set G)).inv_mem (hm.normalizes hdL))
    change C.map f ⊓ layer L R = _
    rw [← hV, ← map_inf _ _ _ (MulAut.conj d⁻¹).injective,
      A.strict_layer_center_intersection h611 hnatural hz horder hstrict]
  have hJO : J ⊓ omegaCenterIn (T : Subgroup G) = ⊥ := by
    have hΩ : omegaCenterIn (T : Subgroup G) = zpowers z := by
      rw [omegaCenterIn_eq_omegaOneAmbient, map_center_subtype_eq_inf_centralizer]
      exact A.central_omega
    rw [hΩ]
    apply bot_unique
    have hV : zpowers z ≤ layer L R := zpowers_le.mpr hz.1
    have he : J ⊓ zpowers z ≤ zpowers z ⊓ (zpowers z).map f :=
      le_inf inf_le_right ((le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans hV)).trans_eq hCZ)
    exact he.trans_eq (disjoint_iff.mp (strict_disjoint_conjugate_line horder hd))
  apply disjoint_iff.mpr
  by_contra hne
  exact inf_omegaCenterIn_ne_bot_of_normalized_twoGroup J (T : Subgroup G)
    (inf_le_left.trans ((map_subtype_le _).trans hUT)) T.isPGroup' hTJ hne hJO

/-- Taking the perpendicular twice computes the centralizer of the hyperplane. -/
theorem strict_hyperplane_double_centralizer
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
    (hBa : B.IsAlt) (hBn : B.Nondegenerate)
    (hB : ∀ u v : sourceClosure (T : Subgroup G) L R z,
      B (strictHatElement (T : Subgroup G) L R z u)
        (strictHatElement (T : Subgroup G) L R z v) = 0 ↔ Commute u v)
    (hSU : ZS (T : Subgroup G) L R ≤ sourceClosure (T : Subgroup G) L R z) :
    let U := sourceClosure (T : Subgroup G) L R z
    let W := U ⊓ centralizer (ZS (T : Subgroup G) L R : Set G)
    U ⊓ centralizer (W : Set G) = (center U).map U.subtype ⊔ ZS (T : Subgroup G) L R := by
  let U := sourceClosure (T : Subgroup G) L R z
  let S := ZS (T : Subgroup G) L R
  let W := U ⊓ centralizer (S : Set G)
  let C := (center U).map U.subtype
  have hCC : C ≤ centralizer (U : Set G) := by
    rintro x ⟨c, hc, rfl⟩ u hu
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨u, hu⟩)
  apply le_antisymm
  · intro u hu
    have hm := (strict_hat_orthogonal_iff B hB W inf_le_left ⟨u, hu.1⟩).mpr hu.2
    rw [strict_centralizer_hat_eq_orthogonal B hB hSU,
      B.orthogonal_orthogonal hBn hBa.isRefl] at hm
    obtain ⟨s, hs, he⟩ := hm
    obtain ⟨c, hc, hec⟩ := (QuotientGroup.mk'_eq_mk' (center U)).mp he
    have hu' : (s : G) * (c : G) = u := congrArg Subtype.val hec
    rw [← hu']
    exact mul_mem (mem_sup_right hs) (mem_sup_left ⟨c, hc, rfl⟩)
  · exact sup_le (le_inf (map_subtype_le _) (hCC.trans (centralizer_le inf_le_left)))
      (le_inf hSU (le_centralizer_iff.mp (show W ≤ centralizer (S : Set G) from inf_le_right)))

/-- The hyperplane centralizer has center Z(U)Z_S in the original group. -/
theorem LocalAnalysis.strict_hyperplane_center
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    let U := sourceClosure (T : Subgroup G) L R z
    let W := U ⊓ centralizer (ZS (T : Subgroup G) L R : Set G)
    (center W).map W.subtype = (center U).map U.subtype ⊔ ZS (T : Subgroup G) L R := by
  obtain ⟨d, _, _, _, hdZ, _, hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
  obtain ⟨he, B, hBa, hBn, _, _, hB, _⟩ :=
    A.strict_crossing_symplectic_geometry h611 hnatural hz horder hstrict hdZ hdH
  let := he
  let U := sourceClosure (T : Subgroup G) L R z
  let S := ZS (T : Subgroup G) L R
  let W := U ⊓ centralizer (S : Set G)
  have hSU : S ≤ U := hstrict.le.trans inf_le_left
  have hdouble := strict_hyperplane_double_centralizer B hBa hBn hB hSU
  let := h611.ZS_elementary
  have hCW : (center U).map U.subtype ⊔ S ≤ W := by
    apply sup_le
    · refine le_inf (map_subtype_le _) ?_
      rintro c ⟨c, hc, rfl⟩ s hs
      exact congrArg Subtype.val (mem_center_iff.mp hc ⟨s, hSU hs⟩)
    · exact le_inf hSU (Subgroup.le_centralizer S)
  change (center W).map W.subtype = (center U).map U.subtype ⊔ S
  rw [map_center_subtype_eq_inf_centralizer]
  exact le_antisymm ((inf_le_inf_right _ inf_le_left).trans_eq hdouble)
    (le_inf hCW (hdouble.ge.trans inf_le_right))

/-- The original plane is generated by the two distinct Frattini lines. -/
theorem strict_plane_eq_sup_crossing_lines
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    {d : G} (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G)) :
    ZS (T : Subgroup G) L R = zpowers z ⊔ (zpowers z).map (MulAut.conj d⁻¹).toMonoidHom := by
  let S := ZS (T : Subgroup G) L R
  let f := (MulAut.conj d⁻¹).toMonoidHom
  have hZS : zpowers z ≤ S := zpowers_le.mpr hz
  have hmS : S.map f = S := mem_normalizer_iff_map_conj_eq.mp ((normalizer (S : Set G)).inv_mem hdZ)
  have hZ'S : (zpowers z).map f ≤ S := (map_mono hZS).trans_eq hmS
  let := h611.ZS_elementary
  have hn : (zpowers z).map f ≤ normalizer (zpowers z : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx t ht
    exact congrArg Subtype.val (mul_comm (⟨t, hZS ht⟩ : S) ⟨x, hZ'S hx⟩)
  apply (eq_of_le_of_card_ge (sup_le hZS hZ'S) ?_).symm
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn (strict_disjoint_conjugate_line horder hd),
    card_map_of_injective (MulAut.conj d⁻¹).injective, Nat.card_zpowers, horder,
    (h611.natural_ZS_geometry hnatural).2.1]

/-- The center of the literal crossed centralizer is Z(U)^d times the original line. -/
theorem LocalAnalysis.strict_crossing_group_center
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G)) :
    let X := strictCrossingGroup (T : Subgroup G) L R z d
    (center X).map X.subtype = strictCrossingCenter (T : Subgroup G) L R z d ⊔ zpowers z := by
  let U := sourceClosure (T : Subgroup G) L R z
  let S := ZS (T : Subgroup G) L R
  let W := U ⊓ centralizer (S : Set G)
  let f := (MulAut.conj d⁻¹).toMonoidHom
  have hmS : S.map f = S := mem_normalizer_iff_map_conj_eq.mp ((normalizer (S : Set G)).inv_mem hdZ)
  have hmC : (centralizer (S : Set G)).map f = centralizer (S : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (centralizer (S : Set G) : Set G)).inv_mem
      (normalizer_le_normalizer_centralizer S hdZ))
  have hmW : W.map f = strictCrossingGroup (T : Subgroup G) L R z d := by
    rw [map_inf _ _ _ (MulAut.conj d⁻¹).injective, hmC]
    rfl
  have hc := congrArg (fun D : Subgroup G => D.map f)
    (A.strict_hyperplane_center h611 hnatural hz horder hstrict)
  rw [map_embeddedCenter _ _ (MulAut.conj d⁻¹).injective, hmW, Subgroup.map_sup, hmS] at hc
  dsimp only
  rw [hc]
  change strictCrossingCenter (T : Subgroup G) L R z d ⊔ ZS (T : Subgroup G) L R = _
  rw [strict_plane_eq_sup_crossing_lines h611 hnatural hz horder hdZ hd]
  have hZC : zpowers z ≤ (center U).map U.subtype :=
    (A.strict_layer_center_intersection h611 hnatural hz horder hstrict).symm ▸ inf_le_left
  have hZ'C : (zpowers z).map f ≤ strictCrossingCenter (T : Subgroup G) L R z d := map_mono hZC
  exact le_antisymm (sup_le le_sup_left (sup_le le_sup_right (hZ'C.trans le_sup_left)))
    (sup_le le_sup_left (le_sup_left.trans le_sup_right))

/-- Source 6.2.17(2), after the common center has been shown trivial. -/
theorem LocalAnalysis.strict_center_intersection_crossing
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdL : d ∈ L)
    (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G)) :
    let U := sourceClosure (T : Subgroup G) L R z
    (center U).map U.subtype ⊓ U.map (MulAut.conj d⁻¹).toMonoidHom = zpowers z := by
  let U := sourceClosure (T : Subgroup G) L R z
  let C := (center U).map U.subtype
  let C' := strictCrossingCenter (T : Subgroup G) L R z d
  let U' := U.map (MulAut.conj d⁻¹).toMonoidHom
  let X := strictCrossingGroup (T : Subgroup G) L R z d
  have hdis : Disjoint C C' :=
    A.strict_crossing_centers_disjoint h611 hnatural hz horder hTH hstrict hdL hdZ hd
  have hZC : zpowers z ≤ C :=
    (A.strict_layer_center_intersection h611 hnatural hz horder hstrict).symm ▸ inf_le_left
  have hZ'C : (zpowers z).map (MulAut.conj d⁻¹).toMonoidHom ≤ C' := map_mono hZC
  have hXH := strictCrossingGroup_le_centralizer (T : Subgroup G) L R z d hz
  have hXC : X ≤ normalizer (C : Set G) := hXH.trans
    ((sourceClosure_normalized (T : Subgroup G) L R z).trans
      (normalizer_le_normalizer_characteristic_image U (center U)))
  have hp : IsPGroup 2 U' :=
    (((centralizer ({z} : Set G)).isPGroup_pCoreIn 2).to_le A.closure_le_core).map _
  let : Fact (IsPGroup 2 U') := ⟨hp⟩
  have hcent : C ⊓ U' ≤ (center X).map X.subtype := by
    intro y hy
    have hyX : y ∈ X := ⟨hy.2, by
      obtain ⟨c, hc, rfl⟩ := hy.1
      intro s hs
      exact congrArg Subtype.val (mem_center_iff.mp hc ⟨s, (hstrict.le hs).1⟩)⟩
    refine ⟨⟨y, hyX⟩, mem_center_iff.mpr ?_, rfl⟩
    intro x
    have hcC : ⁅y, (x : G)⁆ ∈ C :=
      (le_normalizer_iff_commutator_le_left.mp hXC) (commutator_mem_commutator hy.1 x.property)
    have hcPhi : ⁅y, (x : G)⁆ ∈ (frattini U').map U'.subtype := by
      refine ⟨⁅(⟨y, hy.2⟩ : U'), ⟨(x : G), x.property.1⟩⁆, ?_, rfl⟩
      exact commutator_le_frattini_of_isPGroup (p := 2)
        (commutator_mem_commutator (mem_top _) (mem_top _))
    rw [frattini_image_map _ _ (MulAut.conj d⁻¹).injective,
      (A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict).1] at hcPhi
    have hc1 : ⁅y, (x : G)⁆ = 1 := mem_bot.mp (hdis.le_bot ⟨hcC, hZ'C hcPhi⟩)
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp hc1).symm
  have hprod : C ⊓ U' ≤ C' ⊔ zpowers z :=
    hcent.trans_eq (A.strict_crossing_group_center h611 hnatural hz horder hstrict hdZ hd)
  have hZX : zpowers z ≤ X := (zpowers_le.mpr hz).trans
    ((strict_plane_le_crossing h611 hz hdZ).trans
      (A.strict_crossing_le_group h611 hnatural hz horder hstrict hdZ hd))
  have hn : zpowers z ≤ normalizer (C' : Set G) :=
    (hZX.trans inf_le_right).trans (strict_plane_centralizer_normalizes_crossing h611 hz hdZ).2
  apply le_antisymm
  · intro y hy
    have hyprod : y ∈ (C' : Set G) * (zpowers z : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left C' (zpowers z) hn]
      exact hprod hy
    obtain ⟨c, hc, t, ht, rfl⟩ := hyprod
    have hcC : c ∈ C := (C.mul_mem_cancel_right (hZC ht)).mp hy.1
    have hc1 : c = 1 := mem_bot.mp (hdis.le_bot ⟨hcC, hc⟩)
    change c * t ∈ zpowers z
    rw [hc1, one_mul]
    exact ht
  · exact le_inf hZC (hZX.trans inf_le_left)

/-- The symmetric center cut retains the right-conjugation convention. -/
theorem LocalAnalysis.strict_crossing_center_intersection
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdL : d ∈ L)
    (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G)) :
    strictCrossingCenter (T : Subgroup G) L R z d ⊓ sourceClosure (T : Subgroup G) L R z =
      (zpowers z).map (MulAut.conj d⁻¹).toMonoidHom := by
  let U := sourceClosure (T : Subgroup G) L R z
  let C := (center U).map U.subtype
  let f := (MulAut.conj d⁻¹).toMonoidHom
  have hdinv : d⁻¹ ∉ centralizer ({z} : Set G) := by
    simpa only [inv_mem_iff] using hd
  have hcut := A.strict_center_intersection_crossing h611 hnatural hz horder hTH hstrict
    (L.inv_mem hdL) ((normalizer (ZS (T : Subgroup G) L R : Set G)).inv_mem hdZ) hdinv
  apply le_antisymm
  · rintro y ⟨⟨c, hc, rfl⟩, hy⟩
    apply mem_map_of_mem
    apply hcut.le
    refine ⟨hc, f c, hy, ?_⟩
    simp only [f, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    group
  · have hZC : zpowers z ≤ C :=
      (A.strict_layer_center_intersection h611 hnatural hz horder hstrict).symm ▸ inf_le_left
    have hS : (ZS (T : Subgroup G) L R).map f = ZS (T : Subgroup G) L R :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (ZS (T : Subgroup G) L R : Set G)).inv_mem hdZ)
    exact le_inf (map_mono hZC) (((map_mono (zpowers_le.mpr hz)).trans_eq hS).trans
      (hstrict.le.trans inf_le_left))

/-- The crossed centralizer centralizes exactly the original plane in E. -/
theorem LocalAnalysis.strict_crossing_fixed_subgroup
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdL : d ∈ L)
    (hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G))
    (hd : d ∉ centralizer ({z} : Set G)) :
    strictCrossingIntersection (T : Subgroup G) L R z d ⊓
      centralizer (strictCrossingGroup (T : Subgroup G) L R z d : Set G) =
      ZS (T : Subgroup G) L R := by
  let U := sourceClosure (T : Subgroup G) L R z
  let C' := strictCrossingCenter (T : Subgroup G) L R z d
  let X := strictCrossingGroup (T : Subgroup G) L R z d
  let E := strictCrossingIntersection (T : Subgroup G) L R z d
  have hEX := A.strict_crossing_le_group h611 hnatural hz horder hstrict hdZ hd
  have hZX : zpowers z ≤ X := (zpowers_le.mpr hz).trans
    ((strict_plane_le_crossing h611 hz hdZ).trans hEX)
  have hn : zpowers z ≤ normalizer (C' : Set G) :=
    (hZX.trans inf_le_right).trans (strict_plane_centralizer_normalizes_crossing h611 hz hdZ).2
  apply le_antisymm
  · intro y hy
    have hycenter : y ∈ (center X).map X.subtype := by
      rw [map_center_subtype_eq_inf_centralizer]
      exact ⟨hEX hy.1, hy.2⟩
    rw [A.strict_crossing_group_center h611 hnatural hz horder hstrict hdZ hd] at hycenter
    have hyprod : y ∈ (C' : Set G) * (zpowers z : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left C' (zpowers z) hn]
      exact hycenter
    obtain ⟨c, hc, t, ht, rfl⟩ := hyprod
    have htU : t ∈ U := (hstrict.le (zpowers_le.mpr hz ht)).1
    have hcU : c ∈ U := (U.mul_mem_cancel_right htU).mp hy.1.1
    have hcline := (A.strict_crossing_center_intersection h611 hnatural hz horder hTH hstrict hdL hdZ hd).le ⟨hc, hcU⟩
    rw [strict_plane_eq_sup_crossing_lines h611 hnatural hz horder hdZ hd]
    exact mul_mem (mem_sup_right hcline) (mem_sup_left ht)
  · exact le_inf (strict_plane_le_crossing h611 hz hdZ)
      (le_centralizer_iff.mp (show X ≤ centralizer (ZS (T : Subgroup G) L R : Set G) from inf_le_right))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
