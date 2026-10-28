module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ResidualAlignment
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.Centralizer

/-!
# Normalizer escape for the original nonsingular residual

Assume K_v is not quasisimple and N_G(R_v) lies in M. The canonical FF
analysis gives the literal S8 quotient and makes the selected S an ambient
Sylow. Movement of the original local fixed line makes C_V(L) nontrivial.
The original Thompson argument then centralizes Ω1 Z(T), and the checked
conjugacy and alignment carry K_v to L, K_v S to LT, and L_v to itself.

The two cores of K_v S and LT have equal order under this conjugation.
Since K_v is not in M, O2(K_v S)<R_v; together with Q≤R_v this proves Q<R_v.
The full centralizer of the actual A6 image in S8 has order at most two,
so R_v fills C_LT(L_v/O2(L_v)). Its conjugate lies in that same subgroup
and has the same order. Thus the conjugator normalizes R_v, placing it in
M=N_G(L) and forcing K_v=L, a contradiction.

This completes 12.6.17 under actual nonquasisimplicity. The preferred-point
application discharges that premise when the original C_V(L) is nontrivial,
and supplies Q<R_v for 12.6.18. HS/J4 exclusions in the remaining original
branch, general canonical-module arguments, blocks, splitting and fixed-space
elimination remain; neither 12.6.2 nor 12.6.23 is asserted. Earlier invariance/TI
retain producer qt-d-1222-source; final discharge stays with qt-d-12634-source.
Source: Aschbacher--Smith, 12.6.16--18, printed pp.826--827,
combined manuscript of 1 March 2004.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem core_centralizer_eq_of_large_symmetric_image
    (f : G →* Equiv.Perm (Fin 8)) (hk : IsPGroup 2 f.ker)
    (A R : Subgroup G) [Group.IsPerfect A]
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (hKR : f.ker < R) (hRC : R ≤ coreQuotientCentralizer A) :
    coreQuotientCentralizer A = R := by
  obtain ⟨hbot,⟨a⟩⟩ :=
    Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.symmetric_six_section_image f hk A e
  have hc : (coreQuotientCentralizer A).map f ≤ centralizer (A.map f : Set (Equiv.Perm (Fin 8))) := by
    rintro _ ⟨r,hr,rfl⟩ x hx
    have hh := ((mem_coreQuotientCentralizer_iff _ _).mp
      ((mem_coreQuotientCentralizer_iff_map f A hk (coreQuotientCentralizer_le_normalizer A hr)).mp hr)).2 x hx
    have hh1 : ⁅f r,x⁆ = 1 := by
      simpa only [pCoreIn,hbot,Subgroup.map_bot,mem_bot] using hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh1).symm
  have hne : R.map f ≠ ⊥ := by
    intro he
    exact hKR.not_ge ((map_eq_bot_iff R).mp he)
  have hl : 2 ≤ Nat.card (R.map f) := ((one_lt_card_iff_ne_bot (R.map f)).mpr hne)
  have hu := Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.six_subgroup_centralizer_card_le_two
    (A.map f) a
  have he : R.map f = centralizer (A.map f : Set (Equiv.Perm (Fin 8))) :=
    eq_of_le_of_card_ge ((map_mono hRC).trans hc) (hu.trans hl)
  apply le_antisymm ?_ hRC
  rw [←comap_map_eq_self hKR.le]
  exact (le_comap_map f _).trans (comap_mono (hc.trans_eq he.symm))

variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Once K_v S is conjugate to LT, its strict two-core bound makes Q<R_v. -/
theorem SourceHypothesis.nonsingular_original_core_lt_of_conjugacy
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (g : G)
    (hJ : (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype).map
      (MulAut.conj g).toMonoidHom = LT T L) :
    Q T L < Rv T L (v : G) := by
  let P := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ P
  have hR := H.nonsingular_R_eq_Rv_of_normalizer D v hv hs hNM S hTS
  have hc := core_le_R_of_sylow L (Kv (v : G)) (v : G) S (Kv_le_Gv _)
  rw [hR] at hc
  have hcard : Nat.card (J.pCoreIn 2) = Nat.card (Q T L) := by
    have hm : (J.pCoreIn 2).map (MulAut.conj g).toMonoidHom = Q T L := by
      rw [map_pCoreIn_of_injective 2 J (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hJ]
      rfl
    exact (Nat.card_congr ((J.pCoreIn 2).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).trans (congrArg (fun W : Subgroup G => Nat.card W) hm)
  apply lt_of_le_of_ne (Q_le_Rv H.chosen v)
  intro heq
  have heq' : J.pCoreIn 2 = Rv T L (v : G) := eq_of_le_of_card_ge hc
    (by rw [←heq,hcard])
  have hn : J ≤ normalizer (J.pCoreIn 2 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  rw [heq'] at hn
  exact he ((show Kv (v : G) ≤ J from le_sup_left).trans (hn.trans hNM))

/-- The actual S8 quotient identifies the whole relative quotient centralizer. -/
theorem SourceHypothesis.nonsingular_relative_core_centralizer_eq
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (e : Star (LT T L) ≃* Equiv.Perm (Fin 8))
    (hlt : Q T L < Rv T L (v : G)) :
    LT T L ⊓ coreQuotientCentralizer (Lv L (v : G)) = Rv T L (v : G) := by
  let J := LT T L
  let A := (Lv L (v : G)).subgroupOf J
  let R₀ := (Rv T L (v : G)).subgroupOf J
  have hAJ : Lv L (v : G) ≤ J := (Lv_le_L L _).trans le_sup_left
  have hRJ : Rv T L (v : G) ≤ J := (pCoreIn_le 2 _).trans inf_le_left
  let a : A ≃* Lv L (v : G) := subgroupOfEquivOfLe hAJ
  obtain ⟨ea⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let := Lv_isPerfect_of_A6 L (v : G) ea
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hf : f.ker = pCore 2 J := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 J) x) = 1 ↔ x ∈ pCore 2 J
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hKR : f.ker < R₀ := by
    rw [hf]
    apply (map_lt_map_iff_of_injective J.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hRJ]
    exact hlt
  have hRCA : Rv T L (v : G) ≤ coreQuotientCentralizer (Lv L (v : G)) :=
    (Rv_eq_inf_coreQuotientCentralizer T L H.chosen.sylow_normalizes_component _
      (Lv_coreQuotient_center_eq_bot_of_A6 L (v : G) ea)).le.trans inf_le_right
  have hcompare (r : J) : r ∈ coreQuotientCentralizer A ↔
      (r : G) ∈ coreQuotientCentralizer (Lv L (v : G)) := by
    constructor
    · intro hr
      have hh := (mem_coreQuotientCentralizer_iff_map J.subtype A
        (IsPGroup.ker_isPGroup_of_injective J.subtype_injective)
        (coreQuotientCentralizer_le_normalizer A hr)).mp hr
      rwa [map_subgroupOf_eq_of_le hAJ] at hh
    · intro hr
      have hn : r ∈ normalizer (A : Set J) := by
        rw [←subgroupOf_normalizer_eq hAJ]
        exact coreQuotientCentralizer_le_normalizer _ hr
      apply (mem_coreQuotientCentralizer_iff_map J.subtype A
        (IsPGroup.ker_isPGroup_of_injective J.subtype_injective) hn).mpr
      rwa [map_subgroupOf_eq_of_le hAJ]
  have he := core_centralizer_eq_of_large_symmetric_image f (hf ▸ pCore_isPGroup) A R₀
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans ea) hKR
    (fun r hr => (hcompare r).mpr (hRCA hr))
  apply le_antisymm
  · intro r hr
    exact he.le ((hcompare ⟨r,hr.1⟩).mpr hr.2)
  · exact le_inf hRJ hRCA

private theorem aligned_normalizer_contradiction
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (e : Star (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ≃*
      Equiv.Perm (Fin 8))
    (g : G)
    (hK : (Kv (v : G)).map (MulAut.conj g).toMonoidHom = L)
    (hJ : (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype).map
      (MulAut.conj g).toMonoidHom = LT T L)
    (hA : (Lv L (v : G)).map (MulAut.conj g).toMonoidHom = Lv L (v : G)) : False := by
  let P := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ P
  let c := (MulAut.conj g).toMonoidHom
  let j : J ≃* LT T L := (J.equivMapOfInjective c (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr hJ)
  let eLT := (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).symm.trans e
  have hlt := H.nonsingular_original_core_lt_of_conjugacy D v hv hs he hNM S hTS g hJ
  have hC := H.nonsingular_relative_core_centralizer_eq D v hv eLT hlt
  have hR := H.nonsingular_R_eq_Rv_of_normalizer D v hv hs hNM S hTS
  have hRJ : Rv T L (v : G) ≤ J := by
    rw [←hR]
    exact inf_le_left.trans le_sup_right
  have hRC : Rv T L (v : G) ≤ coreQuotientCentralizer (Lv L (v : G)) :=
    hC.ge.trans inf_le_right
  have hmap : (Rv T L (v : G)).map c ≤ Rv T L (v : G) := by
    apply le_trans ?_ hC.le
    apply le_inf ((map_mono hRJ).trans_eq hJ)
    rintro _ ⟨r,hr,rfl⟩
    have hc := (mem_coreQuotientCentralizer_iff_map c (Lv L (v : G))
      (IsPGroup.ker_isPGroup_of_injective (MulAut.conj g).injective)
      (coreQuotientCentralizer_le_normalizer _ (hRC hr))).mp (hRC hr)
    rwa [hA] at hc
  have hfix : (Rv T L (v : G)).map c = Rv T L (v : G) :=
    eq_of_le_of_card_ge hmap (by rw [card_map_of_injective (MulAut.conj g).injective])
  have hgM : g ∈ M L := hNM (mem_normalizer_iff_map_conj_eq.mpr hfix)
  have hL : L.map c = L := mem_normalizer_iff_map_conj_eq.mp hgM
  have heq : Kv (v : G) = L := map_injective (MulAut.conj g).injective (hK.trans hL.symm)
  exact he (heq ▸ L.le_normalizer)

/-- Source 12.6.17 with only the still-required nonquasisimplicity branch explicit. -/
theorem SourceHypothesis.nonsingular_normalizer_escape_of_not_quasisimple
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L) :
    ¬ normalizer (Rv T L (v : G) : Set G) ≤ M L := by
  intro hNM
  have hz := (H.nonsingular_normalizer_local_line_moved D v hv hTV hnot hs hi he hNM).2
  have hJT := H.nonsingular_thompson_not_le_core_of_not_quasisimple D v hv hTV hnot hs hi he
  have hgen := (H.nonsingular_thompson_generation D v hv hTV hs hJT).2.2
  have hLZ := H.component_centralizes_Z_of_thompson_generation D hz hgen
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L H.chosen.sylow_normalizes_component (v : G)
  obtain ⟨_,P,hP⟩ := H.nonsingular_normalizer_ambient_sylow D v hv hTV hnot hs hi he hNM S hTS
  have hPG : (P : Subgroup G) ≤ Gv (v : G) := hP ▸ map_subtype_le _
  obtain ⟨g,hg,_,_,hK⟩ := H.nonsingular_sylow_component_conjugacy D hLZ v hv P hPG
  rw [hP] at hg
  have hJ : (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype).map
      (MulAut.conj g).toMonoidHom = LT T L := by
    rw [Subgroup.map_sup,hK,hg]
    rfl
  obtain ⟨k,hk,hkJ,hkA⟩ := H.nonsingular_aligned_conjugator D v hv hs hi _ g hK hJ
  obtain ⟨⟨e,_,_⟩,_⟩ := H.nonsingular_normalizer_symmetric_quotient D v hv hTV hnot hs hi he hNM S hTS
  exact aligned_normalizer_contradiction H D v hv hs he hNM S hTS e k hk hkJ hkA

/-- The preferred escaping point satisfies normalizer escape whenever the
original C_V(L) is nontrivial; its actual nonquasisimplicity is discharged. -/
theorem SourceHypothesis.exists_preferred_nonsingular_normalizer_escape_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
      ¬ IsQuasisimple (Kv (w : G)) ∧
      ¬ normalizer (Rv T L (w : G) : Set G) ≤ M L ∧
      Q T L < Rv T L (w : G) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,_⟩ :=
    H.exists_preferred_nonsingular_normalizer_conjugacy_of_fixed D hTV hTI hz v hv he
  have hn := H.nonsingular_normalizer_escape_of_not_quasisimple D w hw hTV hnq hs hi hnot
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,hn,lt_of_le_of_ne (Q_le_Rv H.chosen w) ?_⟩
  intro heq
  exact hn (heq ▸ H.core_normalizer_le)

end CFSG.Quasithin.Chapter12.Section06
