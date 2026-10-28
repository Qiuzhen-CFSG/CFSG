module
public import Theory.GroupTheory.ReducedNormal.SylowMovedPlane
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalAmalgam

/-!
# The full central seed and the two source fixed indices

The original Thompson span I moves a plane in the reduced orbit V_H.
The Sylow averaging bound gives |Ω₁Z(T)| ≤ 2|C_{Ω₁Z(T)}(I)|. Maximal
normalizer uniqueness and the earlier index-two fixed subgroup identify
C_{Ω₁Z(T)}(I) with ⟨z⟩. The marked fixed line and escaping z already give
four elements in V∩Ω₁Z(T), so this exhausts the full omega-center.

Consequently C_Z(IT)=C_Z(O²(IT))=⟨z⟩ and both have index two in Z.
The original L₂ fixed-subgroup input gives C_Z(L₂T)=C_V(L), also of index
two, and distinguishes the two parabolics. This discharges13.4.7(b) on the
literal source groups before assuming any amalgam conclusion.
The endpoints construct movement and escape from the checked original-R₁
product, retaining the genuine universal Structural1222 premise and earlier
13.3.9/13.4.2–3 inputs. Their final discharge remains with
qt-d-1341-fixed-core-source. The chief-factor condition, H₀ quotient,
C₃ geometry and ambient fusion remain with qt-d-1341-solvable-source.
The elementary fixed-line argument is also used in Nonsolvable/CentralSeed;
this proof keeps the solvable imports independent of its model calculations.
Source: Aschbacher–Smith13.4.7(b) and13.4.9, printed pp.899 and906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Transport the moved-plane seed bound through the literal centralizer inclusion. -/
theorem centralizer_omega_card_le_twice_thompson_fixed
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hrank : Representation.BinaryOffender.rank
      (⁅centralizerOmegaOrbit T z,
        conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))⁆ : Subgroup G) = 2) :
    Nat.card (omegaOneCenterAmbient (T : Subgroup G)) ≤ 2 *
      Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓
        centralizer (conjugateSpanBy (elementaryAbelianMaxJ R)
          (centralizer ({z} : Set G)) : Set G) : Subgroup G) := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  let S := T.subtype (original_sylow_le_centralizer hz)
  let A := (elementaryAbelianMaxJ R).subgroupOf H
  let N := conjugateSpanBy A ⊤
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let := hU.elementary
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hRH : R ≤ H := hRT.trans hTH
  have hAH : elementaryAbelianMaxJ R ≤ H :=
    (sSup_le fun _ hA => hA.1).trans hRH
  have hAS : A ≤ S := fun _ ha => hRT ((show elementaryAbelianMaxJ R ≤ R from sSup_le fun _ hA => hA.1) ha)
  have hUS : U ≤ S := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)
  have hSmap : (S : Subgroup H).map H.subtype = (T : Subgroup G) := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
  have hZmap : (omegaOneCenterAmbient (S : Subgroup H)).map H.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,hSmap]
  have hZU : omegaOneCenterAmbient (S : Subgroup H) ≤ U := by
    intro a ha
    exact le_conjugateSpanBy _ _ (hZmap ▸ mem_map_of_mem H.subtype ha)
  have hNmap : N.map H.subtype =
      conjugateSpanBy (elementaryAbelianMaxJ R) H := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hAH,
      ← MonoidHom.range_eq_map,range_subtype]
  have hWmap : (⁅U,N⁆ : Subgroup H).map H.subtype =
      ⁅centralizerOmegaOrbit T z,conjugateSpanBy (elementaryAbelianMaxJ R) H⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le (centralizerOmegaOrbit_le hz),hNmap]
  let W := ⁅U,N⁆
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion (commutator_le_left U N)) (inclusion_injective _)
  have hcard : Nat.card W = 4 := by
    have hr : Nat.log 2 (Nat.card W) = 2 := by
      change Nat.log 2 _ = 2 at hrank
      rw [← hWmap,card_map_of_injective H.subtype_injective] at hrank
      exact hrank
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn,Nat.log_pow Nat.one_lt_two] at hr
    rw [hn,hr]
    rfl
  have hb := hU.omegaCenter_card_le_twice_fixed_of_moved_plane U S hUS hZU A hAS hcard
  have hCmap := map_inf_centralizer_of_injective H.subtype H.subtype_injective
    (omegaOneCenterAmbient (S : Subgroup H)) N
  rw [hZmap,hNmap] at hCmap
  rw [hCmap,← hZmap,card_map_of_injective H.subtype_injective,
    card_map_of_injective H.subtype_injective]
  exact hb

private theorem thompson_full_fixed_line
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (z : G) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup G) (hKz : K ≤ centralizer ({z} : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) = zpowers z := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have zero (a : G) (haZ : a ∈ Z) (haL : a ∈ centralizer (L : Set G))
      (haK : a ∈ centralizer (K : Set G)) : a = 1 := by
    by_contra ha1
    apply hKM
    apply le_trans ?_ (Solvable.omega_fixed_generator_centralizer_le_normalizer
      h structural haZ haL ha1)
    exact fun k hk => mem_centralizer_singleton_iff.mpr (haK k hk)
  have hzK : z ∈ centralizer (K : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.mp (hKz hk)
  have hzL : z ∉ centralizer (L : Set G) := fun hzL => hz1 (zero z hzT hzL hzK)
  have hzfix : z ∈ omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) :=
    ⟨hzT,hzK⟩
  apply le_antisymm ?_ (zpowers_le.mpr hzfix)
  intro a ha
  by_cases haL : a ∈ centralizer (L : Set G)
  · rw [zero a ha.1 haL ha.2]
    exact one_mem _
  · let F := (Z ⊓ centralizer (L : Set G)).subgroupOf Z
    have haF : (⟨a,ha.1⟩ : Z) ∉ F := fun hh => haL hh.2
    have hzF : (⟨z,hzT⟩ : Z) ∉ F := fun hh => hzL hh.2
    have hazL : a * z ∈ centralizer (L : Set G) :=
      ((F.mul_mem_iff_of_index_two hindex (a := ⟨a,ha.1⟩) (b := ⟨z,hzT⟩)).mpr
        (by simp only [haF,hzF])).2
    have haz : a * z = 1 := zero (a*z) (Z.mul_mem ha.1 hzT) hazL
      ((centralizer (K : Set G)).mul_mem ha.2 hzK)
    have hae : a = z⁻¹ := eq_inv_of_mul_eq_one_left haz
    rw [hae]
    exact inv_mem (mem_zpowers z)


omit [Finite G] in
/-- Adjoining the original Sylow subgroup does not alter the fixed part of its center. -/
private theorem omega_fixed_join_sylow (K : Subgroup G) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓
        centralizer ((K ⊔ (T : Subgroup G) : Subgroup G) : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) := by
  apply le_antisymm (inf_le_inf_left _
    (centralizer_le (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)))
  intro a ha
  refine ⟨ha.1,?_⟩
  have hc : K ⊔ (T : Subgroup G) ≤ centralizer ({a} : Set G) := by
    refine sup_le (fun k hk => mem_centralizer_singleton_iff.mpr (ha.2 k hk)) ?_
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp ha.1).2.2 t ht)
  exact fun k hk => mem_centralizer_singleton_iff.mp (hc hk)

/-- The actual two-residual and its Sylow supplement fix the same full central seed. -/
private theorem omega_fixed_residual (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓
        centralizer ((pResidual 2 P).map P.subtype : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G) := by
  have he : (pResidual 2 P).map P.subtype ⊔ (T : Subgroup G) = P := by
    have hh := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTP))
    rwa [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP,
      ← MonoidHom.range_eq_map,range_subtype] at hh
  conv_rhs => rw [←he]
  exact (omega_fixed_join_sylow _).symm

/-- The original moved plane and escaping Thompson span determine the entire central seed. -/
theorem full_seed_of_thompson_plane
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (R : Subgroup G) (hRT : R ≤ T)
    (hIM : ¬ conjugateSpanBy (elementaryAbelianMaxJ R)
      (centralizer ({z.val} : Set G)) ≤ normalizer (L : Set G))
    (hrank : Representation.BinaryOffender.rank
      (⁅centralizerOmegaOrbit T z.val,
        conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z.val} : Set G))⁆ : Subgroup G) = 2) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z.val} : Set G))
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    Z = V ⊓ Z ∧ Nat.card Z = 4 ∧ Z ⊓ centralizer (I : Set G) = zpowers z.val ∧
      Z ⊓ centralizer ((I ⊔ (T : Subgroup G) : Subgroup G) : Set G) = zpowers z.val ∧
      (Z ⊓ centralizer ((I ⊔ (T : Subgroup G) : Subgroup G) : Set G)).relIndex Z = 2 := by
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans (original_sylow_le_centralizer hz)))
  have hfix : Z ⊓ centralizer (I : Set G) = zpowers z.val :=
    thompson_full_fixed_line h structural z.val hz1 hz hindex I hIH hIM
  have hline : Nat.card (zpowers z.val) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1
  have hb := centralizer_omega_card_le_twice_thompson_fixed h₀ hz hz1 R hRT hrank
  change Nat.card Z ≤ 2 * Nat.card (Z ⊓ centralizer (I : Set G) : Subgroup G) at hb
  rw [hfix,hline] at hb
  have hseedle : V ⊓ centralizer (L : Set G) ≤ V ⊓ Z :=
    le_inf inf_le_left (fixed_le_original_omegaCenter h structural D m)
  have hproper : ¬ V ⊓ Z ≤ V ⊓ centralizer (L : Set G) :=
    fun hh => hzL (hh ⟨z.property,hz⟩).2
  let F := (V ⊓ centralizer (L : Set G)).subgroupOf (V ⊓ Z)
  have hFne : F ≠ ⊤ := by
    intro he
    apply hproper
    intro a ha
    exact (show (⟨a,ha⟩ : (V ⊓ Z : Subgroup G)) ∈ F from he ▸ mem_top _)
  have hFidx : 2 ≤ F.index := F.one_lt_index_of_ne_top hFne
  have hFcard : Nat.card F = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hseedle).toEquiv).trans m.card_fixed
  have hlo : 4 ≤ Nat.card (V ⊓ Z : Subgroup G) := by
    have hc := F.card_mul_index
    rw [hFcard] at hc
    omega
  have hseed : Z = V ⊓ Z :=
    (eq_of_le_of_card_ge inf_le_right (hb.trans hlo)).symm
  have hcard : Nat.card Z = 4 := le_antisymm hb (hseed.symm ▸ hlo)
  have hpfix : Z ⊓ centralizer ((I ⊔ (T : Subgroup G) : Subgroup G) : Set G) =
      zpowers z.val := (omega_fixed_join_sylow I).trans hfix
  refine ⟨hseed,hcard,hfix,hpfix,?_⟩
  rw [hpfix]
  have hlZ : zpowers z.val ≤ Z := zpowers_le.mpr hz
  have hc := ((zpowers z.val).subgroupOf Z).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hlZ).toEquiv,hline] at hc
  change 2 * (zpowers z.val).relIndex Z = Nat.card Z at hc
  rw [hcard] at hc
  change (zpowers z.val).relIndex Z = 2
  omega

/-- The source product supplies both movement and escape on the original R₁. -/
theorem original_R1_full_seed
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    Z = V ⊓ Z ∧ Nat.card Z = 4 ∧ Z ⊓ centralizer (I : Set G) = zpowers z.val ∧
      Z ⊓ centralizer ((I ⊔ (T : Subgroup G) : Subgroup G) : Set G) = zpowers z.val ∧
      (Z ⊓ centralizer ((I ⊔ (T : Subgroup G) : Subgroup G) : Set G)).relIndex Z = 2 := by
  obtain ⟨_,_,_,hrank,_,_,_,hstar,_⟩ := centralizer_pair_quotient_of_original_R1
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  have hIM : ¬ conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m))
      (centralizer ({z.val} : Set G)) ≤ normalizer (L : Set G) := by
    intro hh
    exact hstar.1.2 (sup_le hh D.sylow_normalizes_component)
  exact full_seed_of_thompson_plane h₀ h structural D m z hz hzL hindex
    (firstFlagCore h structural D m) (firstFlagCore_local_data h structural D m z hz hzL).1
    hIM hrank

/-- Both index-two clauses of13.4.7(b), and the original residual fixed line. -/
theorem original_R1_amalgam_fixed_data
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L)
    (L₂ : Subgroup G)
    (hfixed₂ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L₂ : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
    let P := I ⊔ (T : Subgroup G)
    let K₁ := (pResidual 2 P).map P.subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    Z = V ⊓ Z ∧ Nat.card Z = 4 ∧
      Z ⊓ centralizer (K₁ : Set G) = zpowers z.val ∧
      (Z ⊓ centralizer (K₁ : Set G)).relIndex Z = 2 ∧
      Z ⊓ centralizer ((L₂ ⊔ (T : Subgroup G) : Subgroup G) : Set G) =
        V ⊓ centralizer (L : Set G) ∧
      (Z ⊓ centralizer ((L₂ ⊔ (T : Subgroup G) : Subgroup G) : Set G)).relIndex Z = 2 ∧
      P ≠ L₂ ⊔ (T : Subgroup G) := by
  obtain ⟨hseed,hcard,_,hfix,hidx⟩ := original_R1_full_seed
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
  let P := I ⊔ (T : Subgroup G)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hZV : Z ≤ V := hseed.le.trans inf_le_left
  have hfixed : Z ⊓ centralizer (L : Set G) = V ⊓ centralizer (L : Set G) :=
    le_antisymm (inf_le_inf_right _ hZV)
      (le_inf (fixed_le_original_omegaCenter h structural D m) inf_le_right)
  have hsecond := (omega_fixed_join_sylow L₂).trans hfixed₂
  have hfirst := omega_fixed_residual P (show (T : Subgroup G) ≤ P from le_sup_right)
  have hne : P ≠ L₂ ⊔ (T : Subgroup G) := by
    intro he
    have hzP : z.val ∈ Z ⊓ centralizer (P : Set G) :=
      hfix.symm ▸ mem_zpowers z.val
    rw [he,hsecond] at hzP
    exact hzL hzP.2
  refine ⟨hseed,hcard,hfirst.trans hfix,?_,hsecond.trans hfixed,?_,hne⟩
  · rw [hfirst]
    exact hidx
  · rw [hsecond]
    exact hindex

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
