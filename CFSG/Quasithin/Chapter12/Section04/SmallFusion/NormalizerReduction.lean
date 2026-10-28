module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeFusion
public import Theory.GroupTheory.FourGroupNormalizerIndex
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.FixedSupplementCentralizer
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.IndexNormal

/-!
# Normalizer reductions in the small SL₃ extension

The fixed-supplement calculation gives the whole product Ω₁(Z(Q))=ZV
and [Z,L]=1, with Q=C_T(V) in the statements below. The earlier source
identification Q=O₂(LT) is not asserted here. Centralizing R=C_T(E) then gives Ω₁(Z(R))=ZE. In the
escaping-normalizer branch, source 1.2.7 gives disjoint conjugates of Z;
the hyperplane order argument forces Z=C_V(L) and E=Ω₁(Z(R)). The
normalizer action on E gives |N_G(R):N_M(R)|=3. The characteristic condition
needed for the MS-pair is also proved with normality relative to LR.

In the other branch, Sylow promotion supplies the actual ambient centralizer
witness to the completed SL₃ fusion and literal 12.4.9 consumers.

These are conditional reductions. The fixed-supplement/plane calculations,
the local Sylow witness and its index, and the B.4 commutator geometry are
still explicit. Their construction from the universal earlier source inputs,
the remainder of 12.4.6 and the G₂ branch remain with the SmallFusion owner.
No claim here is a completed proof of the full source family.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
12.4.5--7, printed pp.813--814, and 12.4.9, printed p.816.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
set_option linter.style.haveILetI false
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The two omega identities in 12.4.5--6, after the earlier module
calculations supply their fixed supplement and fixed plane. This is a
reduction, not an assertion of those outstanding module calculations. -/
theorem omega_center_of_fixed_supplement
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (E : Subgroup G) (hEV : E ≤ V)
    (hsplit : omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔ V)
    (hfixed : omegaCenterIn (T : Subgroup G) ⊓ V ≤ centralizer (L : Set G))
    (hplane : V ⊓ centralizer (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G) = E) :
    omegaCenterIn (T : Subgroup G) ≤ centralizer (L : Set G) ∧
    omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
      omegaCenterIn (T : Subgroup G) ⊔ V ∧
    omegaCenterIn ((T : Subgroup G) ⊓ centralizer (E : Set G)) =
      omegaCenterIn (T : Subgroup G) ⊔ E := by
  let _ := D.elementary
  let Z := omegaCenterIn (T : Subgroup G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let R := (T : Subgroup G) ⊓ centralizer (E : Set G)
  have hZC : Z ≤ centralizer ((T : Subgroup G) : Set G) :=
    fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  have hZV := hZC.trans (centralizer_le D.le_sylow)
  have hZU : Z ≤ omegaCenterIn Q := by
    intro x hx
    obtain ⟨hxT,_,hs⟩ := (mem_omegaCenterIn_iff _ _).mp hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨⟨hxT,hZV hx⟩, centralizer_le inf_le_left (hZC hx), hs⟩
  have hsplit' := centralizes_of_fixed_supplement Z V L (omegaCenterIn Q)
    hZU (hZV.trans (Subgroup.centralizer_le_normalizer _)) hsplit hfixed
  have hQR : Q ≤ R := inf_le_inf_left _ (centralizer_le hEV)
  have hVR : V ≤ R := le_inf D.le_sylow
    (V.le_centralizer.trans (centralizer_le hEV))
  have hcenter : centerIn R ≤ Q := le_inf
    (inf_le_left.trans inf_le_left)
    (inf_le_right.trans (centralizer_le hVR))
  have hR : omegaCenterIn R = Z ⊔ E := by
    rw [omegaCenterIn_eq_inf_of_center_le Q R hQR hcenter, hsplit'.1,
      inf_centralizer_sup_of_centralizing Z V R
        (hZV.trans (Subgroup.centralizer_le_normalizer _)) (hZC.trans (centralizer_le inf_le_left)),
      hplane]
  exact ⟨hsplit'.2,hsplit'.1,hR⟩

/-- The escaping-normalizer reduction of 12.4.6. Its additional hypotheses
are exactly the still-needed earlier fixed-supplement and plane calculations;
it does not assume either the global Sylow conclusion or fusion. -/
theorem escaping_normalizer_four_group
    {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (marked : SLThreeAlternative1222 K)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (E : Subgroup G) (hEV : E ≤ V) (hfour : Nat.card E = 4)
    (hsplit : omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔ V)
    (hfixed : omegaCenterIn (T : Subgroup G) ⊓ V = fixedSubgroup L V)
    (hplane : V ⊓ centralizer (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G) = E)
    (hindex : ((T : Subgroup G) ⊓ centralizer (E : Set G)).relIndex T = 2)
    (hescape : ¬ normalizer (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    omegaCenterIn (T : Subgroup G) = fixedSubgroup L V ∧
    Nat.card (omegaCenterIn (T : Subgroup G)) = 2 ∧
    E = omegaCenterIn ((T : Subgroup G) ⊓ centralizer (E : Set G)) ∧
    normalizer (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G) ≤ normalizer (E : Set G) ∧
    ((normalizer (L : Set G)) ⊓ normalizer
      (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G)).relIndex
      (normalizer (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G)) = 3 := by
  let Z := omegaCenterIn (T : Subgroup G)
  let R := (T : Subgroup G) ⊓ centralizer (E : Set G)
  let N := normalizer (R : Set G)
  let M := normalizer (L : Set G)
  obtain ⟨hc,z,hz,hgen,hM,_,hzZ,_⟩ := exists_slThree_fixed_involution_setup
    h D structural marked earlier hmodel hne
  have hzZ' : z ∈ Z := by
    change z ∈ omegaCenterIn (T : Subgroup G)
    rwa [omegaCenterIn_eq_omegaOneAmbient]
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hzF : z ∈ fixedSubgroup L V := hgen ▸ mem_zpowers z
  have hZfacts := omega_center_of_fixed_supplement D E hEV hsplit
    (hfixed.le.trans inf_le_right) hplane
  have hZL : Z ≤ centralizer (L : Set G) := hZfacts.1
  have hRsplit : omegaCenterIn R = Z ⊔ E := hZfacts.2.2
  have hZC : Z ≤ centralizer ((T : Subgroup G) : Set G) :=
    fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  have hzE : z ∈ E := hplane.le ⟨hzF.1, centralizer_le inf_le_left (hZC hzZ')⟩
  have hFZ : fixedSubgroup L V ≤ Z := by
    rw [hgen]
    exact zpowers_le_of_mem hzZ'
  have hFE : fixedSubgroup L V ≤ E := by
    rw [hgen]
    exact zpowers_le_of_mem hzE
  have hZE : Z ⊓ E = fixedSubgroup L V := le_antisymm
    ((inf_le_inf_left _ hEV).trans hfixed.le) (le_inf hFZ hFE)
  have hZnorm : E ≤ normalizer (Z : Set G) :=
    (le_centralizer_iff.mp (hZC.trans (centralizer_le (hEV.trans D.le_sylow)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes Z E hZnorm
  rw [hZE,hfour,hc] at hcard
  have hmult : Nat.card (Z ⊔ E : Subgroup G) = Nat.card Z * 2 := by omega
  have hhyper : Z.relIndex (omegaCenterIn R) = 2 := by
    rw [hRsplit]
    have ht := relIndex_mul_relIndex (⊥ : Subgroup G) Z (Z ⊔ E) bot_le le_sup_left
    rw [relIndex_bot_left, relIndex_bot_left, hmult] at ht
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos ht
  have hZne : Z ≠ ⊥ := fun he => hz1 (show z ∈ (⊥ : Subgroup G) from he ▸ hzZ')
  have hNomega := normalizer_le_normalizer_omegaCenterIn R
  obtain ⟨g,hgN,hgM⟩ := SetLike.not_le_iff_exists.mp hescape
  have horbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl
      (structural G T L h).1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier earlier
    h.simpleQTKE T h.maximal_faithful.1
  have hd : Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ := by
    have hh := hu.centralizer_intersection g (by simpa only [horbit] using hgM)
    change (Z ⊓ centralizer (componentOrbit L (T : Subgroup G) : Set G)) ⊓
      (Z ⊓ centralizer (componentOrbit L (T : Subgroup G) : Set G)).map
        (MulAut.conj g).toMonoidHom = ⊥ at hh
    rw [horbit, inf_eq_left.mpr hZL] at hh
    exact hh
  have hZle : Z ≤ omegaCenterIn R := hRsplit.symm ▸ le_sup_left
  obtain ⟨hZcard,hRcard⟩ := card_eq_two_of_disjoint_conjugate_hyperplane
    Z (omegaCenterIn R) hZle hZne hhyper g (hNomega hgN) hd
  have hZF : Z = fixedSubgroup L V := (eq_of_le_of_card_ge hFZ (by rw [hZcard,hc])).symm
  have hEeq : E = omegaCenterIn R := eq_of_le_of_card_ge
    (hRsplit.symm ▸ le_sup_right) (by rw [hfour,hRcard])
  have hNE : N ≤ normalizer (E : Set G) := by rw [hEeq]; exact hNomega
  have hTN : (T : Subgroup G) ≤ N := by
    letI : (R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hindex
    exact le_normalizer_of_normal_subgroupOf (show R ≤ (T : Subgroup G) from inf_le_left)
  have hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G) :=
    (structural G T L h).1.trans hM.le
  have hi := centralizer_relIndex_eq_three_of_four T N E hTN hNE hfour z hzE hz1 hTz
    (by simpa only [← hM] using hescape)
  refine ⟨hZF,hZcard,hEeq,hNE,?_⟩
  simpa only [← hM, inf_comm] using hi

/-- The first branch of 12.4.6, with the original local Sylow retained. -/
theorem sylow_centralizer_of_normalizer_le {M R : Subgroup G} (v : G)
    (hlocal : Chapter1.IsSylowIn 2 R (M ⊓ centralizer ({v} : Set G)))
    (hnormalizer : normalizer (R : Set G) ≤ M) :
    Chapter1.IsSylowIn 2 R (centralizer ({v} : Set G)) := by
  exact exists_sylow_eq_of_relative_normalizer_le hlocal inf_le_right
    (le_inf (inf_le_right.trans hnormalizer) inf_le_left)

/-- This applies the completed fusion consumer to the normalizer-contained
branch, discharging its ambient Sylow-centralizer premise. -/
theorem slThree_fusion_of_local_sylow_normalizer
    {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (marked : SLThreeAlternative1222 K)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (v : G) (hvV : v ∈ V) (hv : v ∉ fixedSubgroup L V)
    (R : Subgroup G) (hRT : R ≤ T) (hindex : R.relIndex T = 2)
    (hlocal : Chapter1.IsSylowIn 2 R (normalizer (L : Set G) ⊓ centralizer ({v} : Set G)))
    (hnormalizer : normalizer (R : Set G) ≤ normalizer (L : Set G)) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      centralizer ({z} : Set G) ≤ normalizer (V : Set G) ∧
      (∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z) ∧
      ∀ x ∈ V, ∀ y ∈ V, IsConj x y → ∃ l ∈ L, MulAut.conj l x = y := by
  exact source_slThree_fusion h D structural marked earlier hmodel hne v hvV hv R hRT hindex
    (sylow_centralizer_of_normalizer_le v hlocal hnormalizer)

/-- The characteristic-subgroup condition needed for the MS-pair in 12.4.6.
Characteristicity is inside R, and normality is inside L R. -/
theorem characteristic_eq_bot_of_normal_in_LR
    {K : GroupClass.{u}} {T : Sylow 2 G} {L : Subgroup G}
    (h : Hypothesis1223 K T L) (structural : Structural1222 K)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (R : Subgroup G) (hRT : R ≤ T) (hindex : R.relIndex T = 2)
    (hescape : ¬ normalizer (R : Set G) ≤ normalizer (L : Set G))
    (C : Subgroup R) [C.Characteristic]
    (hCnormal : ((C.map R.subtype).subgroupOf (L ⊔ R)).Normal) : C = ⊥ := by
  by_contra hC
  have horbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl
      (structural G T L h).1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier earlier
    h.simpleQTKE T h.maximal_faithful.1
  have hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G) := by
    intro N hN hLN
    simpa only [horbit] using hu.normalizer_unique N hN hLN
  have hN := normalizer_le_normalizer_characteristic_image R C
  have hTN : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    letI : (R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hindex
    exact le_normalizer_of_normal_subgroupOf hRT
  letI := hCnormal
  have hLN : L ⊔ R ≤ normalizer (C.map R.subtype : Set G) :=
    le_normalizer_of_normal_subgroupOf ((map_subtype_le C).trans le_sup_right)
  have hRp : IsPGroup 2 R := T.isPGroup'.of_injective
    (inclusion hRT) (inclusion_injective _)
  have hCN := normalizer_le_of_unique_maximalTwoLocal hunique
    ((hRp.to_subgroup C).map R.subtype)
    (fun he => hC ((C.map_eq_bot_iff_of_injective R.subtype_injective).mp he))
    (sup_le (le_sup_left.trans hLN) (hTN.trans hN))
  exact hescape (hN.trans hCN)

/-- Literal 12.4.9 in the normalizer-contained branch. The B.4 commutator
geometry remains explicit; the global fusion and Sylow inputs are discharged. -/
theorem lemma_12_4_9_of_local_sylow_normalizer
    {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (marked : SLThreeAlternative1222 K)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (v : G) (hvV : v ∈ V) (hv : v ∉ fixedSubgroup L V)
    (R : Subgroup G) (hRT : R ≤ T) (hindex : R.relIndex T = 2)
    (hlocal : Chapter1.IsSylowIn 2 R (normalizer (L : Set G) ⊓ centralizer ({v} : Set G)))
    (hnormalizer : normalizer (R : Set G) ≤ normalizer (L : Set G))
    (g : G) (hA : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hfixed : fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆)
    (hsymmetry : (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map
      (MulAut.conj g).toMonoidHom = ⁅V, V.map (MulAut.conj g).toMonoidHom⁆)
    (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  exact lemma_12_4_9_of_slThree_sylow_centralizer
    h D structural marked earlier hmodel hne v hvV hv R hRT hindex
    (sylow_centralizer_of_normalizer_le v hlocal hnormalizer)
    g hA hfixed hsymmetry hcomm

end CFSG.Quasithin.Chapter12.Section04.SmallFusion
