module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSeedAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentRadicalBaumann

/-!
# Reciprocal component points and residuals at the original G,T

Split the actual omega orbit into its moved subgroup and its fixed part.
Project the original fixed-line generator to a nonzero point whose centralizer
in KT is unchanged and which is fixed by T. In the ordinary original row,
a cubic in this reciprocal centralizer forces L₁ into K by relative normality
in C_G(z). Restricting the prime-to-three residual then gives the literal
reciprocal identity.

These are the point and residual steps of Nonsolvable/ComponentRadicalBaumann,
ComponentLinearContainment and ComponentDoubled, with structural facts only
at the same G,T. ComponentFiveAt applies them to the actual A₅ moved module.
No normality in the ambient simple group or universal structural record is
assumed. Source: Aschbacher--Smith 13.4.10(1--2), printed pp.907--908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher NoncentralChiefRefinement
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- The ordinary original component is the literal prime-to-three residual of its normalizer. -/
theorem original_normalizer_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L := by
  let := h.quasisimple
  have hr := (h.source_normalizer_sqtk_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).stronglyQuasithin
      3 Nat.prime_three (by decide)
  exact (h.source_normalizer_component_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).map_primeToResidual_three_eq_of_quotient_alternating
      L.le_normalizer le_rfl (Or.inl rfl) eL hr

/-- Project the fixed generator to an actual T-fixed nonzero moved point, preserving its centralizer in KT. -/
theorem component_fixed_generator_point_overgroup_at
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G)) :
    ∃ w : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G),
      w ≠ 1 ∧ (T : Subgroup G) ≤ centralizer ({w.val} : Set G) ∧
      (K ⊔ (T : Subgroup G)) ⊓ centralizer ({m.constant.val} : Set G) =
        (K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z K
  let U := ⁅W,K⁆
  let C := Z ⊓ centralizer (K : Set G)
  let X := K ⊔ (T : Subgroup G)
  have hWX : W ≤ X := conjugateSpanBy_le
    ((show Z ≤ (T : Subgroup G) from fun _ hz =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans le_sup_right)
    (le_sup_left.trans X.le_normalizer)
  have hred := component_orbit_reduced h₀ hzT hz1 hKz hTK
  let := hred.elementary
  let : IsElementaryAbelian 2 W := by
    have hh : IsElementaryAbelian 2 ((W.subgroupOf X).map X.subtype) := IsElementaryAbelian.map _
    rwa [map_subgroupOf_eq_of_le hWX] at hh
  have hUW : U ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy Z K)
  have hCW : C ≤ W := inf_le_left.trans (le_conjugateSpanBy Z K)
  have hsplit : W = U ⊔ C := component_seed_split h₀ hzT hz1 hKz hTK
  have hdW : m.constant.val ∈ W := le_conjugateSpanBy _ _
    (m.constant_mem_central_four_at h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hs : U.subgroupOf W ⊔ C.subgroupOf W = ⊤ := by
    rw [←subgroupOf_sup hUW hCW,←hsplit,subgroupOf_self]
  let : (U.subgroupOf W).Normal := normal_of_isMulCommutative _
  obtain ⟨a,ha,c,hc,hac⟩ := mem_sup_of_normal_left.mp
    (show (⟨m.constant.val,hdW⟩ : W) ∈ U.subgroupOf W ⊔ C.subgroupOf W from
      hs ▸ mem_top _)
  have he : a.val * c.val = m.constant.val := congrArg Subtype.val hac
  have hCX : C ≤ centralizer (X : Set G) := by
    apply le_centralizer_iff.mpr
    refine sup_le (le_centralizer_iff.mp inf_le_right) ?_
    exact le_centralizer_iff.mp (fun _ hc => ((mem_omegaOneCenterAmbient_iff _ _).mp hc.1).2.2)
  have hdT : (T : Subgroup G) ≤ centralizer ({m.constant.val} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp (m.constant_mem_central_four_at h structural).2).2.2 t ht)
  have hcT : (T : Subgroup G) ≤ centralizer ({c.val} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hCX hc t (mem_sup_right ht))
  have haT : (T : Subgroup G) ≤ centralizer ({a.val} : Set G) := by
    intro t ht
    have hd := mem_centralizer_singleton_iff.mp (hdT ht)
    have hct := mem_centralizer_singleton_iff.mp (hcT ht)
    apply mem_centralizer_singleton_iff.mpr
    apply mul_right_cancel (b := c.val)
    simpa only [←he,mul_assoc,←hct] using hd
  refine ⟨⟨a.val,ha⟩,?_,haT,?_⟩
  · intro ha1
    have hh : a.val = 1 := congrArg Subtype.val ha1
    rw [hh,one_mul] at he
    exact hdK (he ▸ hc.2)
  · ext k
    constructor
    · rintro ⟨hk,hd⟩
      refine ⟨hk,mem_centralizer_singleton_iff.mpr ?_⟩
      have hck : k * c.val = c.val * k := hCX hc k hk
      have hh := mem_centralizer_singleton_iff.mp hd
      rw [←he] at hh
      have hh' : (k * a.val) * c.val = (a.val * k) * c.val := by
        simpa only [mul_assoc,←hck] using hh
      exact mul_right_cancel hh'
    · rintro ⟨hk,ha⟩
      refine ⟨hk,mem_centralizer_singleton_iff.mpr ?_⟩
      rw [←he]
      have hck : k * c.val = c.val * k := hCX hc k hk
      calc
        k * (a.val * c.val) = (k * a.val) * c.val := (mul_assoc _ _ _).symm
        _ = (a.val * k) * c.val := by rw [mem_centralizer_singleton_iff.mp ha]
        _ = a.val * (c.val * k) := by rw [mul_assoc,hck]
        _ = (a.val * c.val) * k := (mul_assoc _ _ _).symm

/-- A reciprocal cubic forces the original L₁ into K, using normality relative to C_G(z). -/
theorem ordinary_firstResidual_le_of_reciprocal_cubic_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hthree : 3 ∣ Nat.card (K ⊓ normalizer (L : Set G) : Subgroup G)) :
    Solvable.firstCentralizerResidual L z.val ≤ K := by
  let H := centralizer ({z.val} : Set G)
  let M := normalizer (L : Set G)
  let C := L ⊓ H
  let B := K ⊓ M
  let R := (primeToResidual 3 B).map B.subtype
  have hRL : R ≤ L := by
    rw [←original_normalizer_residual_at h structural eL]
    exact embedded_primeToResidual_mono 3 inf_le_right
  have hRK : R ≤ K := (map_subtype_le _).trans inf_le_left
  have hRC : R ≤ C := le_inf hRL (hRK.trans hKz)
  have hthreeR : 3 ∣ Nat.card R := by
    rw [card_map_of_injective B.subtype_injective]
    have hd : 3 ∣ Nat.card B := hthree
    rw [←(primeToResidual 3 B).card_mul_index] at hd
    exact (Nat.prime_three.dvd_mul.mp hd).resolve_right
      (Nat.prime_three.coprime_iff_not_dvd.mp (primeToResidual_index_coprime 3))
  let N := K.subgroupOf C
  let : N.Normal := normal_subgroupOf_of_le_normalizer (inf_le_right.trans hHN)
  let f : R →* N := (inclusion hRC).codRestrict N (fun r => hRK r.property)
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : N => x.val.val) hab)
  have hthreeN : 3 ∣ Nat.card N := hthreeR.trans (card_dvd_of_injective f hf)
  have hc : IsPGroup 2 (Section08.TransvectionRecognition.Component.ModelExtension.centralCore L) := by
    rw [Solvable.centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  obtain ⟨eC⟩ := Solvable.component_centralizer_quotient D m hc z hz
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
  have hcard : Nat.card C = 2 ^ (n+1) * 3 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 C),
      Nat.card_congr eC.toEquiv,Nat.card_perm,Nat.card_fin,hn,pow_succ]
    norm_num [Nat.factorial]
    ring
  have hp : IsPGroup 2 (C ⧸ N) := by
    apply IsPGroup.of_card_dvd_pow (n := n+1)
    apply (Nat.mul_dvd_mul_iff_right (by decide : 0 < 3)).mp
    rw [←hcard,card_eq_card_quotient_mul_card_subgroup N]
    exact Nat.mul_dvd_mul_left _ hthreeN
  have hr : pResidual 2 C ≤ N := sInf_le ⟨inferInstance,hp⟩
  have he := core_component_point_twoResidual D m eL z hz
  rw [←he]
  rintro k ⟨c,hc,rfl⟩
  exact hr hc

/-- Identify the two literal prime-to-three point residuals once the original containment holds. -/
theorem component_reciprocal_residual_of_containment_at
    {D : ChosenModule T L V}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) (z : G)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hJK : Solvable.firstCentralizerResidual L z ≤ K) :
    Solvable.firstCentralizerResidual K m.constant.val =
      Solvable.firstCentralizerResidual L z := by
  let H := centralizer ({z} : Set G)
  let M := normalizer (L : Set G)
  let C := H ⊓ M
  have hr := Solvable.firstCentralizerResidual_eq_intersection_residual z
    (original_normalizer_residual_at h structural eL)
  let N := K.subgroupOf C
  let : N.Normal := normal_subgroupOf_of_le_normalizer (inf_le_left.trans hHN)
  have hRN : primeToResidual 3 C ≤ N := by
    intro c hc
    exact hJK (hr ▸ mem_map_of_mem C.subtype hc)
  have he := congrArg (map C.subtype)
    (embedded_primeToResidual_eq_of_normal 3 N hRN)
  rw [map_embedded_primeToResidual_of_hom,subgroupOf_map_subtype] at he
  have hi : K ⊓ C = K ⊓ M := le_antisymm
    (inf_le_inf_left _ inf_le_right)
    (le_inf inf_le_left (le_inf (inf_le_left.trans hKz) inf_le_right))
  rw [hi] at he
  have hd : centralizer ({m.constant.val} : Set G) = M :=
    fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))
  rw [Solvable.firstCentralizerResidual_eq,hd]
  exact he.trans hr

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
