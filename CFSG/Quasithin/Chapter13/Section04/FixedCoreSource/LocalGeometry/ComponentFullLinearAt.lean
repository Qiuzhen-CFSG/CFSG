module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFullLinearTensorAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullLinear

/-!
# The full linear involution centralizer at the original G,T

Apply B.5 to the actual full centralizer orbit. The enlarged doubled row
is excluded, so minimality identifies the moved orbit with the constructed
natural eight. Consequently C_G(z)=KT, with its literal linear-three quotient
and unchanged seed orbit. The two-parabolic lattice supplies the unique
outside parabolic, its fixed line, solvability, intersection and generation.

ComponentLinearPairAt applies these facts to the original plane and removes
the explicit normalizer supplement using ComponentFullLinearKernelAt.
Source: Aschbacher--Smith 13.4.10(7), printed p.909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

theorem linear_full_moved_card_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Nat.card (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G))
      (centralizer ({z.val} : Set G)),K⁆ : Subgroup G) = 8 := by
  let H := centralizer ({z.val} : Set G)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let Q := ⁅conjugateSpanBy Z H,K⁆
  let A := K.subgroupOf H
  let B := Q.subgroupOf H
  let B₀ := U.subgroupOf H
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTH := Solvable.original_sylow_le_centralizer hzT
  have hTK := hTH.trans hHN
  let S := T.subtype hTH
  obtain ⟨_,hrQ,_,_,hmove,hne,hUQ,hQW,hnQ,_⟩ := component_full_orbit_at h₀ h structural
    D m hindex z hzT hzL hKz hHN hKM
  have hQH : Q ≤ H := hQW.trans (Solvable.centralizerOmegaOrbit_le hzT)
  have hUH : U ≤ H := hUQ.trans hQH
  obtain ⟨DK,q0,e0,he0,_,_,_,_⟩ := linear_component_marking_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  let : A.Normal := normal_subgroupOf_of_le_normalizer hHN
  let : B.Normal := hrQ.normal
  let : IsElementaryAbelian 2 B := hrQ.elementary
  let a := subgroupOfEquivOfLe hKz
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let b := subgroupOfEquivOfLe hQH
  let := component_quotient_quasisimple h1332 hfK
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv aq.symm
  have hcard : Nat.card (A ⧸ pCore 2 A) = 168 := by
    rw [Nat.card_congr (aq.trans eK).toEquiv,Matrix.PSL3Two.card_SL]
  have hcomp : A.IsCComponent := by
    have ht : (⊤ : Subgroup K).IsCComponent := by
      have hh := hfK.1.1.subgroupOf_of_le (le_refl K) (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)
      simpa only [subgroupOf_self] using hh
    have htA : (⊤ : Subgroup A).IsCComponent := by
      simpa only [map_top_of_surjective a.symm.toMonoidHom a.symm.surjective] using ht.map_equiv a.symm
    have hh := htA.map_subtype (inferInstance : A.Normal).isSubnormal
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    h₀.qtke.involution_centralizer_sqtk (orderOf_eq_prime
      ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1)
  have hgenA : ⁅A,elementaryAbelianMaxJ (S : Subgroup H)⁆ = A := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKz,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    change ⁅K,elementaryAbelianMaxJ (((T : Subgroup G).subgroupOf H).map H.subtype)⁆ = K
    rw [map_subgroupOf_eq_of_le hTH]
    exact component_thompson_generation_at (D := D) h₀ h structural h1332 hzT hHN hKM hfK
  have hBmove : ⁅B,A⁆ = B := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hQH,map_subgroupOf_eq_of_le hKz]
    exact hmove
  have hBne : B ≠ ⊥ := by
    intro hh
    have hm := congrArg (map H.subtype) hh
    rw [map_subgroupOf_eq_of_le hQH,Subgroup.map_bot] at hm
    exact hne hm
  rcases full_linear_reduced_component_minimal_or_double S A B hSQ hrQ hcomp hqA hcard
      hgenA hBmove hBne with hmin | ⟨qW,eW,heW⟩
  · have hB₀B : B₀ ≤ B := comap_mono hUQ
    have hn : A ≤ normalizer (B₀ : Set H) := by
      intro k hk
      apply mem_normalizer_iff.mpr
      intro v
      exact mem_normalizer_iff.mp (DK.normalizes hk) v.val
    have hB₀move : ⁅B₀,A⁆ = B₀ := by
      apply map_injective H.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hKz]
      exact component_moved_eq_commutator h₀ hzT hz1 hKz hTK
    have hB₀ne : B₀ ≠ ⊥ := by
      intro hh
      have hm := congrArg (map H.subtype) hh
      rw [map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hm
      exact DK.ne_bot hm
    have heq : B₀ = B := (hmin B₀ hB₀B hn).resolve_right (by
      intro hc
      have hh := commutator_eq_bot_iff_le_centralizer.mpr hc
      rw [hB₀move] at hh
      exact hB₀ne hh)
    have hU : U = Q := by
      have hm := congrArg (map H.subtype) heq
      change (U.subgroupOf H).map H.subtype = (Q.subgroupOf H).map H.subtype at hm
      rwa [map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hQH] at hm
    change Nat.card Q = 8
    rw [←hU,Nat.card_congr e0.toEquiv]
    change Nat.card BinaryLinearThree.Vector = 8
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  · let q := aq.symm.trans qW
    let e := b.symm.trans eW
    have he (k : K) (v : Q) :
        (e (Q.normalizerMonoidHom ⟨k.val,normalizer_commutator_ge_right _ _ k.property⟩ v)).toAdd =
          (BinaryLinearThree.W.prod BinaryLinearThree.W)
            (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd := by
      exact heW (a.symm k) (b.symm v)
    exact (linear_full_orbit_not_doubled_at hl h₀ h structural modules D m h1332 fixed hindex
      hM z hzT hzL hKz hHN hKM hfK eK q e he).elim

/-- The linear-three row has C_G(z)=KT and the original seed orbit is already full. -/
theorem linear_full_centralizer_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    let H := centralizer ({z.val} : Set G)
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    H = K ⊔ (T : Subgroup G) ∧
      conjugateSpanBy Z H = conjugateSpanBy Z K ∧
      ⁅conjugateSpanBy Z H,K⁆ = ⁅conjugateSpanBy Z K,K⁆ ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* BinaryLinearThree.Group) := by
  exact linear_full_centralizer_of_full_moved_card_le_eight_at hl h₀ h structural modules
    D m h1332 fixed hindex hM z hzT hzL hKz hHN hKM hfK eK
    (linear_full_moved_card_at hl h₀ h structural modules D m h1332 fixed hindex hM
      z hzT hzL hKz hHN hKM hfK eK).le

/-- The literal unique outside parabolic in the full linear centralizer. -/
theorem linear_full_centralizer_parabolic_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ∃ P : Subgroup G,
      P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      P < centralizer ({z.val} : Set G) ∧ Group.IsSolvable P ∧
      (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) ⊔ P =
        centralizer ({z.val} : Set G) ∧
      (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) ⊓ P =
        (T : Subgroup G) ∧
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (P : Set G) = zpowers z.val ∧
      (∀ X ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        X ≤ centralizer ({z.val} : Set G) → X = P) := by
  let H := centralizer ({z.val} : Set G)
  let A := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let := h.quasisimple
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  obtain ⟨hH,_,_,⟨q⟩⟩ := linear_full_centralizer_at hl h₀ h structural modules D m h1332
    fixed hindex hM z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨eL⟩ := ordinary_original_of_linear_component_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  have hA : A = (normalizer (L : Set G)) ⊓ H := by
    rw [hM]
    exact ordinary_augmentation_point_parabolic D m eL z hzT hzL
  have hAM : A ≤ normalizer (L : Set G) := hA.le.trans inf_le_left
  have hAH : A < H := lt_of_le_not_ge (hA.le.trans inf_le_right)
    (fun hh => hKM (hKz.trans (hh.trans hAM)))
  have hTA : (T : Subgroup G) < A := lt_of_le_not_ge le_sup_right (by
    intro hh
    have hp := T.isPGroup'.to_le ((show Solvable.firstCentralizerResidual L z.val ≤ A from
      le_sup_left).trans hh)
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hd := (Solvable.firstCentralizerResidual_order_of_marking D m z hzL).2
    rw [hn] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
  obtain ⟨P,hP,hPH,hsolv,hgen,hinter,hunique⟩ := linear_three_unique_outside T
    (normalizer (L : Set G)) H A D.sylow_normalizes_component
    (Solvable.centralizer_mem_HOver hzT hz1)
    (fun hh => hKM (hKz.trans hh)) hTA hAH hAM q
  exact ⟨P,hP,hPH,hsolv,hgen,hinter,
    m.central_four_fixed_of_escape_at h structural z (fun hh => hz1 (congrArg Subtype.val hh))
      hzT P hPH.le hP.1.2,hunique⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
