module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFullSixCentralizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryAugmentationAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSixQuotient

/-!
# The guarded full A₆ centralizer quotient and its outside parabolic

The natural and augmentation actions extend to actual permutations of six
letters. The full centralizer kernel is O₂(H), so H/O₂(H) is A₆ or S₆.
The small-quotient overgroup lattice supplies the unique outside parabolic P,
with index three over the common Sylow. The literal two-residual O²(P)
fixes the same line as P, giving its S₃ quotient and fixed index two on the
full original omega center.

These are same-G,T variants of Nonsolvable/ComponentFullSixQuotient, using
the proved normalizer supplement and action kernels. The original-module
application constructs the augmentation marking and omega index; it retains
the genuine selected component and earlier-source hypotheses. No full
centralizer equality, parabolic witness or normalizer supplement is assumed.
The remaining component rows and final recognition still require assembly.
Source: Aschbacher--Smith 13.4.10(7--8), printed pp.909--910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem quotient_of_six_permutation
    (f : G →* Equiv.Perm (Fin 6)) (hf : f.ker = pCore 2 G)
    (hA : alternatingGroup (Fin 6) ≤ f.range) :
    Nonempty ((G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 6)) := by
  have hi : f.range.index = 1 ∨ f.range.index = 2 := by
    apply (Nat.dvd_prime Nat.prime_two).mp
    have hd := index_dvd_of_le hA
    rwa [alternatingGroup.index_eq_two] at hd
  let d : (G ⧸ pCore 2 G) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hf.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  rcases hi with hi | hi
  · exact Or.inr ⟨(d.trans (MulEquiv.subgroupCongr (index_eq_one.mp hi))).trans topEquiv⟩
  · have heq : alternatingGroup (Fin 6) = f.range := by
      apply eq_of_le_of_card_ge hA
      have hm := f.range.index_mul_card
      have hS6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
        simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
      rw [hS6,hi] at hm
      have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup]
        norm_num
      change Nat.card f.range ≤ Nat.card (alternatingGroup (Fin 6))
      rw [hA6]
      omega
    exact Or.inl ⟨d.trans (MulEquiv.subgroupCongr heq.symm)⟩

omit [Finite G] in
private theorem natural_six_actor_quotient
    (H K U : Subgroup G) (hKH : K ≤ H)
    (hHN : H ≤ normalizer (K : Set G))
    (hHU : H ≤ normalizer (U : Set G))
    (q : K →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
    (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : U),
      (e (U.normalizerMonoidHom ⟨k.val,(hKH.trans hHU) k.property⟩ v)).toAdd =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (q k) (e v).toAdd)
    (hker : H ⊓ centralizer (U : Set G) = H.pCoreIn 2) :
    Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨f,hf⟩ := exists_natural_six_actor H K U hHN hHU (hKH.trans hHU) q hq e he
  have faithful := BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  have hfK (k : K) : f (inclusion hKH k) = (q k).val := by
    apply faithful
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := e.surjective (Multiplicative.ofAdd v)
    have hv : (e w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hv]
    exact (hf (inclusion hKH k) w).symm.trans (he k w)
  have hk : f.ker = pCore 2 H := by
    apply map_injective H.subtype_injective
    change f.ker.map H.subtype = H.pCoreIn 2
    rw [←hker]
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x.property,?_⟩
      intro v hv
      have hh := hf x ⟨v,hv⟩
      rw [show f x = 1 from hx,map_one,Module.End.one_apply] at hh
      have hc := congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective hh))
      exact (mul_inv_eq_iff_eq_mul.mp hc).symm
    · rintro ⟨hx,hc⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      change f ⟨x,hx⟩ = 1
      apply faithful
      apply LinearMap.ext
      intro v
      obtain ⟨w,hw⟩ := e.surjective (Multiplicative.ofAdd v)
      have hv : (e w).toAdd = v := congrArg Multiplicative.toAdd hw
      have hwfix : U.normalizerMonoidHom ⟨x,hHU hx⟩ w = w := by
        apply Subtype.ext
        change x * w.val * x⁻¹ = w.val
        rw [←hc w.val w.property,mul_inv_cancel_right]
      rw [←hv,←hf,hwfix,map_one,Module.End.one_apply]
  apply quotient_of_six_permutation f hk
  intro x hx
  obtain ⟨k,hk⟩ := hq ⟨x,hx⟩
  exact ⟨inclusion hKH k,(hfK k).trans (congrArg Subtype.val hk)⟩

variable {T : Sylow 2 G} {L K V : Subgroup G}
variable {D : ChosenModule T L V}

/-- The literal two-residual fixes the same central line as its Sylow
supplement. This supplies C_Z(K_i), not just C_Z(H_i), in 13.4.7. -/
theorem escaping_residual_fixed_line_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (P : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPz : P ≤ centralizer ({z.val} : Set G)) :
    (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer ((pResidual 2 P).map P.subtype : Set G) = zpowers z.val := by
  rw [← m.central_four_fixed_of_escape_at h structural z hz1 hzT P hPz hP.1.2]
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le (map_subtype_le _)))
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hTP : (T : Subgroup G) ≤ P := hP.1.1.2
  have hs : (pResidual 2 P).map P.subtype ⊔ (T : Subgroup G) = P :=
    embedded_pResidual_sup_of_common_sylow P T (T.subtype hTP)
      (map_subgroupOf_eq_of_le hTP)
  have hc : P ≤ centralizer ({x} : Set G) := by
    rw [← hs]
    refine sup_le (fun r hr => mem_centralizer_singleton_iff.mpr (hx.2 r hr)) ?_
    exact fun t ht => mem_centralizer_singleton_iff.mpr
      (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx.1.2).2.2 t ht)
  exact fun p hp => mem_centralizer_singleton_iff.mp (hc hp)

/-- The fixed subgroup of the actual residual has index two in V∩Ω₁Z(T).
Identifying this seed with full Ω₁Z(T) remains the source 13.4.10(5) step. -/
theorem escaping_residual_fixed_index_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (P : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPz : P ≤ centralizer ({z.val} : Set G)) :
    ((V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer ((pResidual 2 P).map P.subtype : Set G)).relIndex
        (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2 := by
  rw [escaping_residual_fixed_line_at h structural m z hz1 hzT P hP hPz]
  have hle : zpowers z.val ≤ V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
    zpowers_le.mpr ⟨z.property, hzT⟩
  have hc : Nat.card (zpowers z.val) = 2 := by
    rw [Nat.card_zpowers]
    let := D.elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z.val z.property)
      (fun he => hz1 (Subtype.ext he))
  have hm : Nat.card (zpowers z.val) * (zpowers z.val).relIndex
      (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) =
        Nat.card (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact ((zpowers z.val).subgroupOf
      (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))).card_mul_index
  rw [hc, m.central_four_card_eq_four_at h structural z hz1 hzT
    (fun hh => hP.1.2 (hPz.trans hh))] at hm
  omega


/-- The ordinary component gives the literal full-centralizer quotient A₆ or S₆. -/
theorem ordinary_six_full_quotient_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    let H := centralizer ({z.val} : Set G)
    Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 6)) := by
  let H := centralizer ({z.val} : Set G)
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨DK,⟨mark⟩,_,_,_,_,_,_,_,_⟩ := ordinary_six_component_geometry_at
    h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  obtain ⟨hH,_,_,hn⟩ := ordinary_six_full_centralizer_at
    h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  have hk := (ordinary_six_full_action_kernels_at
    h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK).1
  cases mark with
  | linearThree q e he =>
    let ec := QuotientGroup.quotientMulEquivOfEq (Solvable.centralCore_eq_twoCore_of_ordinary eK)
    have hh := Nat.card_congr ((ec.symm.trans q).symm.trans eK).toEquiv
    rw [Matrix.PSL3Two.card_SL,nat_card_alternatingGroup] at hh
    norm_num at hh
  | naturalSix q e he =>
    exact natural_six_actor_quotient H K U hK.1 hHN hn
      (q.toMonoidHom.comp (QuotientGroup.mk' (centralCore K)))
      (q.surjective.comp (QuotientGroup.mk'_surjective _)) e he hk
  | coreSix mK _ =>
    have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
    have hK12 := h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
      (component_quotient_quasisimple h1332 hfK)
    obtain ⟨f,_,_,him,hker⟩ := exists_core_product_permutation_at DK mK hK12 structural eK
    change Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 6))
    rw [show H = K ⊔ (T : Subgroup G) from hH]
    apply quotient_of_six_permutation f hker
    exact him ▸ (K.subgroupOf (K ⊔ (T : Subgroup G))).map_le_range f


/-- The unique outside parabolic of the ordinary A₆ centralizer, on the full
original central seed and with the literal point residual inside M. -/
theorem ordinary_six_full_centralizer_parabolic_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let A := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
    ∃ P : Subgroup G,
      P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      P ⋖ centralizer ({z.val} : Set G) ∧ Group.IsSolvable P ∧
      A ⊔ P = centralizer ({z.val} : Set G) ∧ A ⊓ P = (T : Subgroup G) ∧
      (T : Subgroup G).relIndex P = 3 ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Z = V ⊓ Z ∧ Nat.card Z = 4 ∧
      Z ⊓ centralizer (P : Set G) = zpowers z.val ∧
      Z ⊓ centralizer ((pResidual 2 P).map P.subtype : Set G) = zpowers z.val ∧
      (Z ⊓ centralizer ((pResidual 2 P).map P.subtype : Set G)).relIndex Z = 2 ∧
      (∀ X ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        X ≤ centralizer ({z.val} : Set G) → X = P) := by
  have hM := (six_component_normalizer_supplement_at h₀ h structural modules D m h1332
    fixed hindex z hzT hzL hK hHN hKM hfK eK).2.2.1
  let H := centralizer ({z.val} : Set G)
  let A := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let := h.quasisimple
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hz1' : z ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
  obtain ⟨_,_,_,⟨eL⟩,_,_,hZ,hcard,_,_⟩ := ordinary_six_component_geometry_at
    h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  have model : Nonempty ((H ⧸ pCore 2 H) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 6)) := Or.inr (ordinary_six_full_quotient_at h₀ h structural modules D m h1332
    fixed hindex z hzT hzL hK hHN hKM hfK eK)
  have hA : A = normalizer (L : Set G) ⊓ H := by
    rw [hM]
    exact ordinary_augmentation_point_parabolic D m eL z hzT hzL
  have hAM : A ≤ normalizer (L : Set G) := hA.le.trans inf_le_left
  have hAH : A < H := lt_of_le_not_ge (hA.le.trans inf_le_right)
    (fun hh => hKM (hK.1.trans (hh.trans hAM)))
  have hTA : (T : Subgroup G) < A := lt_of_le_not_ge le_sup_right (by
    intro hh
    have hp := T.isPGroup'.to_le ((show Solvable.firstCentralizerResidual L z.val ≤ A from
      le_sup_left).trans hh)
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hd := (Solvable.firstCentralizerResidual_order_of_marking D m z hzL).2
    rw [hn] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
  obtain ⟨P,hP,hPH,hsolv,hgen,hinter,hunique⟩ := small_quotient_unique_outside T
    (normalizer (L : Set G)) H A D.sylow_normalizes_component
    (Solvable.centralizer_mem_HOver hzT hz1)
    (fun hh => hKM (hK.1.trans hh)) hTA hAH hAM model
  have hTP : (T : Subgroup G) < P := lt_of_le_of_ne hP.1.1.2 (by
    intro he
    exact hP.1.2 (he ▸ D.sylow_normalizes_component))
  have hfix := m.central_four_fixed_of_escape_at h structural z hz1' hzT P hPH.le hP.1.2
  have hres := escaping_residual_fixed_line_at h structural m z hz1' hzT P hP hPH.le
  have hi := escaping_residual_fixed_index_at h structural m z hz1' hzT P hP hPH.le
  rw [←hZ] at hfix hres hi
  have hidx := small_quotient_parabolic_index H P hTP hPH model
  have hquot := parabolic_quotient_of_four_fixed_line T P hTP.le z.val hzT hz1 hPH.le hcard hidx hi
  exact ⟨P,hP,small_quotient_parabolic_maximal H P hTP hPH model,hsolv,hgen,hinter,
    hidx,hquot,hZ,hcard,hfix,hres,hi,hunique⟩



/-- On the original fixed module, a selected ordinary-six component (also
constructed when the selected module has a fixed vector) gives the full
centralizer, its exact kernels, quotient and unique outside S₃ parabolic.
The augmentation marking, index two and both normalizer supplements are proved. -/
theorem original_six_component_full_centralizer_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hrow : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∨
      (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
        Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let H := centralizer ({z.val} : Set G)
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := ⁅conjugateSpanBy Z K,K⁆
    let A := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      normalizer (V : Set G) = L ⊔ (T : Subgroup G) ∧
      H = K ⊔ (T : Subgroup G) ∧
      ⁅conjugateSpanBy Z H,K⁆ = U ∧
      conjugateSpanBy Z H = conjugateSpanBy Z K ∧
      H ⊓ centralizer (U : Set G) = H.pCoreIn 2 ∧
      H ⊓ centralizer (conjugateSpanBy Z H : Set G) = H.pCoreIn 2 ∧
      (Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∨
        Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 6))) ∧
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ⋖ H ∧ Group.IsSolvable P ∧
        A ⊔ P = H ∧ A ⊓ P = (T : Subgroup G) ∧
        (T : Subgroup G).relIndex P = 3 ∧
        Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
        Z = V ⊓ Z ∧ Nat.card Z = 4 ∧
        Z ⊓ centralizer (P : Set G) = zpowers z.val ∧
        Z ⊓ centralizer ((pResidual 2 P).map P.subtype : Set G) = zpowers z.val ∧
        (Z ⊓ centralizer ((pResidual 2 P).map P.subtype : Set G)).relIndex Z = 2 ∧
        (∀ X ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
          X ≤ H → X = P) := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  have hindex := original_omega_fixed_index_at h₀ h structural D m earlier
  have heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
    rcases hrow with heK | hfixedK
    · exact heK
    · exact ordinary_component_of_source_fixed_at h₀ h structural D m h1332 fixed
        hindex z hzT hzL hK hHN hKM hfK hfixedK
  obtain ⟨eK⟩ := heK
  obtain ⟨hL,_,hM,hV⟩ := six_component_normalizer_supplement_at h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  obtain ⟨hH,hQ,hW,_⟩ := ordinary_six_full_centralizer_at h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  obtain ⟨hUker,hWker⟩ := ordinary_six_full_action_kernels_at h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  exact ⟨hL,hM,hV,hH,hQ,hW,hUker,hWker,
    ordinary_six_full_quotient_at h₀ h structural modules
      D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK,
    ordinary_six_full_centralizer_parabolic_at h₀ h structural modules
      D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
