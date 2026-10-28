module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSixCentralizer
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.TerminalSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.SmallQuotientParabolics
public import Theory.GroupTheory.CardFourAutomorphismStabilizer

/-!
# The full A₆ centralizer quotient and its outside parabolic

The natural four-space extends the component action to six-letter
permutations. Its faithful action kernel is the already identified O₂(H).
In the augmentation five-space row, the original core action gives the
same kernel on H=KT. In both cases the image contains A₆, so the literal
H/O₂(H) is A₆ or S₆. The original L/centralCore L marking is retained.

The small-quotient lattice now constructs the unique outside parabolic,
its Sylow index three, and its fixed line on the full Ω₁Z(T). To identify
its quotient as S₃, a normal Sylow would normalize the four-element seed
while fixing z. The resulting automorphism image has order at most two,
so the two-residual would centralize that seed, contradicting its fixed
line. No extra Sylow-normalizer containment is needed.

ComponentFullSixPair applies these results to the original second flag
and verifies the local join and relative residual clauses of 13.4.7.
Earlier M=LT and Chapter12/13.3 inputs remain explicit, with final discharge
at qt-d-1341-fixed-core-source. The module-weight alternatives, comparison
at both escaping weights, reciprocal commutator exclusions and graph
argument remain with qt-d-1341-nonsolvable-source. This does not complete
that contradiction or remove the separate linear row's LargeDistanceInput.

Source: Aschbacher–Smith 13.4.10(7–8), printed pp.909–910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
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

/-- An index-three parabolic fixing a nonzero point of the central four-group
has quotient S₃ when its two-residual fixes exactly a line. -/
theorem parabolic_quotient_of_four_fixed_line
    (T : Sylow 2 G) (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (z : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hPz : P ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hi : (T : Subgroup G).relIndex P = 3)
    (hfixed : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer ((pResidual 2 P).map P.subtype : Set G)).relIndex
        (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) := by
  let S := T.subtype hTP
  have hproper : pCore 2 P < (S : Subgroup P) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S) ?_
    intro he
    have hPT : P ≤ normalizer (T : Set G) := by
      have hn : P ≤ normalizer (P.pCoreIn 2 : Set G) := by
        simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
          (pCore 2 P).le_normalizer_map P.subtype
      have hc : P.pCoreIn 2 = (T : Subgroup G) := by
        change (pCore 2 P).map P.subtype = _
        rw [he,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP]
      rwa [hc] at hn
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    have hTZ : normalizer (T : Set G) ≤ normalizer (Z : Set G) := by
      let C : Subgroup (T : Subgroup G) :=
        (omega₁ (G := center (T : Subgroup G)) (p := 2)).map (center (T : Subgroup G)).subtype
      let : (omega₁ (G := center (T : Subgroup G)) (p := 2)).Characteristic :=
        omega₁_characteristic (center (T : Subgroup G))
      let : C.Characteristic := inferInstance
      exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        (T : Subgroup G) C
    let f : P →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion (hPT.trans hTZ))
    have hb : Nat.card f.range ≤ 2 := card_mulAut_subgroup_le_two_of_fixed_point hcard
      (⟨z,hz⟩ : Z) (fun hh => hz1 (congrArg Subtype.val hh)) f.range (by
        rintro _ ⟨p,rfl⟩
        apply Subtype.ext
        change p.val * z * p.val⁻¹ = z
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hPz p.property)))
    have hp : IsPGroup 2 f.range := by
      have hpos := Nat.card_pos (α := f.range)
      have hc : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by omega
      rcases hc with hc | hc
      · exact IsPGroup.of_card (n := 0) (by simpa only [pow_zero] using hc)
      · exact IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hc)
    have hr := pResidual_le_ker_of_isPGroup 2 f.rangeRestrict hp
    have hc : Z ≤ centralizer ((pResidual 2 P).map P.subtype : Set G) := by
      intro w hw
      rintro _ ⟨p,hp,rfl⟩
      have hh : f p = 1 := congrArg Subtype.val (hr hp)
      have hv := congrArg (fun a : MulAut Z => (a ⟨w,hw⟩).val) hh
      exact mul_inv_eq_iff_eq_mul.mp hv
    rw [inf_eq_left.mpr hc,relIndex_self] at hfixed
    omega
  exact sylow_index_three_core_quotient S hi hproper

variable {T : Sylow 2 G} {L K V : Subgroup G}

/-- The ordinary component gives the literal full-centralizer quotient A₆ or S₆. -/
theorem ordinary_six_full_quotient
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
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
  obtain ⟨DK,⟨mark⟩,_,_,_,_,_,_,_,_⟩ := ordinary_six_component_geometry
    h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  obtain ⟨hH,_,_,hn⟩ := ordinary_six_full_centralizer
    h₀ h structural modules D m h1332 fixed hindex hM z hzT hzL hK hHN hKM hfK eK
  have hk := (ordinary_six_full_action_kernels
    h₀ h structural modules D m h1332 fixed hindex hM z hzT hzL hK hHN hKM hfK eK).1
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
    obtain ⟨f,_,_,him,hker⟩ := exists_core_product_permutation DK mK hK12 structural eK
    change Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 6))
    rw [show H = K ⊔ (T : Subgroup G) from hH]
    apply quotient_of_six_permutation f hker
    exact him ▸ (K.subgroupOf (K ⊔ (T : Subgroup G))).map_le_range f


/-- The unique outside parabolic of the ordinary A₆ centralizer, on the full
original central seed and with the literal point residual inside M. -/
theorem ordinary_six_full_centralizer_parabolic
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
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
  let H := centralizer ({z.val} : Set G)
  let A := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let := h.quasisimple
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hz1' : z ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
  obtain ⟨_,_,_,⟨eL⟩,_,_,hZ,hcard,_,_⟩ := ordinary_six_component_geometry
    h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  have model : Nonempty ((H ⧸ pCore 2 H) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 6)) := Or.inr (ordinary_six_full_quotient h₀ h structural modules D m h1332
    fixed hindex hM z hzT hzL hK hHN hKM hfK eK)
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
  have hfix := m.central_four_fixed_of_escape h structural z hz1' hzT P hPH.le hP.1.2
  have hres := escaping_residual_fixed_line h structural m z hz1' hzT P hP hPH.le
  have hi := escaping_residual_fixed_index h structural m z hz1' hzT P hP hPH.le
  rw [←hZ] at hfix hres hi
  have hidx := small_quotient_parabolic_index H P hTP hPH model
  have hquot := parabolic_quotient_of_four_fixed_line T P hTP.le z.val hzT hz1 hPH.le hcard hidx hi
  exact ⟨P,hP,small_quotient_parabolic_maximal H P hTP hPH model,hsolv,hgen,hinter,
    hidx,hquot,hZ,hcard,hfix,hres,hi,hunique⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
