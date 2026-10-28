module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearWholeAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearMS

/-!
# The guarded linear point MS construction

Reorient the actual natural marking at the Sylow-fixed point. Its full
centralizer kernel and the original radical comparison identify R=O₂(L₁T)
inside KR. Perfection identifies O²(KR)=K. The original covered Baumann
normalizer bound excludes every nontrivial characteristic subgroup normal
in KR, supplying the genuine natural-point MS input on K Baum(R).

This retains the actual quotient maps and the five-dimensional original
augmentation module, using structural facts only at the same G,T.
ComponentLinearGeometryAt uses its intrinsic core-length bound to exclude
the original covering row. Source: Aschbacher--Smith 13.4.10(2), p.908;
C.1.37, pp.141--143.
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

open Chapter12.Section08 ChapterC.NaturalPointControl
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
theorem covered_augmentation_characteristic_normalizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (A : Subgroup G)
    (hAB : A ≤ ChapterB.baumann ((Solvable.firstCentralizerResidual L z.val ⊔
      (T : Subgroup G)).pCoreIn 2))
    (hchar : (A.subgroupOf (ChapterB.baumann ((Solvable.firstCentralizerResidual L z.val ⊔
      (T : Subgroup G)).pCoreIn 2))).Characteristic)
    (hne : A ≠ ⊥) : normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  let X := L ⊔ (T : Subgroup G)
  let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
  let B := ChapterB.baumann R
  have hb : B = ChapterB.baumann (X.pCoreIn 2) :=
    (covered_augmentation_thompson_baumann_at h structural D m hc z hzT hzL).2
  have hXB : X ≤ normalizer (B : Set G) := by
    rw [hb]
    exact (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
        (normalizer_le_normalizer_baumann (X.pCoreIn 2))
  let : (A.subgroupOf B).Characteristic := hchar
  have hBA := normalizer_le_normalizer_characteristic_image B (A.subgroupOf B)
  rw [map_subgroupOf_eq_of_le (show A ≤ B from hAB)] at hBA
  exact normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique_at structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    ((isPGroup_pCoreIn 2 _).to_le (hAB.trans inf_le_left)) hne (hXB.trans hBA)

omit [Finite G] in
private theorem natural_point_action
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (K : Subgroup G) (q : K →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (e : U ≃* Multiplicative BinaryLinearThree.Vector)
    (he : ∀ (k : K) (v : U), (e (MulAut.conjNormal k.val v)).toAdd =
      BinaryLinearThree.W (q k) (e v).toAdd)
    (hkernel : centralizer (U : Set G) = pCore 2 G)
    (w : U) (hw : w ≠ 1) :
    ∃ a : NaturalAction U, a.P = centralizer ({w.val} : Set G) := by
  have hv : (e w).toAdd ≠ 0 := fun hh => hw (e.injective (hh.trans e.map_one.symm))
  obtain ⟨g,hg⟩ := BinaryLinearThree.natural_transitive_nonzero
    (e w).toAdd Matrix.PSL3Two.flagPoint.val hv
    Matrix.PSL3Two.flagPoint.property
  let c := e.trans (slAut g)
  have hc : (c w).toAdd = Matrix.PSL3Two.flagPoint.val :=
    (slAut_apply g (e w)).trans hg
  let f : G →* MulAut U := MulAut.conjNormal
  let p : G →* BinaryLinearThree.Group := slAut.symm.toMonoidHom.comp
    ((MulAut.congr c).toMonoidHom.comp f)
  have hp (x : G) (v : U) : (c (MulAut.conjNormal x v)).toAdd =
      BinaryLinearThree.W (p x) (c v).toAdd := by
    have hh := congrArg (fun b : MulAut Model => b (c v)) (slAut.apply_symm_apply
      ((MulAut.congr c) (f x)))
    have hh' := congrArg Multiplicative.toAdd hh
    rw [slAut_apply] at hh'
    change BinaryLinearThree.W (p x) (c v).toAdd =
      (c (f x (c.symm (c v)))).toAdd at hh'
    rw [c.symm_apply_apply] at hh'
    exact hh'.symm
  have honto : Function.Surjective p := by
    intro a
    obtain ⟨k,hk⟩ := hq (g⁻¹ * a * g)
    refine ⟨k.val,?_⟩
    apply slAut.injective
    apply MulEquiv.ext
    intro v
    obtain ⟨v,rfl⟩ := c.surjective v
    apply Multiplicative.toAdd.injective
    rw [slAut_apply,slAut_apply]
    change BinaryLinearThree.W (p k.val) (c v).toAdd =
      BinaryLinearThree.W a (c v).toAdd
    rw [←hp]
    change (slAut g (e (MulAut.conjNormal k.val v))).toAdd =
      BinaryLinearThree.W a (slAut g (e v)).toAdd
    rw [slAut_apply,slAut_apply,he,hk]
    change BinaryLinearThree.W g (BinaryLinearThree.W (g⁻¹*a*g) (e v).toAdd) =
      BinaryLinearThree.W a (BinaryLinearThree.W g (e v).toAdd)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact congrArg (fun b : BinaryLinearThree.Group => BinaryLinearThree.W b (e v).toAdd)
      (by group : g * (g⁻¹ * a * g) = a * g)
  have hker : p.ker = pCore 2 G := by
    rw [←hkernel]
    ext x
    change p x = 1 ↔ x ∈ centralizer (U : Set G)
    rw [←slAut.map_eq_one_iff]
    change slAut (slAut.symm ((MulAut.congr c) (f x))) = 1 ↔ _
    rw [slAut.apply_symm_apply]
    change (MulAut.congr c) (f x) = 1 ↔ _
    rw [(MulAut.congr c).map_eq_one_iff]
    constructor
    · intro hx v hv
      have hh := congrArg (fun b : MulAut U => (b ⟨v,hv⟩).val) hx
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hx
      ext v
      change x * v.val * x⁻¹ = v.val
      rw [←hx v.val v.property,mul_inv_cancel_right]
  let a : NaturalAction U := ⟨p,honto,hker,c,hp⟩
  refine ⟨a,?_⟩
  ext x
  change p x ∈ Matrix.PSL3Two.pointParabolicSL ↔ _
  rw [←Matrix.PSL3Two.Fano.stabilizer_flagPoint_SL]
  change p x • Matrix.PSL3Two.flagPoint = Matrix.PSL3Two.flagPoint ↔ _
  rw [Subtype.ext_iff]
  change BinaryLinearThree.W (p x) Matrix.PSL3Two.flagPoint.val =
    Matrix.PSL3Two.flagPoint.val ↔ _
  rw [←hc,←hp,Multiplicative.toAdd.injective.eq_iff,c.injective.eq_iff,Subtype.ext_iff]
  change x * w.val * x⁻¹ = w.val ↔ _
  rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]

private theorem linear_point_pi
    {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : IsPiGroup twoThreePrimes A := by
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hc : Nat.card A = 24 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      Nat.card_perm,Nat.card_fin,hn]
    norm_num [Nat.factorial]
  rw [IsPiGroup_iff]
  intro p hp
  rw [hc] at hp
  change p.val = 2 ∨ p.val = 3
  have he : 24 * 2 ^ n = 2 ^ (n+3) * 3 := by ring
  rw [he] at hp
  rcases p.property.dvd_mul.mp hp with h2 | h3
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
variable {T : Sylow 2 G} {L K V : Subgroup G}

/-- The covered original augmentation and selected natural linear-three row
construct the actual point Baumann MS pair in KR. -/
theorem covered_linear_component_ms_at
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
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    let X := K ⊔ R
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ hn : (U.subgroupOf X).Normal,
      ∃ hel : IsElementaryAbelian 2 (U.subgroupOf X),
        letI := hn
        letI := hel
        ∃ a : NaturalAction (U.subgroupOf X),
          a.R = R.subgroupOf X ∧ pResidual 2 X = K.subgroupOf X ∧
          Nonempty (ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple a.LJ a.BJ) := by
  let H := K ⊔ (T : Subgroup G)
  let P := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ R
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  have hPR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hRT : R ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 P).le_sylow_of_normalized T (le_sup_right.trans hPR)
  have hXH : X ≤ H := sup_le le_sup_left (hRT.trans le_sup_right)
  have hHX : H ≤ normalizer (X : Set G) := sup_le
    (le_sup_left.trans X.le_normalizer)
    ((le_inf hTK (le_sup_right.trans hPR)).trans (normalizer_inf_normalizer_le_normalizer_sup K R))
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  obtain ⟨DK,q,e,he,_,_,_,_⟩ := linear_component_marking_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  have hUK : U ≤ K := (component_moved_le_twoCore h₀ hzT hz1 hKz hTK).trans (pCoreIn_le 2 K)
  have hUX : U ≤ X := hUK.trans le_sup_left
  have hUH : U ≤ H := hUX.trans hXH
  have hHU : H ≤ normalizer (U : Set G) :=
    le_normalizer_of_normal_subgroupOf hUH (hK := hred.normal)
  have hC : H ⊓ centralizer (U : Set G) = H.pCoreIn 2 :=
    (chosen_linear_three_join DK (le_sup_right.trans hHU) q e he).1
  let Ui := U.subgroupOf X
  let Ki := K.subgroupOf X
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hHU)
  let := DK.elementary
  let : IsElementaryAbelian 2 Ui := IsElementaryAbelian.subgroupOf hUX
  let eu : Ui ≃* U := subgroupOfEquivOfLe hUX
  let ek : Ki ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  let qi := (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp ek.toMonoidHom
  have hqi : Function.Surjective qi := (q.surjective.comp
    (QuotientGroup.mk'_surjective _)).comp ek.surjective
  have hei (k : Ki) (v : Ui) : ((eu.trans e) (MulAut.conjNormal k.val v)).toAdd =
      BinaryLinearThree.W (qi k) ((eu.trans e) v).toAdd := he (ek k) (eu v)
  have hkernel : centralizer (Ui : Set X) = pCore 2 X := by
    apply le_antisymm
    · apply le_sSup
      refine ⟨inferInstance,?_⟩
      apply (isPGroup_pCoreIn 2 H).comap_subtype.to_le
      intro x hx
      apply hC.le
      refine ⟨hXH x.property,?_⟩
      intro v hv
      exact congrArg Subtype.val (hx ⟨v,hUX hv⟩ hv)
    · intro x hx v hv
      apply Subtype.ext
      exact (hC.ge (pCoreIn_mono_of_normalizes hXH hHX
        (mem_map_of_mem X.subtype hx))).2 v.val hv
  obtain ⟨w,hw,_,hpoint⟩ := component_fixed_generator_point_overgroup_at
    h₀ h structural m hzT hz1 hKz hTK hKM
  let wi := eu.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by simpa [wi] using congrArg eu hh)
  obtain ⟨a,ha⟩ := natural_point_action Ui Ki qi hqi (eu.trans e) hei hkernel wi hwi
  have hCm : a.P.map X.subtype = X ⊓ centralizer ({m.constant.val} : Set G) := by
    rw [ha]
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b.property,(hpoint.ge ⟨hXH b.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hb))⟩).2⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp (hpoint.le ⟨hXH hx,hc⟩).2)),rfl⟩
  obtain ⟨f,hf,hfk⟩ := BinaryLinearThree.natural_point_centralizer K U DK.normalizes q e he w hw
  have h23 : IsPiGroup twoThreePrimes (K ⊓ normalizer (L : Set G) : Subgroup G) := by
    have hKC : K ⊓ normalizer (L : Set G) = K ⊓ centralizer ({w.val} : Set G) := by
      rw [←fixed_generator_centralizer_at h structural D m
        ⟨m.constant.property,m.constant_fixed⟩ (fun hh => m.constant_ne_one (Subtype.ext hh))]
      ext k
      exact ⟨fun hk => ⟨hk.1,(hpoint.le ⟨mem_sup_left hk.1,hk.2⟩).2⟩,
        fun hk => ⟨hk.1,(hpoint.ge ⟨mem_sup_left hk.1,hk.2⟩).2⟩⟩
    rw [hKC]
    exact linear_point_pi f hf (by rw [hfk]; exact (isPGroup_pCoreIn 2 K).comap_subtype)
  have h9 : ¬ 9 ∣ Nat.card K := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    have hcard : Nat.card K = 168 * 2^n := by
      rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K),
        Nat.card_congr eK.toEquiv,Matrix.PSL3Two.card_SL,hn]
    rw [hcard]
    intro hd
    exact (by decide : ¬ 9 ∣ 168)
      (((by decide : Nat.Coprime 9 2).pow_right n).dvd_mul_right.mp hd)
  have hRm : a.R.map X.subtype = R := by
    rw [a.R_eq_parabolic_core,map_pCoreIn_of_injective 2 _ _ X.subtype_injective,hCm]
    exact covered_component_point_radical_at h structural D m hc z hzT hzL hKz hHN h23 h9
  have hR : a.R = R.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hRm,map_subgroupOf_eq_of_le (show R ≤ X from le_sup_right)]
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer (hRT.trans hTK))
  have hcomp : Ki.IsCComponent := hfK.1.1.subgroupOf_of_le (show K ≤ X from le_sup_left) hXH
  let : Group.IsPerfect Ki := hcomp.perfect
  have hperfect : IsPPerfect 2 Ki := by
    intro N hN hQ
    let := hN
    have hh : Subsingleton (Ki ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (Ki ⧸ N) hQ.isNilpotent
    apply eq_top_iff.mpr
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  have hres : pResidual 2 X = Ki :=
    pResidual_eq_of_isPPerfect_sup Ki (R.subgroupOf X) hperfect
      (isPGroup_pCoreIn 2 P).comap_subtype (by
        rw [←subgroupOf_sup (show K ≤ X from le_sup_left)
          (show R ≤ X from le_sup_right),subgroupOf_self])
  obtain ⟨_,_,_,_,hSQ⟩ := MainForward.localComponents_local_setup h₀.qtke T hfK.1
  have hSQX : IsSQTK KnownSimple.IsKnownSimple X :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hXH)).mp (hSQ.subgroup (X.subgroupOf H))
  refine ⟨inferInstance,inferInstance,a,hR,hres,?_⟩
  apply Or.resolve_left (a.characteristic_or_msInput hSQX (hres.symm ▸ hcomp))
  rintro ⟨C,hchar,hne,hn⟩
  let B := ChapterB.baumann R
  have hB : a.B.map X.subtype = B := by
    change (ChapterB.baumann a.R).map X.subtype = _
    dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha]
    rw [baumann_map_injective X.subtype X.subtype_injective,hRm]
    rfl
  let F := (C.map a.B.subtype).map X.subtype
  have hFB : F ≤ B := hB ▸ map_mono (map_subtype_le C)
  have hcharF : (F.subgroupOf B).Characteristic := by
    let eB : a.B ≃* B := (equivMapOfInjective a.B X.subtype X.subtype_injective).trans
      (MulEquiv.subgroupCongr hB)
    have hm : C.map eB.toMonoidHom = F.subgroupOf B := by
      apply map_injective B.subtype_injective
      rw [map_subgroupOf_eq_of_le hFB,map_map]
      change C.map _ = (C.map a.B.subtype).map X.subtype
      rw [map_map]
      rfl
    rw [←hm]
    apply characteristic_iff_le_comap.mpr
    intro b x hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨(MulAut.congr eB.symm b) y,
      characteristic_iff_le_comap.mp hchar (MulAut.congr eB.symm b) hy,?_⟩
    exact eB.apply_symm_apply _
  have hFne : F ≠ ⊥ := by
    intro hh
    have h1 := (map_eq_bot_iff_of_injective _ X.subtype_injective).mp hh
    exact hne ((map_eq_bot_iff_of_injective _ a.B.subtype_injective).mp h1)
  have hXN : X ≤ normalizer (F : Set G) :=
    le_normalizer_of_normal_subgroupOf (map_subtype_le _) (hK := by
      change ((C.map a.B.subtype).map X.subtype).subgroupOf X |>.Normal
      change ((C.map a.B.subtype).map X.subtype |>.comap X.subtype).Normal
      rw [comap_map_eq_self_of_injective X.subtype_injective]
      exact hn)
  exact hKM ((le_sup_left.trans hXN).trans
    (covered_augmentation_characteristic_normalizer_at h structural D m hc z hzT hzL
      F hFB hcharF hFne))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
