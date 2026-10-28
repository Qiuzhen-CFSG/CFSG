module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentPointBaumann
public import Theory.GroupTheory.PResidual.SylowCentralizer
public import CFSG.Quasithin.ChapterB.Section02.DoubledOvergroupPointBaumann
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers

/-!
# The original doubled-component radical and its Baumann subgroup

The fixed-line generator differs from a nonzero vector of the actual moved
orbit by an element centralized by all of KT. The resulting point is fixed
by the original T, and its full centralizer in KT agrees with that of the
fixed-line generator. In the ordinary-A₆ branch the previously established
reciprocal residual identity, the actual S₄ point quotient and Sylow
supplementation identify this full point centralizer with the original L₁T.

The full doubled-natural normalizer calculation then applies to O₂(L₁T),
including any multiplicity action of T. Its Thompson and Baumann subgroups
are exactly those of O₂(KT); hence its Baumann normalizer escapes N_G(L).
All quotient maps, subgroup inclusions and the original five-dimensional
augmentation marking are retained. The ordinary L quotient is explicit;
the covered-row exclusion is not asserted by this module.

This discharges the radical comparison in the doubled branch of 13.4.10(4).
The augmentation form of 13.2.2(7), remaining module-row exclusions and the
comparison, commutator and graph assembly remain with
qt-d-1341-nonsolvable-source. Earlier structural/module premises retain
final discharge with qt-d-1341-fixed-core-source. Universal nonsolvability
is still required at both escaping weight choices.

Source: Aschbacher–Smith 13.4.10(2–4), printed pp.908–909;
13.2.2(7), printed pp.877–878, supplies the next short-block alternative.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

theorem component_fixed_generator_point_overgroup
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (m.constant_mem_central_four h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer h structural D m
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
      (((mem_omegaOneCenterAmbient_iff _ _).mp (m.constant_mem_central_four h structural).2).2.2 t ht)
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


private theorem component_sylow_in_original
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
  let X := K ⊔ (T : Subgroup G)
  let N := K.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  obtain ⟨Q,hQ⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_sylow_map_eq_inf_of_normal N
  let e : N ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((Q : Subgroup N).map e.toMonoidHom).map K.subtype ≤ _
  have he : ((Q : Subgroup N).map e.toMonoidHom).map K.subtype =
      ((Q : Subgroup N).map N.subtype).map X.subtype := by
    rw [map_map,map_map]
    rfl
  rw [he,hQ]
  exact (map_mono inf_le_left).trans (by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)])


private theorem twoThree_of_two_kernel_symmetric_four
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

/-- The original L₁T is the full point centralizer inside KT, without
assuming the equality or discarding the outer action of T. -/
theorem ordinary_doubled_point_parabolic
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    ∃ w : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G),
      w ≠ 1 ∧ (T : Subgroup G) ≤ centralizer ({w.val} : Set G) ∧
      Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) =
        (K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G) := by
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  obtain ⟨w,hw,hTw,hX⟩ := component_fixed_generator_point_overgroup h₀ h structural m hzT hz1 hKz hTK hKM
  have hC : K ⊓ centralizer ({m.constant.val} : Set G) =
      K ⊓ centralizer ({w.val} : Set G) := by
    ext k
    exact ⟨fun hk => ⟨hk.1,(hX.le ⟨mem_sup_left hk.1,hk.2⟩).2⟩,
      fun hk => ⟨hk.1,(hX.ge ⟨mem_sup_left hk.1,hk.2⟩).2⟩⟩
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  obtain ⟨f,hf,hfk⟩ := BinaryLinearThree.doubled_point_centralizer_of_sylow K _
    (normalizer_commutator_ge_right _ _) eK e he w hw S (hS.trans hTw)
  have hp : IsPGroup 2 f.ker := by
    rw [hfk]
    exact (isPGroup_pCoreIn 2 K).comap_subtype
  have h23 := twoThree_of_two_kernel_symmetric_four f hf hp
  have hr := (ordinary_doubled_component_residuals h₀ h structural D m eL z hzT hzL
    hKz hHN hTK hKM eK e he).2
  rw [Solvable.firstCentralizerResidual_eq,hC,←twoResidual_eq_primeToResidual_three h23] at hr
  refine ⟨w,hw,hTw,?_⟩
  rw [←hr]
  exact embedded_pointResidual_sup_sylow T K hTK w.val hTw

/-- The Baumann group of the original O₂(L₁T) is normalized by KT. -/
theorem ordinary_doubled_original_baumann
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ ((K ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ChapterB.baumann R = ChapterB.baumann ((K ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ¬ normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let X := K ⊔ (T : Subgroup G)
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hUK : U ≤ K := (component_moved_le_twoCore h₀ hzT hz1 hKz hTK).trans (pCoreIn_le 2 K)
  have hUX : U ≤ X := hUK.trans le_sup_left
  let Ki := K.subgroupOf X
  let Ui := U.subgroupOf X
  let ek : Ki ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  let eu : Ui ≃* U := subgroupOfEquivOfLe hUX
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  let : Ui.Normal := hred.normal
  let : IsElementaryAbelian 2 Ui := hred.elementary
  let q0 := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let q := q0.comp ek.toMonoidHom
  have hq : Function.Surjective q :=
    (eK.surjective.comp (QuotientGroup.mk'_surjective _)).comp ek.surjective
  have hk : q.ker = pCore 2 Ki := by
    change q0.ker.comap ek.toMonoidHom = _
    have hq0 : q0.ker = pCore 2 K := by
      rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    rw [hq0]
    exact ek.toMonoidHom.comap_pCore_of_ker_isPGroup ek.surjective
      (IsPGroup.ker_isPGroup_of_injective ek.injective)
  let ei := eu.trans e
  have hei (k : Ki) (u : Ui) : (ei (MulAut.conjNormal k.val u)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (q k) (ei u).toAdd := by
    exact he (ek k) (eu u)
  have hquot : IsPGroup 2 (X ⧸ Ki) := by
    apply isPGroup_quotient_of_sup_eq_top Ki ((T : Subgroup G).subgroupOf X) T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup (show K ≤ X from le_sup_left) (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
  obtain ⟨w,hw,hTw,hPar⟩ := ordinary_doubled_point_parabolic h₀ h structural D m eL z hzT hzL
    hKz hHN hTK hKM eK e he
  let wi := eu.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by simpa [wi] using congrArg eu hh)
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  let Si := S.mapSurjective (f := ek.symm.toMonoidHom) ek.symm.surjective
  have hSi : (Si : Subgroup Ki).map Ki.subtype ≤ centralizer ({wi.val} : Set X) := by
    rintro x ⟨a,ha,rfl⟩
    obtain ⟨k,hk,hka⟩ := (show a ∈ (S : Subgroup K).map ek.symm.toMonoidHom from ha)
    rw [←hka]
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTw (hS (mem_map_of_mem K.subtype hk))))
  have hb := ChapterB.doubled_overgroup_point_baumann Ki Ui q hq hk ei hei hquot
    (le_centralizer_iff.mp hred.le_centralizer_pCore) wi hwi Si hSi
  let C := centralizer ({wi.val} : Set X)
  have hCm : C.map X.subtype = Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
    rw [hPar]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hm := congrArg (fun A : Subgroup X => A.map X.subtype) hb.2.1
  change (ChapterB.baumann (C.pCoreIn 2)).map X.subtype = (ChapterB.baumann (pCore 2 X)).map X.subtype at hm
  dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha] at hm
  rw [baumann_map_injective X.subtype X.subtype_injective,
    baumann_map_injective X.subtype X.subtype_injective,
    map_pCoreIn_of_injective 2 C X.subtype X.subtype_injective,hCm] at hm
  have hj := congrArg (fun A : Subgroup X => A.map X.subtype) hb.1
  change (elementaryAbelianMaxJ (C.pCoreIn 2)).map X.subtype =
    (elementaryAbelianMaxJ (pCore 2 X)).map X.subtype at hj
  rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    map_pCoreIn_of_injective 2 C X.subtype X.subtype_injective,hCm] at hj
  change ChapterB.baumann ((Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2) =
    ChapterB.baumann (X.pCoreIn 2) at hm
  refine ⟨hj,hm,?_⟩
  rw [hm]
  intro hbound
  exact hKM ((show K ≤ X from le_sup_left).trans ((X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
      ((normalizer_le_normalizer_baumann (X.pCoreIn 2)).trans hbound)))
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
