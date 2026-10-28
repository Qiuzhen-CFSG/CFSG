module

public import Theory.GroupTheory.ElementaryThompsonQuotientNormalizer
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.PerfectNormalizerLift
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
/-!
# Thompson normalizers through a component's odd central kernel

Let G = KR with K a normal C-component and R a two-subgroup. A normal
kernel containing O₂(G) and avoiding K becomes an odd subgroup of the center
of the quasisimple component in G/O₂(G). First lift Thompson normalizers
through O₂(G) ≤ R, then lift two-subgroup normalizers through the odd kernel
by Sylow conjugacy. Intersections with K lift as well. Perfectness prevents
a proper marked intersection from becoming the whole component image.

The final theorem proves the displayed normalizer restriction (*) used in
Aschbacher–Smith C.2.7, printed p.146, without assuming that the whole action
kernel lies in R. No parabolic or module classification is asserted here.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory.QuasisimpleThompson
variable {G H D : Type*} [Group G] [Finite G] [Group H] [Group D]

theorem normalizer_maxJ_two_stage (R : Subgroup G) (hR : IsPGroup 2 R)
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker ≤ R)
    (f : H →* D) (hf : Function.Surjective f)
    (hcop : Nat.Coprime 2 (Nat.card f.ker)) :
    (normalizer (elementaryAbelianMaxJ R : Set G)).map (f.comp q) =
      normalizer ((elementaryAbelianMaxJ R).map (f.comp q) : Set D) := by
  let : Finite H := Finite.of_surjective q hq
  let : Fact (IsPGroup 2 ((elementaryAbelianMaxJ R).map q)) :=
    ⟨(hR.to_le (sSup_le fun _ hA => hA.1)).map q⟩
  rw [← map_map, ← map_map, normalizer_map_maxJ R q hq hk,
    normalizer_map_eq_of_coprime_kernel 2 _ f hf hcop]

theorem normalizer_maxJ_of_odd_core_kernel (R : Subgroup G) (hR : IsPGroup 2 R)
    (f : G →* H) (hf : Function.Surjective f)
    (P : Subgroup G) [P.Normal] (hPR : P ≤ R) (hPk : P ≤ f.ker)
    (hcop : Nat.Coprime 2 (Nat.card (f.ker.map (QuotientGroup.mk' P)))) :
    (normalizer (elementaryAbelianMaxJ R : Set G)).map f =
      normalizer ((elementaryAbelianMaxJ R).map f : Set H) := by
  let q := QuotientGroup.mk' P
  let f' := QuotientGroup.lift P f hPk
  have he : f'.comp q = f := by ext; rfl
  rw [← he]
  apply normalizer_maxJ_two_stage R hR q (QuotientGroup.mk'_surjective P)
    (by simpa [q] using hPR) f' (QuotientGroup.lift_surjective_of_surjective P f hf hPk)
  simpa only [f',QuotientGroup.ker_lift] using hcop

-- Core-free image of an avoiding normal kernel is central in the component.
theorem core_kernel_central (K S N : Subgroup G) [K.Normal] [N.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤)
    (hQN : pCore 2 G ≤ N) (hKN : ¬ K ≤ N) :
    N.map (QuotientGroup.mk' (pCore 2 G)) ≤
      (center (K.map (QuotientGroup.mk' (pCore 2 G)))).map
        (K.map (QuotientGroup.mk' (pCore 2 G))).subtype := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  let B := K.map q
  let C := N.map q
  let : B.Normal := Normal.map inferInstance q hq
  let : C.Normal := Normal.map inferInstance q hq
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hquot : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (S.map q) (hS.map q) (by
      rw [← Subgroup.map_sup,hgen,map_top_of_surjective q hq])
  have hF : generalizedFitting (G ⧸ pCore 2 G) = B :=
    generalizedFitting_eq_of_quasisimple_two_quotient B hquot (pCore_quotient_pCore_eq_bot 2)
  have hBC : ¬ B ≤ C := by
    intro hh
    apply hKN
    have ht := map_le_iff_le_comap.mp hh
    rwa [comap_map_eq_self (show q.ker ≤ N by rwa [QuotientGroup.ker_mk'])] at ht
  have hd := (show IsComponent (G ⧸ pCore 2 G) B from
    ⟨(inferInstance : B.Normal).isSubnormal,inferInstance⟩).normal_dichotomy C
  have hCB : C ≤ centralizer (B : Set (G ⧸ pCore 2 G)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hd.resolve_left hBC))
  have hCK : C ≤ B := hCB.trans (hF ▸ centralizer_generalizedFitting_le _)
  intro x hx
  exact ⟨⟨x,hCK hx⟩,mem_center_iff.mpr (fun k => Subtype.ext (hCB hx k k.property)),rfl⟩

theorem core_kernel_coprime (K S N : Subgroup G) [K.Normal] [N.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤)
    (hQN : pCore 2 G ≤ N) (hKN : ¬ K ≤ N) :
    Nat.Coprime 2 (Nat.card (N.map (QuotientGroup.mk' (pCore 2 G)))) := by
  let B := K.map (QuotientGroup.mk' (pCore 2 G))
  let e := cComponentTwoCoreQuotientEquiv hK
  have hb : pCore 2 B = ⊥ := by
    have he := pCore_map_iso 2 e
    rw [pCore_quotient_pCore_eq_bot,Subgroup.map_bot] at he
    exact he.symm
  have hc : Nat.Coprime 2 (Nat.card (center B)) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr
      (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hb (center B) le_rfl)
  exact hc.of_dvd_right ((card_dvd_of_le (core_kernel_central K S N hK hS hgen hQN hKN)).trans
    (card_map_dvd (center B) B.subtype))

theorem map_inf_normalizer_maxJ_two_stage (K R : Subgroup G) (hR : IsPGroup 2 R)
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker ≤ R)
    (f : H →* D) (hf : Function.Surjective f)
    (hcop : Nat.Coprime 2 (Nat.card f.ker)) (hfK : f.ker ≤ K.map q) :
    (K ⊓ normalizer (elementaryAbelianMaxJ R : Set G)).map (f.comp q) =
      K.map (f.comp q) ⊓ normalizer ((elementaryAbelianMaxJ R).map (f.comp q) : Set D) := by
  let : Finite H := Finite.of_surjective q hq
  let : Fact (IsPGroup 2 ((elementaryAbelianMaxJ R).map q)) :=
    ⟨(hR.to_le (sSup_le fun _ hA => hA.1)).map q⟩
  have hRN : R ≤ normalizer (elementaryAbelianMaxJ R : Set G) :=
    R.le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ R)
  rw [← map_map, map_inf_of_ker_le q K _ (hk.trans hRN),
    normalizer_map_maxJ R q hq hk, inf_comm, map_inf_of_ker_le f _ _ hfK,
    inf_comm, ← normalizer_map_eq_of_coprime_kernel 2 _ f hf hcop, map_map, map_map]

omit [Finite G] in
theorem map_lt_map_of_kernel_central_in_perfect (K J : Subgroup G)
    [Group.IsPerfect K] (hJ : J < K) (f : G →* H)
    (hk : f.ker ≤ (center K).map K.subtype) : J.map f < K.map f := by
  refine lt_of_le_of_ne (map_mono hJ.le) ?_
  intro he
  have hker : (f.comp K.subtype).ker ≤ center K := by
    intro x hx
    obtain ⟨z,hz,he⟩ := hk hx
    exact (Subtype.ext he : z = x) ▸ hz
  have hmap : (⊤ : Subgroup K).map (f.comp K.subtype) ≤
      (J.subgroupOf K).map (f.comp K.subtype) := by
    rw [← map_map,← map_map, ← MonoidHom.range_eq_map, K.range_subtype, map_subgroupOf_eq_of_le hJ.le]
    exact he.ge
  have hh := le_of_map_le_of_perfect (f.comp K.subtype) hker ⊤ (J.subgroupOf K) hmap
  exact hJ.ne (le_antisymm hJ.le (fun x hx => hh (show (⟨x,hx⟩ : K) ∈ ⊤ from mem_top _)))

theorem component_thompson_intersection_control (K R M N : Subgroup G)
    [K.Normal] [N.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hgen : K ⊔ R = ⊤) (hQR : pCore 2 G ≤ R)
    (hQN : pCore 2 G ≤ N) (hKN : ¬K ≤ N)
    (hcontrol : R.characteristicNormalizerClosure ≤ M) (hout : ¬K ≤ M) :
    K.map (QuotientGroup.mk' N) ⊓
        normalizer ((elementaryAbelianMaxJ R).map (QuotientGroup.mk' N) : Set (G ⧸ N)) ≤
      (K ⊓ M).map (QuotientGroup.mk' N) ∧
      (K ⊓ M).map (QuotientGroup.mk' N) < K.map (QuotientGroup.mk' N) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let f := QuotientGroup.lift (pCore 2 G) (QuotientGroup.mk' N)
    (by simpa only [QuotientGroup.ker_mk'] using hQN)
  have he : f.comp q = QuotientGroup.mk' N := by ext; rfl
  have hfk : f.ker = N.map q := by
    simp only [f,q,QuotientGroup.ker_lift,QuotientGroup.ker_mk']
  have hc : f.ker ≤ (center (K.map q)).map (K.map q).subtype := by
    rw [hfk]
    exact core_kernel_central K R N hK hR hgen hQN hKN
  have hcop : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hfk]
    exact core_kernel_coprime K R N hK hR hgen hQN hKN
  have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective _ _
    (QuotientGroup.mk'_surjective N) _
  have hNM : normalizer (elementaryAbelianMaxJ R : Set G) ≤ M :=
    (normalizer_maxJ_le_characteristicNormalizerClosure R R
      (sSup_le fun _ hA => hA.1) le_rfl
      (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup R hR hne)).trans hcontrol
  have hRM : R ≤ M := (R.le_normalizer.trans
    (normalizer_le_normalizer_elementaryAbelianMaxJ R)).trans hNM
  have hqp : q.ker ≤ R := by simpa only [q,QuotientGroup.ker_mk'] using hQR
  have hqm : q.ker ≤ M := hqp.trans hRM
  refine ⟨?_,?_⟩
  · rw [←he,←map_inf_normalizer_maxJ_two_stage K R hR q
      (QuotientGroup.mk'_surjective _) (by simpa only [q,QuotientGroup.ker_mk'] using hQR)
      f hf hcop (hc.trans (map_subtype_le _))]
    exact map_mono (inf_le_inf_left K hNM)
  · have hm : (K ⊓ M).map q < K.map q := by
      refine lt_of_le_of_ne (map_mono inf_le_left) ?_
      intro hh
      apply hout
      have hh' : K.map q ≤ M.map q := hh ▸ map_mono (show K ⊓ M ≤ M from inf_le_right)
      have hle := map_le_iff_le_comap.mp hh'
      rwa [comap_map_eq_self hqm] at hle
    let : Group.IsPerfect K := hK.perfect
    let : Group.IsPerfect (K.map q) := Group.IsPerfect.map q
    have hh := map_lt_map_of_kernel_central_in_perfect (K.map q) ((K ⊓ M).map q) hm f hc
    simpa only [map_map,he] using hh
end Theory.GroupTheory.QuasisimpleThompson


