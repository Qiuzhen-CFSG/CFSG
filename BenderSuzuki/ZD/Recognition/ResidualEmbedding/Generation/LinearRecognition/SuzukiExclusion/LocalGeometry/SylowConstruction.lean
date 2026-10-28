module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Borel
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Outer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Stages
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The actual Suzuki Sylow product and its enlargement

Choose the marked Borel Sylow subgroup P of L and a Sylow subgroup U of
J = C_G(L). Multiplication transports their product to a Sylow subgroup
of LJ. Every two-subgroup of N_G(L) lies in LJ by the odd outer index,
so T = PU is Sylow in N_G(L). Relative indices show [D:J] is odd;
consequently U is also Sylow in the literal pair stabilizer D. The odd
intersection L ∩ D makes the factors P and U disjoint.

The point-stabilizer and permutation-degree formulas give |G|₂ = q|T|,
where q = 2^(2*m+1). The Sylow normalizer theorem therefore enlarges T
to S. Finally P ≤ T ≤ M identifies the distinguished closure in T with
A = ⟨Z ∩ M⟩. Invariance of Z gives N_G(T) ≤ N_G(A) = M, retaining the
source placement S ≤ M without assuming elementary abelianness of U.

Source: GLS4, Chapter 2, Lemma 14.2(c,e), equations (14A)–(14C), and the
Sylow enlargement in Lemma 14.3(b), `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
open Subgroup
open scoped Pointwise
namespace BenderSuzuki.ZD.SuzukiExclusion
variable {G : Type*} [Group G] [Finite G]

private theorem commuting_sylow_product (L J : Subgroup G)
    (hc : J ≤ centralizer (L : Set G)) (P : Sylow 2 L) (Q : Sylow 2 J) :
    ∃ R : Sylow 2 (L ⊔ J : Subgroup G),
      (R : Subgroup (L ⊔ J : Subgroup G)).map (L ⊔ J : Subgroup G).subtype =
        (P : Subgroup L).map L.subtype ⊔ (Q : Subgroup J).map J.subtype := by
  let F := L ⊔ J
  let μ : L × J →* G := L.subtype.noncommCoprod J.subtype
    (fun l j => hc j.property l l.property)
  let f : L × J →* F := μ.codRestrict F (fun x => mul_mem_sup x.1.property x.2.property)
  have hn : J ≤ normalizer (L : Set G) := hc.trans (Subgroup.centralizer_le_normalizer _)
  have hf : Function.Surjective f := by
    intro x
    have hx : (x : G) ∈ (L : Set G) * (J : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L J hn]
      exact x.property
    obtain ⟨l, hl, j, hj, he⟩ := hx
    exact ⟨(⟨l, hl⟩, ⟨j, hj⟩), Subtype.ext he⟩
  let W := (P : Subgroup L).prod (Q : Subgroup J)
  have hp : IsPGroup 2 W := by
    obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
    obtain ⟨b, hb⟩ := Q.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a + b)
    rw [Nat.card_congr (Subgroup.prodEquiv (P : Subgroup L) (Q : Subgroup J)).toEquiv,
      Nat.card_prod, ha, hb, pow_add]
  have hi : ¬ 2 ∣ W.index := by
    rw [Subgroup.index_prod]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index Q.not_dvd_index
  let R := hp.toSylow hi
  refine ⟨R.mapSurjective hf, ?_⟩
  change (W.map f).map F.subtype = _
  rw [map_map]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact mul_mem_sup (mem_map_of_mem _ hy.1) (mem_map_of_mem _ hy.2)
  · apply sup_le
    · rintro x ⟨l, hl, rfl⟩
      exact ⟨(l, 1), ⟨hl, Q.one_mem⟩, by change (l : G) * 1 = l; exact mul_one _⟩
    · rintro x ⟨j, hj, rfl⟩
      exact ⟨(1, j), ⟨P.one_mem, hj⟩, by change (1 : G) * j = j; exact one_mul _⟩

variable {Z : Set G} {M : Subgroup G} {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

private theorem pair_intersection_odd :
    Odd (Nat.card (residualGenerated M z t ⊓ residualPairStabilizer M t : Subgroup G)) := by
  have he := (residualGenerated_suzuki_pair_cyclic_card d.minimal.disconnected
    d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.parameter_pos d.model).2
  rw [inf_comm, he]
  have hh : Even (2 ^ (2 * m + 1)) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  exact Nat.Even.sub_odd Nat.one_le_two_pow hh odd_one

private theorem centralizer_pair_index_odd :
    Odd ((centralizer (residualGenerated M z t : Set G)).relIndex
      (residualPairStabilizer M t)) := by
  let L := residualGenerated M z t
  let J := centralizer (L : Set G)
  let D := residualPairStabilizer M t
  let N := normalizer (L : Set G)
  let F := L ⊔ J
  let K := L ⊓ D
  obtain ⟨_, _, _, _, hDN, _, _, _, _, _, _, _, _, hJD, _⟩ :=
    proper_residualGenerated_structure d.minimal d.reduction d.action
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  have hLN : L ≤ N := L.le_normalizer
  have hJN : J ≤ N := Subgroup.centralizer_le_normalizer _
  have hFN : F ≤ N := sup_le hLN hJN
  have hJF : J ≤ F := le_sup_right
  have hFNnormal : (F.subgroupOf N).Normal := by
    dsimp [F]
    rw [subgroupOf_sup hLN hJN]
    infer_instance
  have hFD : F ⊓ D = K ⊔ J := by
    apply le_antisymm
    · intro x hx
      have hxF : x ∈ (L : Set G) * (J : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left L J hJN]
        exact hx.1
      obtain ⟨l, hl, j, hj, rfl⟩ := hxF
      have hlD : l ∈ D := by
        simpa using D.mul_mem hx.2 (D.inv_mem (hJD hj))
      exact mul_mem_sup ⟨hl, hlD⟩ hj
    · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
        (le_inf hJF hJD)
  have hJE : J.relIndex (K ⊔ J) = J.relIndex K := by
    have hKN : K ≤ N := inf_le_left.trans hLN
    have hEN : K ⊔ J ≤ N := sup_le hKN hJN
    rw [← relIndex_subgroupOf hEN, subgroupOf_sup hKN hJN,
      relIndex_sup_right, relIndex_subgroupOf hKN]
  have hK : Odd (Nat.card K) := pair_intersection_odd d
  have h1o : Odd (J.relIndex (F ⊓ D)) := by
    rw [hFD, hJE]
    exact hK.of_dvd_nat (relIndex_dvd_card _ _)
  have h2o : Odd (F.relIndex D) := by
    have hi : F.relIndex D ∣ (F.subgroupOf N).index := by
      rw [← relIndex_subgroupOf hDN]
      exact relIndex_dvd_index_of_normal _ _
    exact ((show Odd (2 * m + 1) from ⟨m, by omega⟩).of_dvd_nat
      d.normalizer_inner_index_dvd).of_dvd_nat hi
  have he := relIndex_inf_mul_relIndex J F D
  rw [inf_eq_left.mpr hJF] at he
  exact he ▸ h1o.mul h2o


/-- The actual commuting Sylow factors before enlargement. -/
public theorem Context.exists_sylow_product :
    ∃ T U : Subgroup G,
      (∃ V : Sylow 2 (normalizer (residualGenerated M z t : Set G)),
        (V : Subgroup (normalizer (residualGenerated M z t : Set G))).map
          (normalizer (residualGenerated M z t : Set G)).subtype = T) ∧
      (∃ V : Sylow 2 (residualPairStabilizer M t),
        (V : Subgroup (residualPairStabilizer M t)).map
          (residualPairStabilizer M t).subtype = U) ∧
      (∃ V : Sylow 2 (centralizer (residualGenerated M z t : Set G)),
        (V : Subgroup (centralizer (residualGenerated M z t : Set G))).map
          (centralizer (residualGenerated M z t : Set G)).subtype = U) ∧
      U = T ⊓ centralizer (residualGenerated M z t : Set G) ∧
      borelTwoCore M z t = T ⊓ residualGenerated M z t ∧
      T = borelTwoCore M z t ⊔ U ∧
      Disjoint (borelTwoCore M z t) U := by
  let L := residualGenerated M z t
  let J := centralizer (L : Set G)
  let D := residualPairStabilizer M t
  let N := normalizer (L : Set G)
  let F := L ⊔ J
  let P := borelTwoCore M z t
  obtain ⟨_, _, _, _, hDN, _, _, _, _, _, _, _, _, hJD, _⟩ :=
    proper_residualGenerated_structure d.minimal d.reduction d.action
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  obtain ⟨V, hV⟩ := d.borelTwoCore_sylow
  obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := J)
  let U := (Q : Subgroup J).map J.subtype
  let T := P ⊔ U
  have hPL : P ≤ L := by
    rw [show P = (V : Subgroup L).map L.subtype from hV.symm]
    exact map_subtype_le _
  have hUJ : U ≤ J := map_subtype_le _
  have hUD : U ≤ D := hUJ.trans hJD
  have hUp : IsPGroup 2 U := Q.isPGroup'.map J.subtype
  have hPp : IsPGroup 2 P := by
    rw [show P = (V : Subgroup L).map L.subtype from hV.symm]
    exact V.isPGroup'.map L.subtype
  have hUP : U ≤ normalizer (P : Set G) :=
    (hUJ.trans (centralizer_le hPL)).trans (Subgroup.centralizer_le_normalizer _)
  have hTp : IsPGroup 2 T := hPp.to_sup_of_normal_left' hUp hUP
  have hUI : U.relIndex J = (Q : Subgroup J).index := by
    change (U.comap J.subtype).index = _
    rw [comap_map_eq_self_of_injective Subtype.val_injective]
  have hUIo : Odd (U.relIndex D) := by
    rw [← relIndex_mul_relIndex U J D hUJ hJD, hUI]
    exact (Nat.not_even_iff_odd.mp (fun h => Q.not_dvd_index h.two_dvd)).mul
      (centralizer_pair_index_odd d)
  have hUDs : ∃ W : Sylow 2 D, (W : Subgroup D).map D.subtype = U := by
    refine ⟨hUp.comap_subtype.toSylow hUIo.not_two_dvd_nat, ?_⟩
    exact map_subgroupOf_eq_of_le hUD
  obtain ⟨R, hR⟩ := commuting_sylow_product L J le_rfl V Q
  rw [hV] at hR
  have hFN : F ≤ N := sup_le L.le_normalizer (Subgroup.centralizer_le_normalizer _)
  obtain ⟨W, hW⟩ := (R.isPGroup'.map (inclusion hFN)).exists_le_sylow
  let T' := (W : Subgroup N).map N.subtype
  have hTT' : T ≤ T' := by
    have hh := map_mono (f := N.subtype) hW
    rw [map_map] at hh
    change (R : Subgroup F).map F.subtype ≤ T' at hh
    rwa [hR] at hh
  have hT'p : IsPGroup 2 T' := W.isPGroup'.map N.subtype
  have hT'F : T' ≤ F := d.twoSubgroup_le_inner T' hT'p (map_subtype_le _)
  have hT'eq : T' = T := by
    have he := inf_eq_sylow_map R hT'p (hR.symm ▸ hTT')
    rw [inf_eq_left.mpr hT'F, hR] at he
    exact he
  have hd : Disjoint P U := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hcop : (Nat.card P).Coprime (Nat.card (L ⊓ D : Subgroup G)) := by
      rw [hk]
      exact (pair_intersection_odd d).coprime_two_left.pow_left k
    apply disjoint_def.mpr
    intro x hxP hxU
    exact disjoint_def.mp (disjoint_of_coprime_natCard hcop) hxP ⟨hPL hxP, hUD hxU⟩
  refine ⟨T, U, ⟨W, hT'eq⟩, hUDs, ⟨Q, rfl⟩, ?_, ?_, rfl, hd⟩
  · exact (inf_eq_sylow_map Q hTp le_sup_right).symm
  · have hh := inf_eq_sylow_map V hTp (show (V : Subgroup L).map L.subtype ≤ T from
      hV.symm ▸ (show borelTwoCore M z t ≤ T from le_sup_left))
    exact (hh.trans hV).symm

private theorem normalizer_le_pointStabilizer {T : Subgroup G}
    (hPT : borelTwoCore M z t ≤ T) (hTM : T ≤ M) :
    normalizer (T : Set G) ≤ M := by
  let A := closure (Z ∩ (M : Set G))
  have hAP : A ≤ borelTwoCore M z t := by
    rw [show A = (center (borelTwoCore M z t)).map (borelTwoCore M z t).subtype from
      d.borelTwoCore_center.symm]
    exact map_subtype_le _
  have hAT := hAP.trans hPT
  have hA : closure (Z ∩ (T : Set G)) = A := by
    apply le_antisymm (closure_mono (Set.inter_subset_inter_right _ hTM))
    apply (closure_le _).mpr
    intro x hx
    exact subset_closure ⟨hx.1, hAT (subset_closure hx)⟩
  rw [← distinguishedClosure_normalizer d.minimal.disconnected]
  change normalizer (T : Set G) ≤ normalizer (A : Set G)
  rw [← hA]
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨d.minimal.disconnected.invariant g x hx.1,
    (mem_normalizer_iff.mp hg x).mp hx.2⟩

private theorem ambient_sylow_card {T U : Subgroup G}
    (hUD : ∃ V : Sylow 2 (residualPairStabilizer M t),
      (V : Subgroup (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype = U)
    (hTc : Nat.card T = (2 ^ (2 * m + 1)) ^ 2 * Nat.card U)
    (W : Sylow 2 G) : Nat.card W = 2 ^ (2 * m + 1) * Nat.card T := by
  let q := 2 ^ (2 * m + 1)
  let D := residualPairStabilizer M t
  obtain ⟨Q, hQ⟩ := hUD
  have hQc : Nat.card Q = Nat.card U := by
    rw [← hQ, card_map_of_injective Subtype.val_injective]
  have hDI : Nat.card D = Nat.card U * (Q : Subgroup D).index := by
    rw [← (Q : Subgroup D).card_mul_index, hQc]
  have hqE : Even q := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have hq2E : Even (q ^ 2) := hqE.pow_of_ne_zero (by decide)
  have hoddC : Odd (q ^ 2 - q + 1) := (hq2E.tsub hqE).add_one
  have hoddM : Odd M.index := by
    change Odd (Nat.card (G ⧸ M))
    rw [d.degree]
    exact hq2E.add_one.mul (hq2E.mul_right (q - 1)).add_one
  have hoddQ : Odd (Q : Subgroup D).index :=
    Nat.not_even_iff_odd.mp (fun h => Q.not_dvd_index h.two_dvd)
  let c := (q ^ 2 - q + 1) * (Q : Subgroup D).index * M.index
  have hco : Odd c := (hoddC.mul hoddQ).mul hoddM
  have hc0 : c ≠ 0 := by intro h; rw [h] at hco; exact Nat.not_odd_zero hco
  have hGc : Nat.card G = (q ^ 3 * Nat.card U) * c := by
    rw [← M.card_mul_index, d.card_pointStabilizer, hDI]
    dsimp [c, q]
    ring
  obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
  have hpow : q ^ 3 * Nat.card U = 2 ^ ((2 * m + 1) * 3 + k) := by
    rw [← hQc, hk, pow_add, pow_mul]
  have hWc : Nat.card W = q ^ 3 * Nat.card U := by
    rw [W.card_eq_multiplicity, hGc, hpow,
      Nat.factorization_mul (by positivity) hc0, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hco.not_two_dvd_nat, add_zero]
  rw [hWc, hTc]
  dsimp [q]
  ring

/-- The literal source configuration in (14B)–(14C). -/
public theorem Context.sylowConfiguration : Nonempty (SylowConfiguration M z t) := by
  obtain ⟨T, U, hTN, hUD, hUJ, hU, hP, hT, hd⟩ := d.exists_sylow_product
  let P := borelTwoCore M z t
  let D := residualPairStabilizer M t
  obtain ⟨V, hV⟩ := hTN
  have hTp : IsPGroup 2 T := hV ▸ V.isPGroup'.map _
  have hPL : P ≤ residualGenerated M z t := by
    rw [show P = T ⊓ residualGenerated M z t from hP]
    exact inf_le_right
  have hPT : P ≤ T := by
    rw [show P = T ⊓ residualGenerated M z t from hP]
    exact inf_le_left
  have hUT : U ≤ T := hU ▸ inf_le_left
  have hUJle : U ≤ centralizer (residualGenerated M z t : Set G) := hU ▸ inf_le_right
  have hUDle : U ≤ D := by
    obtain ⟨Q, hQ⟩ := hUD
    exact hQ ▸ map_subtype_le _
  have hUP : U ≤ normalizer (P : Set G) :=
    (hUJle.trans (centralizer_le hPL)).trans (Subgroup.centralizer_le_normalizer _)
  have hTc : Nat.card T = Nat.card P * Nat.card U := by
    rw [hT]
    exact card_sup_eq_mul_of_normalizes_of_disjoint P U hUP hd
  have hTM : T ≤ M := by
    rw [hT]
    apply sup_le
    · exact (map_subtype_le _).trans inf_le_left
    · exact hUDle.trans inf_le_left
  have hNM := normalizer_le_pointStabilizer d hPT hTM
  have hdiv : 2 * Nat.card T ∣ Nat.card G := by
    obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := G)
    have hQc := ambient_sylow_card d hUD
      (hTc.trans (congrArg (fun n => n * Nat.card U) d.borelTwoCore_card)) Q
    calc
      2 * Nat.card T ∣ 2 ^ (2 * m + 1) * Nat.card T :=
        Nat.mul_dvd_mul (dvd_pow_self 2 (by omega)) dvd_rfl
      _ = Nat.card Q := hQc.symm
      _ ∣ Nat.card G := (Q : Subgroup G).card_subgroup_dvd_card
  let N := normalizer (T : Set G)
  obtain ⟨W⟩ := Sylow.nonempty (p := 2) (G := N)
  let S := (W : Subgroup N).map N.subtype
  have hTS : T ≤ S := by
    have hp : IsPGroup 2 (T.subgroupOf N) := hTp.comap_subtype
    have hi : (T.subgroupOf N).Normal := Subgroup.normal_in_normalizer
    have hh := map_mono (f := N.subtype) (hp.le_sylow_of_normal W)
    rw [map_subgroupOf_eq_of_le T.le_normalizer] at hh
    exact hh
  have hlt : T < S := by
    apply lt_of_le_of_ne hTS
    intro he
    obtain ⟨a, ha⟩ := hTp.exists_card_eq
    have hg : 2 ^ (a + 1) ∣ Nat.card G := by simpa [ha, pow_succ, Nat.mul_comm] using hdiv
    have hn := Sylow.prime_pow_dvd_card_normalizer hg ha
    have hw := W.pow_dvd_card_of_pow_dvd_card hn
    have hc : Nat.card W = Nat.card T := by
      rw [he]
      exact (card_map_of_injective N.subtype_injective).symm
    rw [hc, ha] at hw
    have hh := Nat.le_of_dvd (by positivity : 0 < 2 ^ a) hw
    have hstrict : 2 ^ a < 2 ^ (a + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  exact ⟨{
    T := T
    U := U
    S := S
    T_sylow := ⟨V, hV⟩
    S_sylow := ⟨W, rfl⟩
    U_eq := hU
    U_sylow_pair := hUD
    U_sylow_centralizer := hUJ
    P_eq := hP
    T_product := by rw [hT]; exact coe_mul_of_right_le_normalizer_left P U hUP
    P_disjoint_U := hd
    T_lt_S := hlt
    S_le_M := (map_subtype_le _).trans hNM }⟩

end BenderSuzuki.ZD.SuzukiExclusion
