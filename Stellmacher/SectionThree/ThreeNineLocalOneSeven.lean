module

public import Stellmacher.SectionOne.OffenderSelectedProduct
public import FeitThompson.Fitting.Centralizer
public import FeitThompson.PCore.CentralizerControl
public import FeitThompson.PCore.Nilpotent
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# The local application of Stellmacher (1.7) in (3.9)

This module isolates the first local use of (1.7) in the proof of
Stellmacher (3.9).  For
`F = O_{2'}(F(G)) R J`, where `R J` is normal in a local subgroup `P`, the
odd Fitting factor does not change the Sylow 2-subgroup.  If `R J`
centralizes `O₂(G)` and the chosen Sylow image meets `O₂(G)` trivially, then
`O₂(F)=1`: its ambient image lies in the chosen Sylow and centralizes the
Fitting subgroup, hence lies in `O₂(G)` by nilpotence of `F(G)`.

The second theorem packages the direct (1.7) endpoint.  Offenders generating
`J` select an internal product of `SL₂(2)` factors.  If `[K,J]=K`, normality
of the selected product inside the global one-seven product places `K` in
its derived subgroup, which is a 3-group.  The complete factor normality and
module decomposition are retained for the ambient promotion and support
comparison in the rest of (3.9).

The journal scan has `O_{2'}(F(G))` in this construction; the prime is lost
in `refs/latex/stellmacher-n-group.tex`.  This module uses only the direct
Section One development and does not import Stellmacher (2.2).
-/

open scoped BigOperators Pointwise commutatorElement

namespace Stellmacher.SectionThree

universe u v

private theorem sl2_commutator_cube_39
    {H : Type u} [Group H] [Finite H] (h : IsSL2Two H)
    (x : H) (hx : x ∈ commutator H) : x ^ 3 = 1 := by
  obtain ⟨e⟩ := h
  have hmul : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by
    decide +kernel
  have hcomm : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      ⁅a, b⁆ ^ 3 = 1 := by
    decide +kernel
  let C : Subgroup H :=
    { carrier := {x | (e x) ^ 3 = 1}
      one_mem' := by simp
      mul_mem' := by intro a b ha hb; simpa using hmul (e a) (e b) ha hb
      inv_mem' := by intro a ha; simp_all [inv_pow] }
  have hle : commutator H ≤ C := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change e ⁅a, b⁆ ^ 3 = 1
    rw [map_commutatorElement]
    exact hcomm _ _
  have hcube : e x ^ 3 = 1 := hle hx
  exact e.injective (by simpa using hcube)

private theorem internalSL2Product_commutator_isPGroup_three_39
    {G : Type u} [Group G] [Finite G]
    {n : ℕ} (E : Subgroup G) (D : Fin n → Subgroup G)
    (hprod : IsInternalDirectProductFamily E D)
    (hSL : ∀ i, IsSL2Two (D i)) :
    IsPGroup 3 (commutator E) := by
  classical
  let P := ∀ i : Fin n, (D i)
  have hcomm : Pairwise (fun i j : Fin n => ∀ x y : G,
      x ∈ D i → y ∈ D j → Commute x y) := by
    intro i j hij x y hx hy
    exact hprod.2.2 i j hij x hx y hy
  let f : P →* G := Subgroup.noncommPiCoprod hcomm
  have hf : f.range = E := (Subgroup.noncommPiCoprod_range).trans hprod.1.symm
  have hmap : (commutator P).map f = (commutator E).map E.subtype := by
    rw [map_commutator_eq, hf, Subgroup.map_subtype_commutator]
  have hPp : IsPGroup 3 (commutator P) := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    funext i
    have heval : (x : P) i ∈ commutator (D i) := by
      have hm := Subgroup.mem_map_of_mem
        (Pi.evalMonoidHom (fun i : Fin n => (D i)) i) x.property
      rw [map_commutator_eq] at hm
      exact Subgroup.commutator_mono le_top le_top hm
    exact sl2_commutator_cube_39 (hSL i) _ heval
  have himage : IsPGroup 3 ((commutator E).map E.subtype) := by
    rw [← hmap]
    exact hPp.map f
  exact himage.of_equiv
    ((commutator E).equivMapOfInjective E.subtype E.subtype_injective).symm

private theorem isPGroup_le_pCore_of_le_fitting_39
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hPp : IsPGroup p P)
    (hPF : P ≤ fittingSubgroup G) :
    P ≤ pCore p G := by
  classical
  let PF : Subgroup (fittingSubgroup G) := P.subgroupOf (fittingSubgroup G)
  have hPFp : IsPGroup p PF :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPF).symm
  obtain ⟨U, hPFU⟩ := hPFp.exists_le_sylow
  have hUnormal : (U : Subgroup (fittingSubgroup G)).Normal :=
    Group.IsNilpotent.sylow_normal
      (G := fittingSubgroup G) (inferInstance : Group.IsNilpotent (fittingSubgroup G)) p U
  have hUchar : (U : Subgroup (fittingSubgroup G)).Characteristic :=
    Sylow.characteristic_of_normal U hUnormal
  have hUmapNormal : ((U : Subgroup (fittingSubgroup G)).map
      (fittingSubgroup G).subtype).Normal := by
    infer_instance
  have hUmapP : IsPGroup p ((U : Subgroup (fittingSubgroup G)).map
      (fittingSubgroup G).subtype) := U.isPGroup'.map (fittingSubgroup G).subtype
  have hUcore : (U : Subgroup (fittingSubgroup G)).map
      (fittingSubgroup G).subtype ≤ pCore p G :=
    le_sSup ⟨hUmapNormal, hUmapP⟩
  have hm := Subgroup.map_mono (f := (fittingSubgroup G).subtype) hPFU
  rw [Subgroup.map_subgroupOf_eq_of_le hPF] at hm
  exact hm.trans hUcore

private theorem local_twoCore_eq_bot_of_fitting_centralizer_39
    {G : Type u} [Group G] [Finite G]
    (S F : Subgroup G) (hsolv : Group.IsSolvable G)
    (hcoreS : (pCore 2 F).map F.subtype ≤ S)
    (hcoreCent : (pCore 2 F).map F.subtype ≤
      Subgroup.centralizer (fittingSubgroup G : Set G))
    (hSCore : S ⊓ pCore 2 G = ⊥) :
    pCore 2 F = ⊥ := by
  let K : Subgroup G := (pCore 2 F).map F.subtype
  have hKFit : K ≤ fittingSubgroup G :=
    hcoreCent.trans (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)
  have hKp : IsPGroup 2 K := (pCore_isPGroup (G := F) (p := 2)).map F.subtype
  have hKCore : K ≤ pCore 2 G :=
    isPGroup_le_pCore_of_le_fitting_39 K hKp hKFit
  have hKbot : K = ⊥ := by
    apply le_bot_iff.mp
    rw [← hSCore]
    exact le_inf hcoreS hKCore
  apply Subgroup.map_injective F.subtype_injective
  simpa [K] using hKbot

private theorem local_twoCore_le_centralizer_fitting_39
    {G : Type u} [Group G] [Finite G]
    (F : Subgroup G)
    (hoddF : (pPrimeCore 2 (fittingSubgroup G)).map
      (fittingSubgroup G).subtype ≤ F)
    (hFcoreCent : F ≤ Subgroup.centralizer (pCore 2 G : Set G)) :
    (pCore 2 F).map F.subtype ≤
      Subgroup.centralizer (fittingSubgroup G : Set G) := by
  classical
  let K : Subgroup G := (pCore 2 F).map F.subtype
  let D : Subgroup G := (pPrimeCore 2 (fittingSubgroup G)).map
    (fittingSubgroup G).subtype
  have hKF : K ≤ F := Subgroup.map_subtype_le _
  have hKcoreCent : K ≤ Subgroup.centralizer (pCore 2 G : Set G) :=
    hKF.trans hFcoreCent
  have hKnormalF : (K.subgroupOf F).Normal := by
    simpa [K, subgroupOf_map_subtype_eq] using
      (pCore_normal (G := F) (p := 2))
  have hDnormal : D.Normal := by
    dsimp [D]
    infer_instance
  have hDnormalF : (D.subgroupOf F).Normal := hDnormal.subgroupOf F
  have hFnormK : F ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKF).mp hKnormalF
  have hFnormD : F ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hoddF).mp hDnormalF
  have hKDleInf : ⁅K, D⁆ ≤ K ⊓ D := le_inf
    ((Subgroup.le_normalizer_iff_commutator_le_left).mp (hoddF.trans hFnormK))
    ((Subgroup.le_normalizer_iff_commutator_le_right).mp (hKF.trans hFnormD))
  have hKp : IsPGroup 2 K :=
    (pCore_isPGroup (G := F) (p := 2)).map F.subtype
  obtain ⟨n, hKcard⟩ := hKp.exists_card_eq
  have hDcard : Nat.card D = Nat.card (pPrimeCore 2 (fittingSubgroup G)) := by
    exact Subgroup.card_map_of_injective (fittingSubgroup G).subtype_injective
  have hKDcop : Nat.Coprime (Nat.card K) (Nat.card D) := by
    rw [hKcard, hDcard]
    exact (pPrimeCore_coprime_card (G := fittingSubgroup G) (p := 2)).pow_left n
  have hKDdisj : Disjoint K D := Subgroup.disjoint_of_coprime_natCard hKDcop
  have hKcentD : K ≤ Subgroup.centralizer (D : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact le_bot_iff.mp (hKDleInf.trans hKDdisj.le_bot)
  have hFitGen : fittingSubgroup G ≤ pCore 2 G ⊔ D := by
    have hgen := nilpotent_top_le_pCore_sup_pPrimeCore
      (Q := fittingSubgroup G) (p := 2)
      (inferInstance : Group.IsNilpotent (fittingSubgroup G))
    have hm := Subgroup.map_mono (f := (fittingSubgroup G).subtype) hgen
    rw [Subgroup.map_sup] at hm
    have htopMap : (⊤ : Subgroup (fittingSubgroup G)).map
        (fittingSubgroup G).subtype = fittingSubgroup G := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [htopMap] at hm
    apply hm.trans
    apply sup_le_sup_right
    exact isPGroup_le_pCore_of_le_fitting_39
      ((pCore 2 (fittingSubgroup G)).map (fittingSubgroup G).subtype)
      ((pCore_isPGroup (G := fittingSubgroup G) (p := 2)).map
        (fittingSubgroup G).subtype)
      (Subgroup.map_subtype_le _)
  exact (Subgroup.le_centralizer_sup_of_le_centralizers hKcoreCent hKcentD).trans
    (Subgroup.centralizer_le hFitGen)

private theorem prime_not_dvd_index_of_normal_sup_39
    {H : Type u} [Group H] [Finite H]
    {K U : Subgroup H} [K.Normal] {p : ℕ}
    (hKcard : ¬ p ∣ Nat.card K) (hKU : K ⊔ U = ⊤) :
    ¬ p ∣ U.index := by
  intro hpU
  have hrel_eq : U.relIndex (U ⊔ K) = (U ⊓ K).relIndex K := by
    have hKrel : K.relIndex (U ⊔ K) = (U ⊓ K).relIndex U := by
      calc
        K.relIndex (U ⊔ K) = K.relIndex U := by simp
        _ = (U ⊓ K).relIndex U := by
          symm
          simpa [inf_comm] using
            (Subgroup.inf_relIndex_left (H := U) (K := K))
    have hmul :
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
          (U ⊓ K).relIndex K * (U ⊓ K).relIndex U := by
      calc
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
            (U ⊓ K).relIndex (U ⊔ K) :=
          Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
        _ = (U ⊓ K).relIndex K * K.relIndex (U ⊔ K) := by
          symm
          exact Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
        _ = (U ⊓ K).relIndex K * (U ⊓ K).relIndex U := by rw [hKrel]
    have hpos : 0 < (U ⊓ K).relIndex U := by
      exact Nat.pos_of_ne_zero (by
        dsimp [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite)
    have hmul' :
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
          (U ⊓ K).relIndex U * (U ⊓ K).relIndex K := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    exact Nat.eq_of_mul_eq_mul_left hpos hmul'
  have hidx : U.relIndex (U ⊔ K) = U.index := by
    rw [show U ⊔ K = ⊤ by simpa [sup_comm] using hKU]
    exact Subgroup.relIndex_top_right (H := U)
  have hdvd : U.index ∣ Nat.card K := by
    rw [← hidx, hrel_eq]
    exact Subgroup.relIndex_dvd_card (H := U ⊓ K) (K := K)
  exact hKcard (hpU.trans hdvd)

private theorem isSylowSubgroupIn_normal_odd_sup_39
    {G : Type u} [Group G] [Finite G]
    (D P S : Subgroup G) (hDnormal : D.Normal)
    (hDodd : ¬ 2 ∣ Nat.card D)
    (hSylow : IsSylowSubgroupIn S P) :
    IsSylowSubgroupIn S (D ⊔ P) := by
  classical
  let L : Subgroup G := D ⊔ P
  have hDL : D ≤ L := le_sup_left
  have hPL : P ≤ L := le_sup_right
  have hSL : S ≤ L := by
    obtain ⟨T, hT⟩ := hSylow
    rw [← hT]
    exact (Subgroup.map_subtype_le (T : Subgroup P)).trans hPL
  let DL : Subgroup L := D.subgroupOf L
  let PL : Subgroup L := P.subgroupOf L
  let SL : Subgroup L := S.subgroupOf L
  have hDLnormal : DL.Normal := hDnormal.subgroupOf L
  let _ : DL.Normal := hDLnormal
  have hDLcard : Nat.card DL = Nat.card D := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hDLodd : ¬ 2 ∣ Nat.card DL := by simpa [hDLcard] using hDodd
  have hsup : DL ⊔ PL = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hDL hPL]
    exact Subgroup.subgroupOf_self L
  have hPindex : ¬ 2 ∣ PL.index :=
    prime_not_dvd_index_of_normal_sup_39 hDLodd hsup
  obtain ⟨T, hT⟩ := hSylow
  have hSP : S.subgroupOf P = (T : Subgroup P) := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (by
      rw [← hT]
      exact Subgroup.map_subtype_le (T : Subgroup P)), hT]
  have hSindexP : ¬ 2 ∣ S.relIndex P := by
    change ¬ 2 ∣ (S.subgroupOf P).index
    rw [hSP]
    exact T.not_dvd_index
  have hSrel : S.relIndex P * P.relIndex L = S.relIndex L :=
    Subgroup.relIndex_mul_relIndex S P L (by
      rw [← hT]
      exact Subgroup.map_subtype_le (T : Subgroup P)) hPL
  have hPindex' : ¬ 2 ∣ P.relIndex L := by
    change ¬ 2 ∣ (P.subgroupOf L).index
    exact hPindex
  have hSindexL : ¬ 2 ∣ SL.index := by
    change ¬ 2 ∣ S.relIndex L
    intro hdvd
    have hprod : 2 ∣ S.relIndex P * P.relIndex L := by
      rwa [hSrel]
    rcases Nat.prime_two.dvd_mul.mp hprod with hdvd | hdvd
    · exact hSindexP hdvd
    · exact hPindex' hdvd
  have hSp : IsPGroup 2 S := by
    rw [← hT]
    exact T.isPGroup'.map P.subtype
  have hSLp : IsPGroup 2 SL :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  let U : Sylow 2 L := hSLp.toSylow hSindexL
  refine ⟨U, ?_⟩
  have hU : (U : Subgroup L) = SL := IsPGroup.toSylow_coe hSLp hSindexL
  rw [hU]
  exact Subgroup.map_subgroupOf_eq_of_le hSL

private theorem local_twoCore_le_sylow_39
    {G : Type u} [Group G] [Finite G]
    (D P S F : Subgroup G) (hDnormal : D.Normal)
    (hDodd : ¬ 2 ∣ Nat.card D)
    (hSylow : IsSylowSubgroupIn S P)
    (hFL : F ≤ D ⊔ P) (hFnormal : (F.subgroupOf (D ⊔ P)).Normal) :
    (pCore 2 F).map F.subtype ≤ S := by
  let L : Subgroup G := D ⊔ P
  have hSylowL : IsSylowSubgroupIn S L :=
    isSylowSubgroupIn_normal_odd_sup_39 D P S hDnormal hDodd hSylow
  have hcore := pCoreAmbient_mono_of_isSubnormalIn F L 2 hFL hFnormal.isSubnormal
  obtain ⟨U, hU⟩ := hSylowL
  apply hcore.trans
  rw [← hU]
  exact Subgroup.map_mono
    ((pCore_isPGroup (G := L) (p := 2)).le_sylow_of_normal U)

private theorem odd_normal_sup_local_normal_in_extension_39
    {G : Type u} [Group G]
    (D P R J : Subgroup G) (hDnormal : D.Normal)
    (hRJP : R ⊔ J ≤ P) (hRJnormal : ((R ⊔ J).subgroupOf P).Normal) :
    ((D ⊔ R ⊔ J).subgroupOf (D ⊔ P)).Normal := by
  have hRP : R ≤ P := le_sup_left.trans hRJP
  have hJP : J ≤ P := le_sup_right.trans hRJP
  have hFL : D ⊔ R ⊔ J ≤ D ⊔ P :=
    sup_le (sup_le le_sup_left (hRP.trans le_sup_right))
      (hJP.trans le_sup_right)
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hFL).mpr
  apply sup_le
  · exact (show D ≤ D ⊔ R ⊔ J from le_sup_left.trans le_sup_left) |>.trans
      (D ⊔ R ⊔ J).le_normalizer
  · have hPnormD : P ≤ Subgroup.normalizer (D : Set G) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hPnormRJ : P ≤ Subgroup.normalizer ((R ⊔ J : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRJP).mp hRJnormal
    have hPnormF : P ≤ Subgroup.normalizer ((D ⊔ (R ⊔ J) : Subgroup G) : Set G) :=
      (le_inf hPnormD hPnormRJ).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup D (R ⊔ J))
    simpa [sup_assoc] using hPnormF

private theorem fitting_oddCore_le_centralizer_twoCore_39
    {G : Type u} [Group G] [Finite G] :
    (pPrimeCore 2 (fittingSubgroup G)).map (fittingSubgroup G).subtype ≤
      Subgroup.centralizer (pCore 2 G : Set G) := by
  let O : Subgroup G := pCore 2 G
  let Fit : Subgroup G := fittingSubgroup G
  let OF : Subgroup Fit := O.subgroupOf Fit
  have hOFnormal : OF.Normal := by
    dsimp [OF, O, Fit]
    exact (pCore_normal (G := G) (p := 2)).subgroupOf (fittingSubgroup G)
  have hOFp : IsPGroup 2 OF := by
    exact (pCore_isPGroup (G := G) (p := 2)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (pCore_le_fitting G 2)).symm
  have hOFcore : OF ≤ pCore 2 Fit := le_sSup ⟨hOFnormal, hOFp⟩
  have hm := Subgroup.map_mono (f := Fit.subtype) hOFcore
  have hOmap : OF.map Fit.subtype = O :=
    Subgroup.map_subgroupOf_eq_of_le (pCore_le_fitting G 2)
  rw [hOmap] at hm
  exact (pPrimeCore_map_le_centralizer_pCore_map (p := 2) Fit).trans
    (Subgroup.centralizer_le hm)

private theorem local_subgroup_le_centralizer_twoCore_39
    {G : Type u} [Group G] [Finite G]
    (R J : Subgroup G)
    (hRJcent : R ⊔ J ≤ Subgroup.centralizer (pCore 2 G : Set G)) :
    (pPrimeCore 2 (fittingSubgroup G)).map (fittingSubgroup G).subtype ⊔ R ⊔ J ≤
      Subgroup.centralizer (pCore 2 G : Set G) := by
  exact sup_le (sup_le fitting_oddCore_le_centralizer_twoCore_39
    (le_sup_left.trans hRJcent)) (le_sup_right.trans hRJcent)

/-- The local group `O₂′(F(G)) R J` is core-free under the Sylow-intersection
and centralization hypotheses occurring in the first application of (1.7)
in Stellmacher (3.9). -/
public theorem threeNine_barF_twoCore_eq_bot
    {G : Type u} [Group G] [Finite G]
    (S P R J : Subgroup G) (hsolv : Group.IsSolvable G)
    (hSylow : IsSylowSubgroupIn S P)
    (hRJP : R ⊔ J ≤ P) (hRJnormal : ((R ⊔ J).subgroupOf P).Normal)
    (hRJcent : R ⊔ J ≤ Subgroup.centralizer (pCore 2 G : Set G))
    (hSCore : S ⊓ pCore 2 G = ⊥) :
    pCore 2 (↥(((pPrimeCore 2 (fittingSubgroup G)).map
      (fittingSubgroup G).subtype ⊔ R ⊔ J : Subgroup G))) = ⊥ := by
  let D : Subgroup G := (pPrimeCore 2 (fittingSubgroup G)).map
    (fittingSubgroup G).subtype
  let F : Subgroup G := D ⊔ R ⊔ J
  have hDnormal : D.Normal := by
    dsimp [D]
    infer_instance
  have hDodd : ¬ 2 ∣ Nat.card D := by
    rw [show Nat.card D = Nat.card (pPrimeCore 2 (fittingSubgroup G)) by
      exact Subgroup.card_map_of_injective (fittingSubgroup G).subtype_injective]
    exact (Nat.prime_two.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (G := fittingSubgroup G) (p := 2)))
  have hFL : F ≤ D ⊔ P := by
    exact sup_le (sup_le le_sup_left ((le_sup_left.trans hRJP).trans le_sup_right))
      ((le_sup_right.trans hRJP).trans le_sup_right)
  have hFnormal : (F.subgroupOf (D ⊔ P)).Normal := by
    simpa [F] using
      odd_normal_sup_local_normal_in_extension_39 D P R J hDnormal hRJP hRJnormal
  have hcoreS : (pCore 2 F).map F.subtype ≤ S :=
    local_twoCore_le_sylow_39 D P S F hDnormal hDodd hSylow hFL hFnormal
  have hFcoreCent : F ≤ Subgroup.centralizer (pCore 2 G : Set G) := by
    simpa [F, D] using local_subgroup_le_centralizer_twoCore_39 R J hRJcent
  have hoddF : D ≤ F := le_sup_left.trans le_sup_left
  have hcoreCentFit : (pCore 2 F).map F.subtype ≤
      Subgroup.centralizer (fittingSubgroup G : Set G) :=
    local_twoCore_le_centralizer_fitting_39 F hoddF hFcoreCent
  exact local_twoCore_eq_bot_of_fitting_centralizer_39
    S F hsolv hcoreS hcoreCentFit hSCore

/-- A subgroup satisfying `[K,J]=K` for offender generators `J` lies in the
derived subgroup of the selected `SL₂(2)` product, and is therefore a
3-group.  The full selected-factor and module data are returned for the
ambient step of Stellmacher (3.9). -/
public theorem threeNine_local_oneSeven_residual_isThreeGroup
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : SectionOne.Hypotheses G V) (S : Sylow 2 G)
    {I : Sort v} (A : I → Subgroup G)
    (hA : ∀ i, SectionOne.oneA (V := V) (S : Subgroup G) (A i))
    (J K : Subgroup G) (hJ : J = ⨆ i, A i)
    (hcomm : ⁅K, J⁆ = K) :
    IsPGroup 3 K ∧
      ∃ (E : Subgroup G) (n : ℕ) (D : Fin n → Subgroup G),
        E = ⁅SectionOne.oddCore G, J⁆ ⊔ J ∧
        J = (S : Subgroup G) ⊓ E ∧
        E ≤ SectionOne.oneSevenGenerated (G := G) (V := V) ∧
        (E.subgroupOf (SectionOne.oneSevenGenerated (G := G) (V := V))).Normal ∧
        IsInternalDirectProductFamily E D ∧
        Function.Injective D ∧
        (∀ i, SectionOne.IsOneSevenFactor (V := V) (D i)) ∧
        (∀ i, ((D i).subgroupOf E).Normal) ∧
        IsInternalDirectProductFamily (⊤ : Subgroup V)
          (fun i : Option (Fin n) => match i with
            | none => FixedPoints.subgroup E V
            | some i => commutatorAction (D i) V) ∧
        K ≤ (commutator E).map E.subtype := by
  classical
  let E : Subgroup G := ⁅(SectionOne.oddCore G), J⁆ ⊔ J
  let N : Subgroup G := SectionOne.oneSevenGenerated (G := G) (V := V)
  obtain ⟨hJinf, hEN, hEnorm, n, D, hprod, hDin, hD, hDN, hmodule⟩ :=
    SectionOne.offender_generated_selected_product h S A hA J hJ
  change IsInternalDirectProductFamily E D at hprod
  change E ≤ N at hEN
  have hNnormal : N.Normal := (SectionOne.oneSeven_global_product h S).1
  let _ : N.Normal := hNnormal
  have hJN : J ≤ N := le_sup_right.trans hEN
  have hKN : K ≤ N := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono le_top hJN).trans
      (Subgroup.commutator_le_right (⊤ : Subgroup G) N)
  have hNE : N ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEN).mp hEnorm
  have hKE : K ≤ E := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono hKN le_sup_right).trans
      ((Subgroup.le_normalizer_iff_commutator_le_right).mp hNE)
  have hKderived : K ≤ (commutator E).map E.subtype := by
    rw [← hcomm, Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_mono hKE le_sup_right
  have hderived : IsPGroup 3 (commutator E) :=
    internalSL2Product_commutator_isPGroup_three_39 E D hprod fun i => (hD i).1
  have hderivedAmbient : IsPGroup 3 ((commutator E).map E.subtype) :=
    hderived.map E.subtype
  exact ⟨hderivedAmbient.to_le hKderived, E, n, D, rfl, hJinf,
    hEN, hEnorm, hprod, hDin, hD, hDN, hmodule, hKderived⟩

end Stellmacher.SectionThree
