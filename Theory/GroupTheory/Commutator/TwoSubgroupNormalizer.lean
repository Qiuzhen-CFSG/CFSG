module

public import Mathlib.GroupTheory.Nilpotent
public import Theory.GroupTheory.Commutator.Basic

/-!
# Normalizer transfer from a full commutator

Let `K`, `B`, and `D` be subgroups of a finite group. If `B` and `D` are
two-groups, `K ⊔ B` normalizes `D`, `D` normalizes `B`, and `[K,B] = K`,
then `D` normalizes `K`. This is the generic finite-group calculation used in
assertion (1) of Stellmacher (5.2), Journal of Algebra 190 (1997), pp. 28--29.

The proof first identifies `K` intrinsically inside `K ⊔ B`: it is the least
normal subgroup with two-group quotient. Indeed, its image in any two-group
quotient is a normal subgroup equal to its commutator with the generated
two-group, which is impossible in a nilpotent group unless the image is
trivial. This characterization makes `K` characteristic in `K ⊔ B`.

It remains to show that `D` normalizes the join. The equality `[K,B] = K`
says that the normal closure of `B` inside `K ⊔ B` is the whole join.
Conjugating a generator `B^l` by `d ∈ D` stays in `B^l`, because `l`
normalizes `D` and `D` normalizes `B`. Thus `D` normalizes the join, and hence
its characteristic subgroup `K`. The two-group hypothesis on `D` is retained
in the public source-facing statement, although the normalization calculation
itself only uses the two displayed normalizer hypotheses.
-/

namespace Subgroup

private theorem normal_commutator_lt_of_nilpotent
    {S : Type*} [Group S] [Group.IsNilpotent S]
    (A : Subgroup S) [A.Normal] (hA : A ≠ ⊥) :
    ⁅A, (⊤ : Subgroup S)⁆ < A := by
  have hle : ⁅A, (⊤ : Subgroup S)⁆ ≤ A := Subgroup.commutator_le_left A ⊤
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hseries : ∀ n : ℕ, A ≤ (⊤ : Subgroup S).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simp [Subgroup.lowerCentralSeries_zero]
    | succ n ih =>
        rw [← heq]
        rw [show (⊤ : Subgroup S).lowerCentralSeries (n + 1) =
          ⁅(⊤ : Subgroup S).lowerCentralSeries n, (⊤ : Subgroup S)⁆ by
            exact Subgroup.lowerCentralSeries_succ (⊤ : Subgroup S) n]
        exact Subgroup.commutator_mono ih le_rfl
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent S)
  apply hA
  apply le_antisymm
  · simpa [hn] using hseries n
  · exact bot_le

/-- If `[K,B] = K`, then `K` lies in every normal subgroup whose quotient is
a finite `p`-group. This is the intrinsic minimality property of the
`p`-residual needed by the normalizer-transfer argument. -/
public theorem le_normal_of_quotient_isPGroup_of_eq_commutator
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (K B N : Subgroup G) [N.Normal]
    (hquotP : IsPGroup p (G ⧸ N))
    (hcomm : ⁅K, B⁆ = K) :
    K ≤ N := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (G ⧸ N) := K.map q
  let Bbar : Subgroup (G ⧸ N) := B.map q
  have hcommbar : ⁅Kbar, Bbar⁆ = Kbar := by
    change ⁅K.map q, B.map q⁆ = K.map q
    rw [← Subgroup.map_commutator, hcomm]
  have hBbarNormKbar : Bbar ≤ Subgroup.normalizer (Kbar : Set (G ⧸ N)) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hcommbar.le
  let S : Subgroup (G ⧸ N) := Kbar ⊔ Bbar
  let A : Subgroup S := Kbar.subgroupOf S
  have hAnormal : A.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    exact sup_le Kbar.le_normalizer hBbarNormKbar
  let _ : A.Normal := hAnormal
  have hSp : IsPGroup p S := hquotP.to_subgroup S
  let _ : Group.IsNilpotent S := hSp.isNilpotent
  have hcommA : ⁅A, (⊤ : Subgroup S)⁆ = A := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator]
    have hmapA : A.map S.subtype = Kbar :=
      Subgroup.map_subgroupOf_eq_of_le le_sup_left
    have hmapTop : (⊤ : Subgroup S).map S.subtype = S := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmapA, hmapTop]
    apply le_antisymm
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (sup_le Kbar.le_normalizer hBbarNormKbar)
    · calc
        Kbar = ⁅Kbar, Bbar⁆ := hcommbar.symm
        _ ≤ ⁅Kbar, S⁆ := Subgroup.commutator_mono le_rfl le_sup_right
  have hAbot : A = ⊥ := by
    by_contra hA
    exact (normal_commutator_lt_of_nilpotent A hA).ne hcommA
  have hKbarBot : Kbar = ⊥ := by
    calc
      Kbar = A.map S.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (show Kbar ≤ S from le_sup_left)).symm
      _ = (⊥ : Subgroup S).map S.subtype := by rw [hAbot]
      _ = ⊥ := Subgroup.map_bot S.subtype
  have hKker : K ≤ q.ker := (Subgroup.map_eq_bot_iff K).mp hKbarBot
  simpa [q, QuotientGroup.ker_mk'] using hKker

private theorem le_normalizer_sup_of_full_commutator
    {G : Type*} [Group G] (K B D : Subgroup G)
    (hSupNormD : K ⊔ B ≤ Subgroup.normalizer (D : Set G))
    (hDNormB : D ≤ Subgroup.normalizer (B : Set G))
    (hcomm : ⁅K, B⁆ = K) :
    D ≤ Subgroup.normalizer ((K ⊔ B : Subgroup G) : Set G) := by
  let L : Subgroup G := K ⊔ B
  have hKL : K ≤ L := le_sup_left
  have hBL : B ≤ L := le_sup_right
  let KL : Subgroup L := K.subgroupOf L
  let BL : Subgroup L := B.subgroupOf L
  have hmapKL : KL.map L.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKL
  have hmapBL : BL.map L.subtype = B :=
    Subgroup.map_subgroupOf_eq_of_le hBL
  have hcommL : ⁅KL, BL⁆ = KL := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, hmapKL, hmapBL, hcomm]
  let N : Subgroup L := Subgroup.normalClosure (BL : Set L)
  have hBLN : BL ≤ N := Subgroup.le_normalClosure
  have hKLN : KL ≤ N := by
    rw [← hcommL]
    exact (Subgroup.commutator_mono le_rfl hBLN).trans
      (Subgroup.commutator_le_right KL N)
  have hgenL : KL ⊔ BL = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, hmapKL, hmapBL]
    have hmapTop : (⊤ : Subgroup L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmapTop]
  have hNtop : N = ⊤ := by
    apply top_unique
    rw [← hgenL]
    exact sup_le hKLN hBLN
  apply Subgroup.le_normalizer_iff.mpr
  intro d hd x hx
  let xL : L := ⟨x, hx⟩
  have hxN : xL ∈ N := by rw [hNtop]; exact Subgroup.mem_top _
  change xL ∈ Subgroup.closure (Group.conjugatesOfSet (BL : Set L)) at hxN
  change d * (xL : G) * d⁻¹ ∈ L
  refine Subgroup.closure_induction
    (k := Group.conjugatesOfSet (BL : Set L))
    (p := fun z _ ↦ d * (z : G) * d⁻¹ ∈ L)
    ?_ ?_ ?_ ?_ hxN
  · intro z hz
    obtain ⟨b, hb, hzb⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨l, rfl⟩ := isConj_iff.mp hzb
    have hlNormD : (l : G) ∈ Subgroup.normalizer (D : Set G) :=
      hSupNormD l.property
    have hlInvNormD : (l : G)⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
      (Subgroup.normalizer (D : Set G)).inv_mem hlNormD
    have hd' : (l : G)⁻¹ * d * (l : G) ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp hlInvNormD d).mp hd
      simpa using this
    have hbB : (b : G) ∈ B := hb
    have hmidB : ((l : G)⁻¹ * d * (l : G)) * (b : G) *
        ((l : G)⁻¹ * d * (l : G))⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hDNormB hd') (b : G)).mp hbB
    have hmidL : ((l : G)⁻¹ * d * (l : G)) * (b : G) *
        ((l : G)⁻¹ * d * (l : G))⁻¹ ∈ L := hBL hmidB
    have hout := L.mul_mem (L.mul_mem l.property hmidL) (L.inv_mem l.property)
    simpa [mul_assoc] using hout
  · simp
  · intro a b _ha _hb ha hb
    simpa [mul_assoc] using L.mul_mem ha hb
  · intro a _ha ha
    simpa [mul_assoc] using L.inv_mem ha

private theorem normalizer_le_normalizer_map_subtype_of_characteristic
    {G : Type*} [Group G] (H : Subgroup G) (K : Subgroup H)
    [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (((K : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  classical
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, hg⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := by
    change xH ∈ Subgroup.comap
      (Subgroup.normalizerMonoidHom H gH).toMonoidHom K
    rw [hfix]
    exact hxK
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

/-- A two-subgroup normalized by `K ⊔ B` and normalizing the two-subgroup
`B` also normalizes `K` when `[K,B] = K`. This is the generic normalizer
transfer in assertion (1) of Stellmacher (5.2). -/
public theorem twoSubgroup_le_normalizer_of_full_commutator
    {G : Type*} [Group G] [Finite G]
    (K B D : Subgroup G)
    (hBtwo : IsPGroup 2 B) (_hDtwo : IsPGroup 2 D)
    (hSupNormD : K ⊔ B ≤ Subgroup.normalizer (D : Set G))
    (hDNormB : D ≤ Subgroup.normalizer (B : Set G))
    (hcomm : ⁅K, B⁆ = K) :
    D ≤ Subgroup.normalizer (K : Set G) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : Subgroup G := K ⊔ B
  have hKL : K ≤ L := le_sup_left
  have hBL : B ≤ L := le_sup_right
  let KL : Subgroup L := K.subgroupOf L
  let BL : Subgroup L := B.subgroupOf L
  have hmapKL : KL.map L.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKL
  have hmapBL : BL.map L.subtype = B :=
    Subgroup.map_subgroupOf_eq_of_le hBL
  have hcommL : ⁅KL, BL⁆ = KL := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, hmapKL, hmapBL, hcomm]
  have hBNormK : B ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hcomm.le
  have hKLnormal : KL.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr
    exact sup_le K.le_normalizer hBNormK
  let _ : KL.Normal := hKLnormal
  let q : L →* L ⧸ KL := QuotientGroup.mk' KL
  have hBLtwo : IsPGroup 2 BL :=
    hBtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm
  have hgenL : KL ⊔ BL = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, hmapKL, hmapBL]
    have hmapTop : (⊤ : Subgroup L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmapTop]
  have hmapBLtop : BL.map q = ⊤ := by
    have hmapGen := congrArg (Subgroup.map q) hgenL
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective KL)] at hmapGen
    simpa using hmapGen
  have hquotTwo : IsPGroup 2 (L ⧸ KL) := by
    have himageTwo : IsPGroup 2 (BL.map q) := hBLtwo.map q
    rw [hmapBLtop] at himageTwo
    exact himageTwo.of_equiv Subgroup.topEquiv
  have hKLchar : KL.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro e
    let Ke : Subgroup L := KL.map e.toMonoidHom
    have hKeNormal : Ke.Normal := hKLnormal.map e.toMonoidHom e.surjective
    let _ : Ke.Normal := hKeNormal
    have hKeQuotTwo : IsPGroup 2 (L ⧸ Ke) := by
      rw [IsPGroup.iff_card] at hquotTwo ⊢
      obtain ⟨n, hn⟩ := hquotTwo
      refine ⟨n, ?_⟩
      calc
        Nat.card (L ⧸ Ke) = Ke.index := (Subgroup.index_eq_card Ke).symm
        _ = KL.index := Subgroup.index_map_equiv KL e
        _ = Nat.card (L ⧸ KL) := Subgroup.index_eq_card KL
        _ = 2 ^ n := hn
    have hle : KL ≤ Ke :=
      le_normal_of_quotient_isPGroup_of_eq_commutator KL BL Ke hKeQuotTwo hcommL
    exact (Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective e.injective).le).symm
  let _ : KL.Characteristic := hKLchar
  have hDNormL : D ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_sup_of_full_commutator K B D hSupNormD hDNormB hcomm
  have hNormK : Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((KL.map L.subtype : Subgroup G) : Set G) :=
    normalizer_le_normalizer_map_subtype_of_characteristic L KL
  rw [hmapKL] at hNormK
  exact hDNormL.trans hNormK

end Subgroup
