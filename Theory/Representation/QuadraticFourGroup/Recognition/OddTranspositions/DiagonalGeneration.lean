module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.QuadraticFourGroup.Recognition.ComponentSpectrum
public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.Definitions

/-!
# Intrinsic diagonal layer: normality and the odd exceptional centre

This file records the group-theoretic consequences that are independent of
the maximality step in GLS2, Theorem 25.14.  In particular, the centre in the
exceptional subgroup is the actual centre of `componentOrbit L B`, and its
two-part vanishes when the ambient two-core does.  The generation statement is
therefore exposed with the precise maximality hypothesis it uses.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/- The layer is invariant under every group isomorphism. -/
private theorem componentLayer_map_equiv_le {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) :
    (componentLayer H).map e.toMonoidHom ≤ componentLayer K := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro C hC
  exact Subgroup.map_le_iff_le_comap.mp (le_sSup (hC.map_equiv e))

private theorem componentLayer_map_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) :
    (componentLayer H).map e.toMonoidHom = componentLayer K := by
  apply le_antisymm (componentLayer_map_equiv_le e)
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact Subgroup.map_le_iff_le_comap.mp (componentLayer_map_equiv_le e.symm)

/- Conjugation by an element of a subgroup normalizer sends the mapped layer
back into itself. -/
private theorem mapped_componentLayer_conj_le_of_mem_normalizer
    {H : Subgroup G} (g : G) (hg : g ∈ normalizer (H : Set G)) :
    ((componentLayer H).map H.subtype).map (MulAut.conj g).toMonoidHom ≤
      (componentLayer H).map H.subtype := by
  have hmap : H.map (MulAut.conj g).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp hg
  let e : H ≃* H :=
    ((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hmap)
  have he : (componentLayer H).map e.toMonoidHom = componentLayer H :=
    componentLayer_map_equiv e
  rw [Subgroup.map_map]
  apply Subgroup.map_le_iff_le_comap.mpr
  intro x hx
  have hxe : e x ∈ componentLayer H := by
    rw [← he]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hx
  exact ⟨e x, hxe, rfl⟩

/- The previous inclusion is an equality, since the inverse conjugation gives
the reverse inclusion. -/
private theorem mapped_componentLayer_conj_eq_of_mem_normalizer
    {H : Subgroup G} (g : G) (hg : g ∈ normalizer (H : Set G)) :
    ((componentLayer H).map H.subtype).map (MulAut.conj g).toMonoidHom =
      (componentLayer H).map H.subtype := by
  have hginv : g⁻¹ ∈ normalizer (H : Set G) :=
    (normalizer (H : Set G)).inv_mem hg
  have hle := mapped_componentLayer_conj_le_of_mem_normalizer (H := H) g hg
  have hle' := mapped_componentLayer_conj_le_of_mem_normalizer (H := H) g⁻¹ hginv
  have hcancel :
      ((componentLayer H).map H.subtype).map
          ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) =
        (componentLayer H).map H.subtype := by
    apply le_antisymm
    · intro z hz
      rcases (Subgroup.mem_map.mp hz) with ⟨y, hy, hzy⟩
      have hident :
          ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) y = y := by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      rw [hident] at hzy
      exact hzy ▸ hy
    · intro z hz
      refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
  have hleft :
      (componentLayer H).map H.subtype ≤
        ((componentLayer H).map H.subtype).map (MulAut.conj g).toMonoidHom := by
    calc
      (componentLayer H).map H.subtype =
          ((componentLayer H).map H.subtype).map
            ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) := hcancel.symm
      _ = (((componentLayer H).map H.subtype).map (MulAut.conj g⁻¹).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by rw [← Subgroup.map_map]
      _ ≤ ((componentLayer H).map H.subtype).map (MulAut.conj g).toMonoidHom :=
        map_mono hle'
  exact le_antisymm hle hleft

/- The four-group normalizes the centralizer of its distinguished member. -/
theorem Hypotheses.fourGroup_normalizes_centralizer
    (h : Hypotheses ρ L B a) :
    B ≤ normalizer (Subgroup.centralizer ({a} : Set G)) := by
  let := h.elementary
  apply le_normalizer_iff.mpr
  intro b hb x hx
  have hab : Commute a (b : G) := by
    exact (mem_centralizer_singleton_iff.mp (h.fourGroup_le_centralizer hb)).symm
  have hax : Commute a x := (mem_centralizer_singleton_iff.mp hx).symm
  exact mem_centralizer_singleton_iff.mpr
    ((hab.mul_right hax).mul_right hab.inv_right).symm

/- Under ambient generation, B normalizes the actual local centralizer. -/
theorem Hypotheses.fourGroup_normalizes_orbitCentralizer [Finite G]
    (h : Hypotheses ρ L B a) (hgen : L ⊔ B = ⊤) :
    B ≤ normalizer (orbitCentralizer L B a : Set G) := by
  have hE : (componentOrbit L B).Normal := by
    have hn := (normal_subgroupOf_iff_le_normalizer (componentOrbit_le_sup L B)).mp
      (componentOrbit_normal_subgroupOf_sup L B)
    rw [hgen] at hn
    exact normalizer_eq_top_iff.mp (top_unique hn)
  have hBE : B ≤ normalizer (componentOrbit L B : Set G) := by
    rw [normalizer_eq_top]
    exact le_top
  have hBC : B ≤ normalizer (Subgroup.centralizer ({a} : Set G)) :=
    h.fourGroup_normalizes_centralizer
  exact (le_inf hBE hBC).trans inf_normalizer_le_normalizer_inf

/- The actual diagonal layer is B-invariant. -/
theorem Hypotheses.diagonalLayer_normalized [Finite G]
    (h : Hypotheses ρ L B a) (hgen : L ⊔ B = ⊤) :
    B ≤ normalizer (diagonalLayer L B a : Set G) := by
  intro b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hbH := h.fourGroup_normalizes_orbitCentralizer hgen hb
  simpa [diagonalLayer] using
    (mapped_componentLayer_conj_eq_of_mem_normalizer
      (H := orbitCentralizer L B a) b hbH)

/- Normalization gives the containment half of the source commutator identity. -/
theorem Hypotheses.diagonalLayer_commutator_le [Finite G]
    (h : Hypotheses ρ L B a) (hgen : L ⊔ B = ⊤) :
    ⁅diagonalLayer L B a, B⁆ ≤ diagonalLayer L B a :=
  le_normalizer_iff_commutator_le_left.mp (h.diagonalLayer_normalized hgen)

/- A normal ambient orbit has trivial intrinsic two-core under a trivial
ambient two-core. -/
theorem componentOrbit_twoCore_eq_bot_of_sup_eq_top
    [Finite G] (hgen : L ⊔ B = ⊤) (hcore : pCore 2 G = ⊥) :
    pCore 2 (componentOrbit L B) = ⊥ := by
  let E := componentOrbit L B
  let : E.Normal := by
    have hn := (normal_subgroupOf_iff_le_normalizer (componentOrbit_le_sup L B)).mp
      (componentOrbit_normal_subgroupOf_sup L B)
    rw [hgen] at hn
    exact normalizer_eq_top_iff.mp (top_unique hn)
  have hn : ((pCore 2 E).map E.subtype).Normal := inferInstance
  have hle : (pCore 2 E).map E.subtype ≤ pCore 2 G :=
    le_sSup ⟨hn, pCore_isPGroup.map E.subtype⟩
  rw [hcore] at hle
  have hmap : (pCore 2 E).map E.subtype = ⊥ := le_bot_iff.mp hle
  have hp : pCore 2 E ≤ E.subtype.ker :=
    (Subgroup.map_eq_bot_iff (pCore 2 E) (f := E.subtype)).mp hmap
  rw [(MonoidHom.ker_eq_bot_iff E.subtype).mpr E.subtype_injective] at hp
  exact le_bot_iff.mp hp

/- The centre of an ambient-normal orbit is ambient normal. -/
theorem orbitCenter_normal_of_sup_eq_top [Finite G]
    (hgen : L ⊔ B = ⊤) :
    (orbitCenter L B).Normal := by
  let E := componentOrbit L B
  let : E.Normal := by
    have hn := (normal_subgroupOf_iff_le_normalizer (componentOrbit_le_sup L B)).mp
      (componentOrbit_normal_subgroupOf_sup L B)
    rw [hgen] at hn
    exact normalizer_eq_top_iff.mp (top_unique hn)
  let : (center E).Characteristic := Subgroup.centerCharacteristic
  exact ConjAct.normal_of_characteristic_of_normal

/- Trivial ambient two-core forces the mapped orbit centre to have odd order. -/
theorem orbitCenter_odd_of_sup_eq_top [Finite G]
    (hgen : L ⊔ B = ⊤) (hcore : pCore 2 G = ⊥) :
    Odd (Nat.card (orbitCenter L B)) := by
  let E := componentOrbit L B
  let : E.Normal := by
    have hn := (normal_subgroupOf_iff_le_normalizer (componentOrbit_le_sup L B)).mp
      (componentOrbit_normal_subgroupOf_sup L B)
    rw [hgen] at hn
    exact normalizer_eq_top_iff.mp (top_unique hn)
  have hEcore : pCore 2 E = ⊥ :=
    componentOrbit_twoCore_eq_bot_of_sup_eq_top hgen hcore
  have hcenter : ¬ 2 ∣ Nat.card (center E) := by
    intro hd
    let P : Sylow 2 (center E) := default
    have hPnormal : (P : Subgroup (center E)).Normal :=
      Subgroup.normal_of_isMulCommutative _
    let : (center E).Normal := inferInstance
    let : (P : Subgroup (center E)).Normal := hPnormal
    let : (P : Subgroup (center E)).Characteristic :=
      Sylow.characteristic_of_normal P hPnormal
    let : ((P : Subgroup (center E)).map (center E).subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hQnormal : ((P : Subgroup (center E)).map (center E).subtype).Normal := inferInstance
    have hQle : (P : Subgroup (center E)).map (center E).subtype ≤ pCore 2 E :=
      le_sSup ⟨hQnormal, (P.isPGroup').map (center E).subtype⟩
    have hP : (P : Subgroup (center E)) = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hx' : (x : E) ∈ (P : Subgroup (center E)).map (center E).subtype :=
        ⟨x, hx, rfl⟩
      have hone : (x : E) = 1 := by
        simpa only [hEcore, mem_bot] using hQle hx'
      exact mem_bot.mpr (Subtype.ext hone)
    have hi := P.not_dvd_index
    rw [hP, index_bot] at hi
    exact hi hd
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hcard : Nat.card (orbitCenter L B) = Nat.card (center E) :=
    Subgroup.card_map_of_injective E.subtype_injective
  exact hcenter (hcard ▸ even_iff_two_dvd.mp heven)

theorem orbitCenter_card_eq_center_card [Finite G]
    (L B : Subgroup G) :
    Nat.card (orbitCenter L B) = Nat.card (center (componentOrbit L B)) := by
  exact Subgroup.card_map_of_injective (componentOrbit L B).subtype_injective

/- Every exceptional element has an odd-order diagonal displacement.  The
quotient by the orbit centre is the clean way to avoid choosing a product
normal form in the subgroup join. -/
theorem Hypotheses.diagonal_product_mem_orbitCenter_of_mem_exceptional [Finite G]
    (h : Hypotheses ρ L B a) (hgen : L ⊔ B = ⊤)
    {x : G} (hx : x ∈ orbitCenter L B ⊔ diagonalOvergroup L B a) :
    a * (x⁻¹ * a * x) ∈ orbitCenter L B := by
  let Z := orbitCenter L B
  let : Z.Normal := orbitCenter_normal_of_sup_eq_top hgen
  let q : G →* (G ⧸ Z) := QuotientGroup.mk' Z
  have hZq : Z ≤ (Subgroup.centralizer ({q a} : Set (G ⧸ Z))).comap q := by
    intro z hz
    apply mem_centralizer_singleton_iff.mpr
    have hzq : q z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    simp [hzq]
  have hYq : diagonalOvergroup L B a ≤
      (Subgroup.centralizer ({q a} : Set (G ⧸ Z))).comap q := by
    intro y hy
    change q y ∈ Subgroup.centralizer ({q a} : Set (G ⧸ Z))
    apply mem_centralizer_singleton_iff.mpr
    have hyc := mem_centralizer_singleton_iff.mp
      (h.diagonalOvergroup_le_centralizer hy)
    simpa only [map_mul] using congrArg q hyc
  have hqx : q x ∈ Subgroup.centralizer ({q a} : Set (G ⧸ Z)) :=
    (sup_le hZq hYq) hx
  have hcomm : q x * q a = q a * q x :=
    mem_centralizer_singleton_iff.mp hqx
  apply (QuotientGroup.eq_one_iff _).mp
  change q (a * (x⁻¹ * a * x)) = 1
  simp only [map_mul, map_inv]
  have hcommC : Commute (q x) (q a) := hcomm
  rw [hcommC.inv_left.eq]
  have ha2 : a ^ 2 = 1 := by rw [← h.involution]; exact pow_orderOf_eq_one _
  have hqa2 : q a * q a = 1 := by
    simpa [pow_two] using congrArg q ha2
  calc
    q a * (q a * (q x)⁻¹ * q x) = (q a * q a) * ((q x)⁻¹ * q x) := by group
    _ = 1 := by rw [hqa2]; simp

theorem Hypotheses.diagonal_product_odd_of_mem_exceptional [Finite G]
    (h : Hypotheses ρ L B a) (hgen : L ⊔ B = ⊤) (hcore : pCore 2 G = ⊥)
    {x : G} (hx : x ∈ orbitCenter L B ⊔ diagonalOvergroup L B a) :
    Odd (orderOf (a * (x⁻¹ * a * x))) := by
  have hd := h.diagonal_product_mem_orbitCenter_of_mem_exceptional hgen hx
  exact Odd.of_dvd_nat (orbitCenter_odd_of_sup_eq_top hgen hcore)
    (Subgroup.orderOf_dvd_natCard _ hd)

/- Maximality and normalizer control are exactly the two hypotheses used in
the source's diagonal generation step. -/
theorem diagonal_generation_of_coatom_of_normalizer_control
    {Y Z : Subgroup G} (hY : IsCoatom Y)
    (hN : normalizer (Y : Set G) ≤ Z ⊔ Y) {x : G}
    (hx : x ∉ Z ⊔ Y) :
    Y ⊔ Y.map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  have hxN : x ∉ normalizer (Y : Set G) := by
    intro hxN
    exact hx (hN hxN)
  have hneq : Y ≠ Y.map (MulAut.conj x⁻¹).toMonoidHom := by
    intro heq
    have hxi : x⁻¹ ∈ normalizer (Y : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr heq.symm
    exact hxN (by simpa using (normalizer (Y : Set G)).inv_mem hxi)
  have hYx : IsCoatom (Y.map (MulAut.conj x⁻¹).toMonoidHom) := by
    change IsCoatom ((MulAut.conj x⁻¹).mapSubgroup Y)
    exact (OrderIso.isCoatom_iff (MulAut.conj x⁻¹).mapSubgroup Y).mpr hY
  exact hY.sup_eq_top_of_ne hYx hneq

theorem Hypotheses.diagonal_generation_of_coatom_and_normalizer_control [Finite G]
    (h : Hypotheses ρ L B a) (hgen : L ⊔ B = ⊤) (hcore : pCore 2 G = ⊥)
    (hY : IsCoatom (diagonalOvergroup L B a))
    (hN : normalizer (diagonalOvergroup L B a : Set G) ≤
      orbitCenter L B ⊔ diagonalOvergroup L B a) :
    ∀ x : G, orderOf (a * (x⁻¹ * a * x)) = 2 →
      diagonalOvergroup L B a ⊔
        (diagonalOvergroup L B a).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  intro x hxorder
  by_cases hx : x ∈ orbitCenter L B ⊔ diagonalOvergroup L B a
  · have hodd := h.diagonal_product_odd_of_mem_exceptional hgen hcore hx
    have : Odd 2 := by simpa [hxorder] using hodd
    exact (by norm_num at this)
  · exact diagonal_generation_of_coatom_of_normalizer_control hY hN hx

end Representation.QuadraticFourGroup

end
