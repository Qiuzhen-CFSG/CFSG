module

public import Theory.SpecificGroups.MacWilliams.HallJankoSubgroups
public import Theory.SpecificGroups.MacWilliams.HallJankoCentricCensus
public import Theory.SpecificGroups.MacWilliams.HallJankoElementarySixteen
public import Theory.GroupTheory.SubgroupLocalStructureTransport
public import Theory.GroupTheory.CentricRadicalCertificates

/-!
# Assembly of the Hall–Janko intrinsic candidate calculation

The finite calculation has two parts. A centric-subgroup census either gives
an outside normalizer element acting trivially on the Frattini quotient, or
identifies one of three useful shapes. The first possibility contradicts
intrinsic radicality. In the exceptional elementary-sixteen shape, a normalizer
of order sixty-four whose squares lie in the sixteen has elementary conjugation
image of order four. Pointwise centralizer data identify its common fixed four.

The theorem `candidates` combines the certified finite census and normalizer
calculation and transports the alternatives to any isomorphic group. Uniqueness
of the normal elementary four identifies the marked subgroup under the
isomorphism. No ambient fusion or solvable automorphism calculation is used.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.4, p.386 and its
application p.395; MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow.HallJankoRadicalCandidates

open Subgroup

variable {P : Type*} [Group P] [Finite P]

omit [Finite P] in
/-- Uniqueness of the normal elementary four identifies the concrete marked
subgroup under any realization of the coordinate group. -/
public theorem marked_four_map_eq
    (e : HallJankoCoordinates.Code ≃* P) (W : Subgroup P)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) :
    HallJankoCoordinates.four.map e.toMonoidHom = W := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply hunique
  · exact Normal.map inferInstance e.toMonoidHom e.surjective
  · exact IsElementaryAbelian.map e.toMonoidHom
  · exact (card_map_of_injective e.injective).trans HallJankoCoordinates.four_card

/-- A Frattini witness eliminates a centric candidate; a central omega identity
makes the marked four characteristic. This is the bridge from finite subgroup
certificates to the intrinsic radical condition. -/
public theorem shape_of_census
    (hP : IsPGroup 2 P) (W U : Subgroup P)
    (hcent : centralizer (U : Set P) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hcensus :
      (∃ g : normalizer (U : Set P), (g : P) ∉ U ∧
        ∀ x : U, x⁻¹ * U.normalizerMonoidHom g x ∈ frattini U) ∨
      (W ≤ U ∧
        (((omega₁ (center U) (p := 2)).map (center U).subtype).map U.subtype = W ∨
          (center U).map U.subtype = center P ∨
          IsElementaryAbelian 2 U ∧ Nat.card U = 16))) :
    W ≤ U ∧ ((W.subgroupOf U).Characteristic ∨
      (center U).map U.subtype = center P ∨
      IsElementaryAbelian 2 U ∧ Nat.card U = 16) := by
  rcases hcensus with ⟨g, hg, hact⟩ | ⟨hWU, hshape⟩
  · exact False.elim (hg (mem_of_intrinsic_radical_of_frattini_action_eq_one U
      (hP.to_subgroup U) hcent hrad g
      (quotientAut_eq_one_of_displacements (frattini U) _ hact)))
  refine ⟨hWU, ?_⟩
  rcases hshape with hfour | hcenter | helemen
  · left
    let O := omega₁ (center U) (p := 2)
    let : O.Characteristic := omega₁_characteristic _
    have hchar : (O.map (center U).subtype).Characteristic :=
      characteristic_of_characteristic_of_characteristic
    have heq : W.subgroupOf U = O.map (center U).subtype := by
      apply map_injective U.subtype_injective
      rw [map_subgroupOf_eq_of_le hWU]
      exact hfour.symm
    exact heq.symm ▸ hchar
  · exact Or.inr (Or.inl hcenter)
  · exact Or.inr (Or.inr helemen)

omit [Finite P] in
/-- Raw multiplication and cardinality certificates for an elementary sixteen
supply the exact normalizer-image and fixed-point data used by the consumer. -/
public theorem elementary_image_of_normalizer_data
    (W U : Subgroup P)
    (hcent : centralizer (U : Set P) = U)
    (hU : Nat.card U = 16)
    (hN : Nat.card (normalizer (U : Set P)) = 64)
    (hsq : ∀ g : normalizer (U : Set P), (g : P) ^ 2 ∈ U)
    (hfixed : ∀ g : normalizer (U : Set P), (g : P) ∉ U →
      ∀ u : U, (g : P) * (u : P) = (u : P) * (g : P) ↔ (u : P) ∈ W) :
    IsElementaryAbelian 2 U.normalizerMonoidHom.range ∧
      Nat.card U.normalizerMonoidHom.range = 4 ∧
      ∀ a : U.normalizerMonoidHom.range, a ≠ 1 →
        ∀ u : U, (a : MulAut U) u = u ↔ (u : P) ∈ W := by
  let f := U.normalizerMonoidHom
  have hker : f.ker = U.subgroupOf (normalizer (U : Set P)) := by
    rw [normalizerMonoidHom_ker, hcent]
  have hpow : ∀ a : f.range, a ^ 2 = 1 := by
    intro a
    obtain ⟨g, hg⟩ := a.property
    apply Subtype.ext
    change (a : MulAut U) ^ 2 = 1
    rw [← hg, ← map_pow]
    change g ^ 2 ∈ f.ker
    rw [hker]
    exact hsq g
  have hinv (a : f.range) : a⁻¹ = a := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hpow a
  have helem : IsElementaryAbelian 2 f.range := {
    toIsMulCommutative := isMulCommutative_iff.mpr (fun a b => by
      calc
        a * b = (a * b)⁻¹ := (hinv _).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
        _ = b * a := by rw [hinv, hinv])
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  have hkcard : Nat.card f.ker = 16 := by
    rw [hker]
    exact (Nat.card_congr (subgroupOfEquivOfLe U.le_normalizer).toEquiv).trans hU
  have hcard := f.ker.card_mul_index
  rw [index_ker, hkcard, hN] at hcard
  change 16 * Nat.card U.normalizerMonoidHom.range = 64 at hcard
  refine ⟨helem, by omega, ?_⟩
  intro a ha u
  obtain ⟨g, hg⟩ := a.property
  have hgout : (g : P) ∉ U := by
    intro hgu
    have hgker : g ∈ f.ker := by rw [hker]; exact hgu
    apply ha
    apply Subtype.ext
    exact hg.symm.trans hgker
  rw [← hg]
  have hiff : f g u = u ↔ (g : P) * (u : P) = (u : P) * (g : P) := by
    rw [Subtype.ext_iff]
    exact mul_inv_eq_iff_eq_mul
  exact hiff.trans (hfixed g hgout u)

variable {Q : Type*} [Group Q]

omit [Finite P] in
private theorem map_centralizer (e : P ≃* Q) (U : Subgroup P) :
    (centralizer (U : Set P)).map e.toMonoidHom =
      centralizer (U.map e.toMonoidHom : Set Q) := by
  apply le_antisymm (map_centralizer_le_centralizer_image (U : Set P) e.toMonoidHom)
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  intro x hx
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    hy (e x) (mem_map_of_mem e.toMonoidHom hx)

omit [Finite P] in
private theorem map_center (e : P ≃* Q) :
    (center P).map e.toMonoidHom = center Q := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using
      congrArg e (mem_center_iff.mp hx z)
  · intro y hy
    refine ⟨e.symm y, mem_center_iff.mpr ?_, e.apply_symm_apply y⟩
    intro x
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hy (e x)

omit [Finite P] in
/-- Every centric intrinsic radical subgroup in a Hall--Janko realization
contains the unique normal elementary four. The four is characteristic in the
candidate, or the candidate has the ambient center, or it is an elementary
sixteen whose normalizer image is an elementary four, every nonidentity element
of which fixes exactly the marked four.

The model and uniqueness suffice: no extra central-omega or normal-rank
hypotheses are needed. -/
public theorem candidates
    (hmodel : Nonempty (P ≃* HallJankoSylow)) (W : Subgroup P)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (U : Subgroup P)
    (hcent : centralizer (U : Set P) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range) :
    W ≤ U ∧ ((W.subgroupOf U).Characteristic ∨
      (center U).map U.subtype = center P ∨
      (IsElementaryAbelian 2 U ∧ Nat.card U = 16 ∧
        IsElementaryAbelian 2 U.normalizerMonoidHom.range ∧
        Nat.card U.normalizerMonoidHom.range = 4 ∧
        ∀ a : U.normalizerMonoidHom.range, a ≠ 1 →
          ∀ u : U, (a : MulAut U) u = u ↔ (u : P) ∈ W)) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m⟩ := hmodel
  let e : P ≃* HallJankoCoordinates.Code := m.trans HallJankoCoordinates.equiv.symm
  let V := U.map e.toMonoidHom
  have hback : V.map e.symm.toMonoidHom = U := by simp [V, map_map]
  have hWmap : W.map e.toMonoidHom = HallJankoCoordinates.four := by
    rw [← marked_four_map_eq e.symm W hunique]
    simp [map_map]
  have hWmem (x : P) : e x ∈ HallJankoCoordinates.four ↔ x ∈ W := by
    rw [← hWmap]
    exact mem_map_iff_mem (f := e.toMonoidHom) e.injective
  have hcV : centralizer (V : Set HallJankoCoordinates.Code) ≤ V := by
    rw [← map_centralizer e U]
    exact map_mono hcent
  have htwo : IsPGroup 2 HallJankoCoordinates.Code :=
    IsPGroup.of_card (n := 7) HallJankoCoordinates.card
  obtain ⟨hfour, hshape⟩ := shape_of_census htwo HallJankoCoordinates.four V hcV
    (intrinsic_radical_map U e 2 hrad)
    (HallJankoCoordinates.CentricCensus.centric_census V hcV)
  have hWU : W ≤ U := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rwa [hWmap]
  refine ⟨hWU, ?_⟩
  rcases hshape with hchar | hcenter | ⟨helem, hcard⟩
  · left
    let u := e.subgroupMap U
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    have hx' : u x ∈ HallJankoCoordinates.four.subgroupOf V :=
      (hWmem x).mpr hx
    have hh := characteristic_iff_le_comap.mp hchar (MulAut.congr u a) hx'
    change (u (a (u.symm (u x))) : HallJankoCoordinates.Code) ∈
      HallJankoCoordinates.four at hh
    rw [u.symm_apply_apply] at hh
    exact (hWmem (a x)).mp hh
  · right; left
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [← centralizer_eq_mapped_center_of_le U hcent, map_centralizer,
      centralizer_eq_mapped_center_of_le V hcV, hcenter, map_center]
  · right; right
    let : IsElementaryAbelian 2 V := helem
    have helemU : IsElementaryAbelian 2 U := by
      rw [← hback]
      exact IsElementaryAbelian.map e.symm.toMonoidHom
    have hcardU : Nat.card U = 16 :=
      (card_map_of_injective e.injective).symm.trans hcard
    refine ⟨helemU, hcardU, elementary_image_of_normalizer_data W U ?_ hcardU ?_ ?_ ?_⟩
    · apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_centralizer]
      exact HallJankoCoordinates.elementary_sixteen_centralizer V hcard
    · have hn := HallJankoCoordinates.elementary_sixteen_normalizer_card V hcard
      rw [← map_equiv_normalizer_eq U e, card_map_of_injective e.injective] at hn
      exact hn
    · intro g
      let g' : normalizer (V : Set HallJankoCoordinates.Code) :=
        ⟨e g, le_normalizer_map e.toMonoidHom (mem_map_of_mem _ g.property)⟩
      have hs := HallJankoCoordinates.elementary_sixteen_normalizer_square V hcard g'
      apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
      simpa only [g', MulEquiv.coe_toMonoidHom, map_pow] using hs
    · intro g hg x
      let g' : normalizer (V : Set HallJankoCoordinates.Code) :=
        ⟨e g, le_normalizer_map e.toMonoidHom (mem_map_of_mem _ g.property)⟩
      let x' : V := e.subgroupMap U x
      have hg' : (g' : HallJankoCoordinates.Code) ∉ V := by
        intro h
        exact hg ((mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp h)
      have hf := HallJankoCoordinates.elementary_sixteen_normalizer_fixed V hcard g' hg' x'
      change (e g * e x = e x * e g ↔ e x ∈ HallJankoCoordinates.four) at hf
      rw [← map_mul, ← map_mul, e.injective.eq_iff, hWmem] at hf
      exact hf

end MacWilliamsSylow.HallJankoRadicalCandidates
