module

public import Stellmacher.Recognition.NormalEightFusedWeakClosure
public import Theory.GroupTheory.CentricRadicalCharacterFusion
public import Theory.GroupTheory.IntrinsicRadicalTransport
public import Theory.GroupTheory.ElementarySixteenFourAutomizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.SpecificGroups.MacWilliams.HallJankoCenter
public import Theory.SpecificGroups.MacWilliams.HallJankoRadicalCandidates
public import Stellmacher.Recognition.NormalFourOddCoreSetup

/-!
# The marked Hall–Janko Sylow exclusion

To exclude the marked Hall–Janko Sylow configuration, it suffices to show that
the normalizers of its centric intrinsic radical candidates preserve membership
in the marked four. The checked conjugation-family theorem then gives strong
closure, hence weak closure. Hall transfer contradicts weak closure of the
fused four in the nonsolvable simple ambient group.

The intrinsic candidate calculation leaves three cases: the four is
characteristic, the candidate center is the Sylow center, or the candidate is
an elementary sixteen. The normal odd-core quotient image controls the second
case. In the third, the ambient normalizer acts solvably, and its Sylow image
has common fixed subgroup the marked four; the solvable automizer theorem
therefore preserves that four. This proves the requested explicit-model
exclusion without assuming a classification theorem.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.4, printed p.386,
and its application on p.395; MacWilliams, Trans. Amer. Math. Soc. 150
(1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace Stellmacher.Recognition.HallJankoTrivialSylowAutomizer

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The local membership assertion needed at each intrinsic radical fusion step.
The Sylow normalizer condition is expressed by equality of two-parts. -/
public def RadicalNormalizerControl (S : Sylow 2 G) (W : Subgroup S) : Prop :=
  ∀ U : Subgroup G, U ≤ (S : Subgroup G) →
    (Nat.card ↥((S : Subgroup G) ⊓ normalizer (U : Set G))).factorization 2 =
      (Nat.card (normalizer (U : Set G))).factorization 2 →
    ((S : Subgroup G) ⊓ centralizer (U : Set G)) ≤ U →
    (((S : Subgroup G).subgroupOf (normalizer (U : Set G))).map
      U.normalizerMonoidHom ⊓ pCore 2 (MulAut U)) ≤
        (MulAut.conj : U →* MulAut U).range →
    ∀ g : G, g ∈ normalizer (U : Set G) →
    ∀ x : S, (x : G) ∈ U → x ∈ W →
      g⁻¹ * (x : G) * g ∈ W.map (S : Subgroup G).subtype

omit [Finite G] in
/-- A characteristic copy of the four is preserved by the entire ambient
normalizer of a candidate. -/
public theorem normalizer_le_four_normalizer_of_characteristic
    (S : Sylow 2 G) (W : Subgroup S) (U : Subgroup G)
    (hWU : W.map (S : Subgroup G).subtype ≤ U)
    [((W.map (S : Subgroup G).subtype).subgroupOf U).Characteristic] :
    normalizer (U : Set G) ≤ normalizer (W.map (S : Subgroup G).subtype : Set G) := by
  simpa only [map_subgroupOf_eq_of_le hWU] using
    normalizer_le_normalizer_characteristic_image U
      ((W.map (S : Subgroup G).subtype).subgroupOf U)

/-- If a candidate has ambient center equal to the central omega line, its
normalizer preserves the four by the normal odd-core quotient image. -/
public theorem normalizer_le_four_normalizer_of_center_eq
    (S : Sylow 2 G) (W : Subgroup S)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (U : Subgroup G) (hUS : U ≤ (S : Subgroup G))
    (hWU : W.map (S : Subgroup G).subtype ≤ U)
    (hcenter : (center U).map U.subtype = NormalFourCentralOmegaTwo.centralOmega S) :
    normalizer (U : Set G) ≤ normalizer (W.map (S : Subgroup G).subtype : Set G) := by
  have hNO : normalizer (U : Set G) ≤ NormalFourCentralOmegaTwo.omegaNormalizer S := by
    simpa only [hcenter] using normalizer_le_normalizer_characteristic_image U (center U)
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply NormalFourCentralOmegaTwo.conjugate_four_eq_of_mem_omegaNormalizer S W g (hNO hg)
  exact ((map_mono hWU).trans
    (mem_normalizer_iff_map_conj_eq.mp hg).le).trans hUS

/-- Local normalizer control confines every returning conjugate of an element
of the four to the four. -/
public theorem mem_four_of_isConj_of_radical_normalizer_control
    (S : Sylow 2 G) (W : Subgroup S) (hlocal : RadicalNormalizerControl S W)
    {x y : S} (hx : x ∈ W) (hxy : IsConj (x : G) (y : G)) : y ∈ W := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := S.intrinsic_radical_fusion_relation (fun a b => a ∈ W → b ∈ W)
    (fun _ ha => ha) (fun hab hbc ha => hbc (hab ha)) ?_ hxy
  · exact h hx
  intro U hUS hext hcent hrad g hg a b ha hab haW
  have hb := hlocal U hUS hext hcent hrad g hg a ha haW
  rw [hab] at hb
  obtain ⟨w, hw, hwb⟩ := hb
  exact (Subtype.ext hwb : w = b) ▸ hw

/-- Strong closure supplied by the radical fusion steps implies weak closure
of the whole four. -/
public theorem weakly_closed_of_radical_normalizer_control
    (S : Sylow 2 G) (W : Subgroup S) (hlocal : RadicalNormalizerControl S W)
    (g : G)
    (hreturn : (W.map (S : Subgroup G).subtype).map
      (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G)) :
    (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
      W.map (S : Subgroup G).subtype := by
  apply eq_of_le_of_card_ge
  · rintro y ⟨v, ⟨x, hx, rfl⟩, rfl⟩
    have hyS : (MulAut.conj g) (x : G) ∈ (S : Subgroup G) :=
      hreturn (mem_map_of_mem _ (mem_map_of_mem _ hx))
    let y : S := ⟨(MulAut.conj g) (x : G), hyS⟩
    have hyW : y ∈ W := mem_four_of_isConj_of_radical_normalizer_control S W hlocal
      hx (isConj_iff.mpr ⟨g, rfl⟩)
    exact mem_map_of_mem (S : Subgroup G).subtype hyW
  · rw [card_map_of_injective (K := W.map (S : Subgroup G).subtype)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]

/-- The ambient contradiction once intrinsic radical normalizers have been
shown to preserve the marked four. The model-specific calculations discharge
`hlocal`; they are separate from this transfer argument. -/
public theorem false_of_radical_normalizer_control [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (hlocal : RadicalNormalizerControl S W) : False := by
  exact NormalEightFusedWeakClosure.false_of_weakly_closed hns S B (by omega)
    hZ hno W hW hfused (weakly_closed_of_radical_normalizer_control S W hlocal)

/-- Full two-part order makes the intersection with the Sylow subgroup a Sylow
subgroup of the local normalizer. -/
private theorem sylow_restriction (S : Sylow 2 G) (N : Subgroup G)
    (hext : (Nat.card ↥((S : Subgroup G) ⊓ N)).factorization 2 =
      (Nat.card N).factorization 2) :
    ∃ P : Sylow 2 N, (P : Subgroup N) = (S : Subgroup G).subgroupOf N := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Subgroup N := (S : Subgroup G).subgroupOf N
  have hTp : IsPGroup 2 T := S.isPGroup'.comap_of_injective N.subtype N.subtype_injective
  have hcardT : Nat.card T = Nat.card ↥((S : Subgroup G) ⊓ N) := by
    have hRT : T = ((S : Subgroup G) ⊓ N).subgroupOf N := by ext x; simp [T]
    rw [hRT]
    exact Nat.card_congr (subgroupOfEquivOfLe (show (S : Subgroup G) ⊓ N ≤ N from inf_le_right)).toEquiv
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTp
  have hfac : (Nat.card T).factorization 2 = n := by rw [hn, Nat.factorization_pow_self Nat.prime_two]
  have hnN : n = (Nat.card N).factorization 2 := by rw [← hfac, hcardT]; exact hext
  refine ⟨Sylow.ofCard T ?_, rfl⟩
  exact hn.trans (congrArg (fun z : ℕ => 2 ^ z) hnN)

private theorem elementary_of_injective {A B : Type*} [Group A] [Group B]
    [IsElementaryAbelian 2 B] (f : A →* B) (hf : Function.Injective f) :
    IsElementaryAbelian 2 A := by
  refine { toIsMulCommutative := isMulCommutative_iff.mpr ?_
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · intro x y
    apply hf
    simp only [map_mul]
    exact (isMulCommutative_iff.mp (inferInstance : IsMulCommutative B) (f x) (f y))
  · intro x
    apply hf
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 B) (f x)

/-- Pull the ambient normalizer action back to the intrinsic elementary
sixteen. Its Sylow image is exactly the certified intrinsic automizer, so the
solvable common-fixed-four theorem applies. -/
private theorem elementary_normalizer_control
    (hN : Stellmacher.IsNTwoGroup G) (S : Sylow 2 G) (W : Subgroup S)
    (hW : Nat.card W = 4) (U : Subgroup G) (hUS : U ≤ (S : Subgroup G))
    (hext : (Nat.card ↥((S : Subgroup G) ⊓ normalizer (U : Set G))).factorization 2 =
      (Nat.card (normalizer (U : Set G))).factorization 2)
    (hWU : W ≤ U.subgroupOf (S : Subgroup G))
    [IsElementaryAbelian 2 (U.subgroupOf (S : Subgroup G))]
    (hUcard : Nat.card (U.subgroupOf (S : Subgroup G)) = 16)
    [IsElementaryAbelian 2 (U.subgroupOf (S : Subgroup G)).normalizerMonoidHom.range]
    (hRcard : Nat.card (U.subgroupOf (S : Subgroup G)).normalizerMonoidHom.range = 4)
    (hfixed : ∀ a : (U.subgroupOf (S : Subgroup G)).normalizerMonoidHom.range,
      a ≠ 1 → ∀ u : U.subgroupOf (S : Subgroup G), (a : MulAut _) u = u ↔ (u : S) ∈ W) :
    ∀ g : G, g ∈ normalizer (U : Set G) → ∀ x : S, (x : G) ∈ U → x ∈ W →
      g⁻¹ * (x : G) * g ∈ W.map (S : Subgroup G).subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := U.subgroupOf (S : Subgroup G)
  let e : V ≃* U := subgroupOfEquivOfLe hUS
  let N := normalizer (U : Set G)
  let f : N →* MulAut V := (MulAut.congr e.symm).toMonoidHom.comp U.normalizerMonoidHom
  let K := f.range
  have hUcard' : Nat.card U = 16 := (Nat.card_congr e.toEquiv).symm.trans hUcard
  have : Group.IsSolvable N := hN N ⟨U, (by intro h; simp [h] at hUcard'),
    (S.isPGroup'.to_subgroup V).of_equiv e, rfl⟩
  have : Group.IsSolvable K := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := sylow_restriction S N hext
  let Q : Sylow 2 K := P.mapSurjective f.rangeRestrict_surjective
  have hQR : (Q : Subgroup K).map K.subtype = V.normalizerMonoidHom.range := by
    change ((P : Subgroup N).map f.rangeRestrict).map K.subtype = _
    rw [map_map]
    change (P : Subgroup N).map f = _
    rw [hP]
    change ((S : Subgroup G).subgroupOf N).map
      ((MulAut.congr e.symm).toMonoidHom.comp U.normalizerMonoidHom) = _
    rw [← map_map, ← normalizer_range_subgroupOf_map_congr U (S : Subgroup G) hUS,
      map_map]
    have hh : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut V) := by ext a x; simp
    rw [hh, map_id]
  let q : Q ≃* V.normalizerMonoidHom.range :=
    ((Q : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hQR)
  have : IsElementaryAbelian 2 Q := elementary_of_injective q.toMonoidHom q.injective
  have hQcard : Nat.card Q = 4 := (Nat.card_congr q.toEquiv).trans hRcard
  let F := W.subgroupOf V
  have hF : Nat.card F = 4 := (Nat.card_congr (subgroupOfEquivOfLe hWU).toEquiv).trans hW
  have hfixQ : ∀ a : Q, a ≠ 1 → ∀ x : V, (((a : K) : MulAut V) x = x ↔ x ∈ F) := by
    intro a ha x
    exact hfixed (q a) (fun h => ha (q.injective (h.trans q.map_one.symm))) x
  intro g hg x hx hxW
  let gi : N := ⟨g⁻¹, inv_mem hg⟩
  have hinv := map_eq_of_solvable_aut16_common_fixed_four hUcard K Q hQcard F hF hfixQ
    (f.rangeRestrict gi)
  have hxF : (⟨x, hx⟩ : V) ∈ F := hxW
  have hout : f gi (⟨x, hx⟩ : V) ∈ F := by
    rw [← hinv]
    exact mem_map_of_mem _ hxF
  have hm := mem_map_of_mem (S : Subgroup G).subtype hout
  change g⁻¹ * (x : G) * (g⁻¹)⁻¹ ∈ W.map (S : Subgroup G).subtype at hm
  simpa only [inv_inv] using hm

private theorem center_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : (center A).map e.toMonoidHom = center B := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    change e z * e x = e x * e z
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
  · intro y hy
    refine ⟨e.symm y, mem_center_iff.mpr ?_, e.apply_symm_apply y⟩
    intro x
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hy (e x)


/-- A nonsolvable simple N₂-group cannot have the explicit Hall–Janko Sylow
model with the marked fused four and normal odd-core quotient image specified
here. The intrinsic candidate calculation requires neither a condition on
the Sylow normalizer nor containment of the four in the chosen sixteen. -/
public theorem false_of_marked_hallJanko [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (hmodel : Nonempty (S ≃* MacWilliamsSylow.HallJankoSylow))
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 → IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) : False := by
  apply false_of_radical_normalizer_control hns S hZ hno W hW hfused B hB
  intro U hUS hext hcent hrad
  let V := U.subgroupOf (S : Subgroup G)
  let e : V ≃* U := subgroupOfEquivOfLe hUS
  have hcent' : centralizer (V : Set S) ≤ V := by
    have hh := (centralizer_subgroupOf_map_le_iff U (S : Subgroup G) hUS
      (MulEquiv.refl S)).mpr hcent
    simpa only [show (MulEquiv.refl S).toMonoidHom = MonoidHom.id S from rfl, map_id] using hh
  have hrad' : V.normalizerMonoidHom.range ⊓ pCore 2 (MulAut V) ≤
      (MulAut.conj : V →* MulAut V).range :=
    (intrinsic_radical_subgroupOf_iff U (S : Subgroup G) hUS 2).mpr hrad
  obtain ⟨hWV, hshape⟩ := MacWilliamsSylow.HallJankoRadicalCandidates.candidates
    hmodel W hunique V hcent' hrad'
  have hWU : W.map (S : Subgroup G).subtype ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hWV hx
  have hmem (x : U) : (x : G) ∈ W.map (S : Subgroup G).subtype ↔ (e.symm x : S) ∈ W := by
    constructor
    · rintro ⟨y, hy, he⟩
      have he' : y = (e.symm x : S) := Subtype.ext he
      exact he' ▸ hy
    · intro hx
      exact ⟨(e.symm x : S), hx, rfl⟩
  have hpreserve (hn : normalizer (U : Set G) ≤ normalizer (W.map (S : Subgroup G).subtype : Set G)) :
      ∀ g : G, g ∈ normalizer (U : Set G) → ∀ x : S, (x : G) ∈ U → x ∈ W →
        g⁻¹ * (x : G) * g ∈ W.map (S : Subgroup G).subtype := by
    intro g hg x _ hx
    have hh := (mem_normalizer_iff_map_conj_eq.mp (hn (inv_mem hg)))
    have hm := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom
      (mem_map_of_mem (S : Subgroup G).subtype hx)
    have hm' := hh.le hm
    change g⁻¹ * (x : G) * (g⁻¹)⁻¹ ∈ W.map (S : Subgroup G).subtype at hm'
    simpa only [inv_inv] using hm'
  rcases hshape with hchar | hcenter | ⟨hUelem, hUcard, hRelem, hRcard, hfixed⟩
  · have : ((W.map (S : Subgroup G).subtype).subgroupOf U).Characteristic := by
      apply characteristic_iff_le_comap.mpr
      intro a x hx
      have hx' : e.symm x ∈ W.subgroupOf V := (hmem x).mp hx
      have ha := characteristic_iff_le_comap.mp hchar (MulAut.congr e.symm a) hx'
      apply (hmem (a x)).mpr
      exact ha
    exact hpreserve (normalizer_le_four_normalizer_of_characteristic S W U hWU)
  · have hScard : Nat.card (center S) = 2 := by
      obtain ⟨m⟩ := hmodel
      have hm := center_map_equiv m
      have hc := card_map_of_injective (K := center S) (f := m.toMonoidHom) m.injective
      rw [hm, MacWilliamsSylow.hallJankoSylow_center_card] at hc
      exact hc.symm
    have hline : (omega₁ (center S) (p := 2)).map (center S).subtype = center S := by
      apply eq_of_le_of_card_ge (map_subtype_le _)
      rw [card_map_of_injective (center S).subtype_injective, hScard, hZ]
    have hScenter : (center S).map (S : Subgroup G).subtype =
        NormalFourCentralOmegaTwo.centralOmega S := by
      change _ = ((omega₁ (center S) (p := 2)).map (center S).subtype).map _
      rw [hline]
    have heq : (center U).map U.subtype =
        ((center V).map V.subtype).map (S : Subgroup G).subtype := by
      rw [← center_map_equiv e, map_map, map_map]
      rfl
    have hcenterU : (center U).map U.subtype = NormalFourCentralOmegaTwo.centralOmega S := by
      rw [heq, hcenter, hScenter]
    exact hpreserve (normalizer_le_four_normalizer_of_center_eq S W U hUS hWU hcenterU)
  · have : IsElementaryAbelian 2 V := hUelem
    have : IsElementaryAbelian 2 V.normalizerMonoidHom.range := hRelem
    exact elementary_normalizer_control hN S W hW U hUS hext hWV hUcard hRcard hfixed

/-- Compatibility wrapper retaining the original trivial-automizer interface. -/
public theorem false_of_trivial_sylow_automizer [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (hmodel : Nonempty (S ≃* MacWilliamsSylow.HallJankoSylow))
    (_hnorm : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G))
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 → IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (_hWB : W ≤ B) : False :=
  false_of_marked_hallJanko hns hN S hmodel hZ hno W hW hunique hfused B hB

end Stellmacher.Recognition.HallJankoTrivialSylowAutomizer
