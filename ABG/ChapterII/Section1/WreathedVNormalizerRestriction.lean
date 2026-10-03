module
public import ABG.ChapterII.Section1.WreathedQuaternionCoreCharacteristic
public import ABG.ChapterII.Section1.FusionPatterns
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Theory.GroupTheory.CyclicSylowCenterNormalizer

/-!
# Normalizer action on the wreathed quaternion factor

The normalizer of the canonical central product V = Q Z(S) normalizes
its quaternion factor Q and fixes Z(S) pointwise. Its outer action has
order dividing six; when that order is six, every automorphism of Q is
realized by an element of N(V). These are the local action facts used in
Alperin--Brauer--Gorenstein, Chapter II Section 1 Proposition 2, article
p. 12 (`page-013.tex`), for involution fusion and focal generation.
All subgroups are actual images under the specified Sylow inclusion.

Characteristicity of Q in V gives the restriction action. The cyclic
center has centralizing normalizer since its automizer order is both a
power of two and a divisor of the odd Sylow index. The inverse image of
Inner(Q) under restriction is exactly V C(V): an element acting trivially
on Q and on Z(S) acts trivially on their join. Every inner automorphism
of Q occurs in the restriction image. Thus its relative index over
Inner(Q) is the outer automizer index of V, and divides the index six
of Inner(Q) in Aut(Q). If it equals six, index multiplicativity makes
the restriction image all of Aut(Q), giving actual normalizer witnesses.
-/

namespace ABG.Wreathed

private theorem map_characteristic_normalizer {H G : Type*} [Group H] [Group G]
    (V Q : Subgroup H) (hQV : Q ≤ V) [(Q.subgroupOf V).Characteristic]
    (f : H →* G) (hf : Function.Injective f) :
    Subgroup.normalizer (V.map f : Set G) ≤ Subgroup.normalizer (Q.map f : Set G) := by
  let e := V.equivMapOfInjective f hf
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨q, hq, rfl⟩ := hx
  let a := (MulAut.congr e.symm) ((V.map f).normalizerMonoidHom ⟨g, hg⟩)
  let qV : V := ⟨q, hQV hq⟩
  have haq : a qV ∈ Q.subgroupOf V :=
    Subgroup.characteristic_iff_le_comap.mp
      (inferInstance : (Q.subgroupOf V).Characteristic) a (show qV ∈ Q.subgroupOf V from hq)
  refine ⟨(a qV : H), haq, ?_⟩
  have he : e (a qV) = (V.map f).normalizerMonoidHom ⟨g, hg⟩ (e qV) := by
    change e (e.symm _) = _
    exact e.apply_symm_apply _
  exact congrArg Subtype.val he

private theorem restriction_indices {G : Type*} [Group G]
    (V Q C : Subgroup G) (hV : V = Q ⊔ C)
    (hC : C ≤ Subgroup.centralizer (V : Set G))
    (hNQ : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (Q : Set G))
    (hNC : Subgroup.normalizer (V : Set G) ≤ Subgroup.centralizer (C : Set G)) :
    let f := Q.normalizerMonoidHom.comp (Subgroup.inclusion hNQ)
    (MulAut.conj : Q →* MulAut Q).range.relIndex f.range = outerAutomizerIndex V ∧
      (MulAut.conj : Q →* MulAut Q).range ≤ f.range := by
  let N := Subgroup.normalizer (V : Set G)
  let f : N →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hNQ)
  have hQV : Q ≤ V := hV ▸ le_sup_left
  have hCV : C ≤ V := hV ▸ le_sup_right
  have hCQ : C ≤ Subgroup.centralizer (Q : Set G) :=
    hC.trans (Subgroup.centralizer_le hQV)
  have hQC : Q ≤ Subgroup.centralizer (C : Set G) := by
    intro q hq c hc
    exact (hCQ hc q hq).symm
  have hDC : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.centralizer_le hQV
  have hpre : (MulAut.conj : Q →* MulAut Q).range.comap f =
      (V ⊔ Subgroup.centralizer (V : Set G)).subgroupOf N := by
    ext g
    change (f g ∈ (MulAut.conj : Q →* MulAut Q).range) ↔ _
    have hbase : f g ∈ (MulAut.conj : Q →* MulAut Q).range ↔
        (g : G) ∈ Q ⊔ Subgroup.centralizer (Q : Set G) := by
      change (⟨g.val, hNQ g.property⟩ : Subgroup.normalizer (Q : Set G)) ∈
        (MulAut.conj : Q →* MulAut Q).range.comap Q.normalizerMonoidHom ↔ _
      rw [Subgroup.normalizerMonoidHom_comap_conj_range]
      rfl
    rw [hbase]
    constructor
    · intro hg
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Q
        (Subgroup.centralizer (Q : Set G)) (Subgroup.centralizer_le_normalizer _)] at hg
      obtain ⟨q, hq, c, hc, hqc⟩ := hg
      have hcC : c ∈ Subgroup.centralizer (C : Set G) := by
        have h := (Subgroup.centralizer (C : Set G)).mul_mem
          ((Subgroup.centralizer (C : Set G)).inv_mem (hQC hq)) (hNC g.property)
        rwa [← hqc, inv_mul_cancel_left] at h
      have hcV : c ∈ Subgroup.centralizer (V : Set G) := by
        have hle : V ≤ Subgroup.centralizer ({c} : Set G) := by
          rw [hV]
          exact sup_le (fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (hc q hq))
            (fun d hd => Subgroup.mem_centralizer_singleton_iff.mpr (hcC d hd))
        exact fun v hv => Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
      change (g : G) ∈ V ⊔ Subgroup.centralizer (V : Set G)
      rw [← hqc]
      exact (V ⊔ Subgroup.centralizer (V : Set G)).mul_mem
        ((show V ≤ V ⊔ Subgroup.centralizer (V : Set G) from le_sup_left) (hQV hq))
        ((show Subgroup.centralizer (V : Set G) ≤ V ⊔ Subgroup.centralizer (V : Set G)
          from le_sup_right) hcV)
    · intro hg
      change (g : G) ∈ V ⊔ Subgroup.centralizer (V : Set G) at hg
      apply (show V ⊔ Subgroup.centralizer (V : Set G) ≤
          Q ⊔ Subgroup.centralizer (Q : Set G) from ?_) hg
      apply sup_le ?_ (hDC.trans le_sup_right)
      rw [hV]
      exact sup_le le_sup_left (hCQ.trans le_sup_right)
  change (MulAut.conj : Q →* MulAut Q).range.relIndex f.range = outerAutomizerIndex V ∧ _
  constructor
  · change _ = ((V ⊔ Subgroup.centralizer (V : Set G)).subgroupOf N).index
    rw [← hpre, Subgroup.index_comap]
  · exact (by
    rintro a ⟨q, rfl⟩
    refine ⟨⟨q.val, V.le_normalizer (hQV q.property)⟩, ?_⟩
    ext t
    rfl)

/-- The normalizer preserves the quaternion factor and fixes the center pointwise. -/
public theorem canonical_v_normalizer_structure {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {n : ℕ} (P : Presentation S n) :
    let V := P.V.map (S : Subgroup G).subtype
    let Q := P.quaternionCore.map (S : Subgroup G).subtype
    let C := (Subgroup.center S).map (S : Subgroup G).subtype
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (Q : Set G) ∧
    Subgroup.normalizer (V : Set G) ≤ Subgroup.centralizer (C : Set G) ∧
    C ≤ Subgroup.centralizer (V : Set G) := by
  let i := (S : Subgroup G).subtype
  let V := P.V.map i
  let Q := P.quaternionCore.map i
  let C := (Subgroup.center S).map i
  have hQV : P.quaternionCore ≤ P.V := le_sup_left
  have hCV : Subgroup.center S ≤ P.V := le_sup_right
  have hCP : C ≤ S := Subgroup.map_subtype_le _
  have hPC : (S : Subgroup G) ≤ Subgroup.centralizer (C : Set G) := by
    intro s hs c hc
    obtain ⟨c, hc, rfl⟩ := hc
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc (⟨s, hs⟩ : S)).symm
  let := P.center_cyclic
  let : IsCyclic C := isCyclic_of_surjective
    ((Subgroup.center S).equivMapOfInjective i (S : Subgroup G).subtype_injective).toMonoidHom
    ((Subgroup.center S).equivMapOfInjective i (S : Subgroup G).subtype_injective).surjective
  have hNC : Subgroup.normalizer (C : Set G) ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.normalizer_le_centralizer_of_cyclic_sylow_center S C hCP hPC
  have hCchar : ((Subgroup.center S).subgroupOf P.V).Characteristic := by
    have he : (Subgroup.center S).subgroupOf P.V = Subgroup.center P.V := by
      apply Subgroup.map_injective P.V.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hCV, P.V_center]
    rw [he]
    infer_instance
  let := hCchar
  let := P.quaternionCore_characteristic_in_V
  have hVNC : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    map_characteristic_normalizer P.V (Subgroup.center S) hCV i (S : Subgroup G).subtype_injective
  have hVNQ : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    map_characteristic_normalizer P.V P.quaternionCore hQV i (S : Subgroup G).subtype_injective
  exact ⟨hVNQ, hVNC.trans hNC,
    Subgroup.le_centralizer_iff.mp ((Subgroup.map_subtype_le P.V).trans hPC)⟩

/-- Restriction to the quaternion factor bounds the canonical outer index by six. -/
public theorem canonical_v_outer_index_dvd_six {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {n : ℕ} (P : Presentation S n) :
    outerAutomizerIndex (P.V.map (S : Subgroup G).subtype) ∣ 6 := by
  obtain ⟨hNQ, hNC, hC⟩ := canonical_v_normalizer_structure S P
  obtain ⟨hrel, hinner⟩ := restriction_indices (P.V.map (S : Subgroup G).subtype)
    _ _ (Subgroup.map_sup _ _ _) hC hNQ hNC
  obtain ⟨eQ⟩ := P.quaternion_core_model.1
  let e := (P.quaternionCore.equivMapOfInjective (S : Subgroup G).subtype
    (S : Subgroup G).subtype_injective).symm.trans eQ
  rw [← hrel, ← QuaternionGroup.index_range_conj_of_equiv e]
  exact Subgroup.relIndex_dvd_index_of_le hinner

/-- With outer index six, every quaternion-factor automorphism is realized by the normalizer. -/
public theorem canonical_v_restriction_surjective {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {n : ℕ} (P : Presentation S n)
    (hindex : outerAutomizerIndex (P.V.map (S : Subgroup G).subtype) = 6)
    (a : MulAut (P.quaternionCore.map (S : Subgroup G).subtype)) :
    ∃ g : G, g ∈ Subgroup.normalizer (P.V.map (S : Subgroup G).subtype : Set G) ∧
      ∀ q : P.quaternionCore.map (S : Subgroup G).subtype,
        g * (q : G) * g⁻¹ = (a q : G) := by
  let V := P.V.map (S : Subgroup G).subtype
  let Q := P.quaternionCore.map (S : Subgroup G).subtype
  obtain ⟨hNQ, hNC, hC⟩ := canonical_v_normalizer_structure S P
  let f := Q.normalizerMonoidHom.comp (Subgroup.inclusion hNQ)
  obtain ⟨hrel, hinner⟩ := restriction_indices V _ _ (Subgroup.map_sup _ _ _) hC hNQ hNC
  obtain ⟨eQ⟩ := P.quaternion_core_model.1
  let e := (P.quaternionCore.equivMapOfInjective (S : Subgroup G).subtype
    (S : Subgroup G).subtype_injective).symm.trans eQ
  have hmul := Subgroup.relIndex_mul_index hinner
  rw [hrel, hindex, QuaternionGroup.index_range_conj_of_equiv e] at hmul
  change 6 * f.range.index = 6 at hmul
  have hi : f.range.index = 1 := by omega
  have ha : a ∈ f.range := (Subgroup.index_eq_one.mp hi) ▸ Subgroup.mem_top a
  obtain ⟨g, hg⟩ := ha
  refine ⟨g, g.property, ?_⟩
  intro q
  exact congrArg Subtype.val (DFunLike.congr_fun hg q)

end ABG.Wreathed
