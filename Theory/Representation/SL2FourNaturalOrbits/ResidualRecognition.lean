module

public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.SpecificGroups.AlternatingFiveBorelProjection
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow

/-!
# Sylow-normalized residual recognition in the marked SL₂(4)

A nontrivial proper two-perfect subgroup normalized by a full Sylow
four-group is exactly the normalizer of that Sylow subgroup. Its join with
the Sylow subgroup remains proper by simplicity. After an inner five-line
marking, the proper-overgroup theorem places the join in the standard A₄;
the existing two-perfect Borel recognition then gives equality.

The conclusions preserve the actual Sylow inclusion, give cardinal twelve,
and construct an A₄ equivalence. An invariant binary plane of cardinal four
supplies properness directly from natural-module transitivity. This is the
finite residual marking used in the natural SL₂(4) branch of
Aschbacher–Smith 13.7.13, printed pp.942–943.
-/

@[expose] public section
open Subgroup
namespace Representation.SL2FourNatural

private theorem residual_join_ne_top (P : Sylow 2 SL) (J : Subgroup SL)
    (hne : J ≠ ⊥) (hn : (P : Subgroup SL) ≤ normalizer (J : Set SL))
    (hproper : J ≠ ⊤) : J ⊔ (P : Subgroup SL) ≠ ⊤ := by
  intro he
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup SL := alternatingFiveEquiv.isSimpleGroup
  have ht : (⊤ : Subgroup SL) ≤ normalizer (J : Set SL) :=
    he ▸ sup_le J.le_normalizer hn
  let : J.Normal := normalizer_eq_top_iff.mp (top_unique ht)
  exact hproper ((inferInstance : J.Normal).eq_bot_or_eq_top.resolve_left hne)

/-- The residual and its full Sylow subgroup admit a common inner five-line marking. -/
theorem residual_marking (P : Sylow 2 SL) (J : Subgroup SL)
    (hp : IsPPerfect 2 J) (hne : J ≠ ⊥)
    (hn : (P : Subgroup SL) ≤ normalizer (J : Set SL)) (hproper : J ≠ ⊤) :
    ∃ e : SL ≃* alternatingGroup (Fin 5),
      (P : Subgroup SL).map e.toMonoidHom = AlternatingFiveProjection.P ∧
      J.map e.toMonoidHom = BinaryPermutation.AlternatingFiveBorel.B := by
  let q := alternatingFiveEquiv
  let Q := P.mapSurjective (f := q.toMonoidHom) q.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) Q AlternatingFiveProjection.sylow
  let e : SL ≃* alternatingGroup (Fin 5) := q.trans (MulAut.conj g)
  have hP : (P : Subgroup SL).map e.toMonoidHom = AlternatingFiveProjection.P := by
    change (P : Subgroup SL).map ((MulAut.conj g).toMonoidHom.comp q.toMonoidHom) = _
    rw [← map_map]
    change (g • Q).toSubgroup = AlternatingFiveProjection.P
    rw [hg]
    rfl
  let D := J.map e.toMonoidHom
  let I := (J ⊔ (P : Subgroup SL)).map e.toMonoidHom
  have hI : I ≠ ⊤ := by
    intro he
    have ht : (J ⊔ (P : Subgroup SL)).map e.toMonoidHom = (⊤ : Subgroup SL).map e.toMonoidHom := by
      simpa only [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using he
    exact residual_join_ne_top P J hne hn hproper ((Subgroup.map_injective e.injective) ht)
  have hPI : AlternatingFiveProjection.P ≤ I := hP ▸ map_mono le_sup_right
  have hIB : I ≤ BinaryPermutation.AlternatingFiveBorel.B := by
    exact (alternatingGroup.proper_sylow_overgroup_le_normalizer
      AlternatingFiveProjection.sylow I hI hPI).trans_eq AlternatingFiveProjection.normalizer_P
  have hDB : D ≤ BinaryPermutation.AlternatingFiveBorel.B := (map_mono le_sup_left).trans hIB
  have hD : D ≠ ⊥ := by
    intro he
    have ht : J.map e.toMonoidHom = (⊥ : Subgroup SL).map e.toMonoidHom := by
      simpa only [Subgroup.map_bot] using he
    exact hne ((map_injective e.injective) ht)
  have hD5 : ∀ d ∈ D, d ^ 5 = 1 → d = 1 := by
    have hc : Nat.card BinaryPermutation.AlternatingFiveBorel.B = 12 :=
      (Nat.card_congr BinaryPermutation.AlternatingFiveBorel.marking.toEquiv.symm).trans
        (alternatingGroup.card_of_card_eq_four (by simp))
    have hd : Nat.card D ∣ 12 := hc ▸ card_dvd_of_le hDB
    have hcop : Nat.Coprime (Nat.card D) 5 := Nat.Coprime.of_dvd_left hd (by decide)
    intro d hd he
    have ht : (⟨d, hd⟩ : D) = 1 := (powCoprime hcop).injective (by
      change (⟨d, hd⟩ : D) ^ 5 = 1 ^ 5
      simpa only [one_pow] using (Subtype.ext he : (⟨d, hd⟩ : D) ^ 5 = 1))
    exact congrArg Subtype.val ht
  have hPD : AlternatingFiveProjection.P ≤ normalizer (D : Set _) := by
    rw [← hP, ← map_equiv_normalizer_eq]
    exact map_mono hn
  exact ⟨e, hP, AlternatingFiveProjection.eq_borel D hD
    (hp.of_surjective (e.toMonoidHom.subgroupMap J) (e.toMonoidHom.subgroupMap_surjective J)) hD5 hPD⟩

/-- The nontrivial proper two-perfect residual is the literal Sylow normalizer. -/
theorem residual_eq_sylow_normalizer (P : Sylow 2 SL) (J : Subgroup SL)
    (hp : IsPPerfect 2 J) (hne : J ≠ ⊥)
    (hn : (P : Subgroup SL) ≤ normalizer (J : Set SL)) (hproper : J ≠ ⊤) :
    J = normalizer (P : Set SL) := by
  obtain ⟨e, hP, hJ⟩ := residual_marking P J hp hne hn hproper
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  change J.map e.toMonoidHom = (normalizer ((P : Subgroup SL) : Set SL)).map e.toMonoidHom
  rw [map_equiv_normalizer_eq (P : Subgroup SL) e, hP, AlternatingFiveProjection.normalizer_P]
  exact hJ

/-- The marked residual has cardinal twelve. -/
theorem residual_card_twelve (P : Sylow 2 SL) (J : Subgroup SL)
    (hp : IsPPerfect 2 J) (hne : J ≠ ⊥)
    (hn : (P : Subgroup SL) ≤ normalizer (J : Set SL)) (hproper : J ≠ ⊤) :
    Nat.card J = 12 := by
  obtain ⟨e, hP, hJ⟩ := residual_marking P J hp hne hn hproper
  have he := Nat.card_congr (J.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  rw [hJ] at he
  exact he.trans ((Nat.card_congr BinaryPermutation.AlternatingFiveBorel.marking.toEquiv.symm).trans
    (alternatingGroup.card_of_card_eq_four (by simp)))

/-- The marked residual is isomorphic to the alternating group on four points. -/
theorem residual_alternatingFour (P : Sylow 2 SL) (J : Subgroup SL)
    (hp : IsPPerfect 2 J) (hne : J ≠ ⊥)
    (hn : (P : Subgroup SL) ≤ normalizer (J : Set SL)) (hproper : J ≠ ⊤) :
    Nonempty (J ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨e, hP, hJ⟩ := residual_marking P J hp hne hn hproper
  exact ⟨(J.equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr hJ).trans BinaryPermutation.AlternatingFiveBorel.marking.symm)⟩

/-- A subgroup preserving an actual binary plane is proper in the natural SL₂(4). -/
theorem subgroup_ne_top_of_invariant_plane (J : Subgroup SL)
    (W : Submodule (ZMod 2) V) (hW : Nat.card W = 4)
    (hstable : ∀ g ∈ J, ∀ v ∈ W, action g v ∈ W) : J ≠ ⊤ := by
  have hn : W ≠ ⊥ := by
    intro he
    have hc : Nat.card W = 1 := he ▸ Nat.card_unique
    omega
  obtain ⟨u, hu, hune⟩ := W.ne_bot_iff.mp hn
  intro he
  have ht : W = ⊤ := by
    apply top_unique
    intro v hv
    by_cases hv0 : v = 0
    · exact hv0 ▸ W.zero_mem
    obtain ⟨g, hg⟩ := transitive_nonzero u v hune hv0
    exact hg ▸ hstable g (he ▸ Subgroup.mem_top g) u hu
  have hc : Nat.card W = 16 := by
    rw [ht, Nat.card_congr (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) V) ≃ₗ[ZMod 2] V).toEquiv,
      Nat.card_eq_fintype_card, card_vector]
  omega

/-- An invariant natural plane gives the complete marked A₄ recognition packet. -/
theorem residual_recognition_of_invariant_plane (P : Sylow 2 SL) (J : Subgroup SL)
    (hp : IsPPerfect 2 J) (hne : J ≠ ⊥)
    (hn : (P : Subgroup SL) ≤ normalizer (J : Set SL))
    (W : Submodule (ZMod 2) V) (hW : Nat.card W = 4)
    (hstable : ∀ g ∈ J, ∀ v ∈ W, action g v ∈ W) :
    J = normalizer (P : Set SL) ∧ Nat.card J = 12 ∧
      Nonempty (J ≃* alternatingGroup (Fin 4)) := by
  have ht := subgroup_ne_top_of_invariant_plane J W hW hstable
  exact ⟨residual_eq_sylow_normalizer P J hp hne hn ht,
    residual_card_twelve P J hp hne hn ht, residual_alternatingFour P J hp hne hn ht⟩

end Representation.SL2FourNatural
