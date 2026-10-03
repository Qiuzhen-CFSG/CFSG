module

public import Theory.GroupTheory.SylowCentralizerConjugacy
public import Theory.GroupTheory.PGroup.NormalExtraspecialDerivedCenter

/-!
# Nonfusion from characteristic Sylow-centralizer lines

Let `z` be central in a Sylow two-subgroup `S`, and let `X` be stable under
conjugation by `C_G(z)` whenever the image returns to `S`. If each relevant
`C_S(t)` is proper and the normalizer of its ambient image fixes `z`, then
no element of `X` is conjugate to `z`.

Choose a conjugate of `z` in `X` with maximal Sylow-centralizer order.
Its centralizer contains an ambient Sylow subgroup `T` containing `C_S(t)`.
The normalizer condition in `T` gives a strictly larger two-group, which
normalizer control places in `C_G(z)`. Conjugating it into `S` within
`C_G(z)` produces a member of `X` with a larger centralizer, a contradiction.
In particular, the common ambient centralizer need not be a two-group.

The intrinsic derived-center identity supplies normalizer control after
transport through the actual ambient image of `C_S(t)`.

Source: the characteristic-centralizer argument in Janko–Thompson,
Math. Z. 113 (1970), §4, Case 1, printed p.392. The local centralizer
calculation is an explicit input, independent of the recognition problem.
-/

open Subgroup

private theorem exists_centralizing_sylow
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (z : S) (hz : z ∈ center S) (t : G) (hconj : IsConj (z : G) t)
    (U : Subgroup G) (hUp : IsPGroup 2 U) (hUC : U ≤ centralizer ({t} : Set G)) :
    ∃ T : Sylow 2 G, U ≤ T ∧ (T : Subgroup G) ≤ centralizer ({t} : Set G) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let a := MulAut.conj g
  let R := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let C := centralizer ({t} : Set G)
  have hRC : (R : Subgroup G) ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hcomm : (z : G) * s = s * z :=
      (congrArg Subtype.val (mem_center_iff.mp hz (⟨s, hs⟩ : S))).symm
    change a s * t = t * a s
    have ha : a (z : G) = t := hg
    rw [← ha, ← map_mul, ← map_mul, hcomm]
  obtain ⟨Q, hUQ⟩ := (hUp.comap_subtype (K := C)).exists_le_sylow
  let I := (Q : Subgroup C).map C.subtype
  have hUI : U ≤ I := by
    intro u hu
    exact ⟨⟨u, hUC hu⟩, hUQ hu, rfl⟩
  have hIcard : Nat.card I = Nat.card R := by
    rw [card_map_of_injective C.subtype_injective,
      Nat.card_congr (Q.equiv (R.subtype hRC)).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv
  obtain ⟨T, hIT⟩ := (Q.isPGroup'.map C.subtype).exists_le_sylow
  have hITeq : I = (T : Subgroup G) := eq_of_le_of_card_ge hIT (by
    rw [hIcard, Nat.card_congr (R.equiv T).toEquiv])
  exact ⟨T, hITeq ▸ hUI, hITeq ▸ map_subtype_le (Q : Subgroup C)⟩

private theorem exists_conj_map_le (p : ℕ) {G : Type*} [Group G] [Finite G]
    [Fact p.Prime] (S : Sylow p G) {R : Subgroup G} (hR : IsPGroup p R) :
    ∃ a : G, R.map (MulAut.conj a).toMonoidHom ≤ (S : Subgroup G) := by
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨a, ?_⟩
  rw [← ha]
  exact map_mono hRQ

/-- A family stable under conjugation by `C_G(z)` cannot contain an ambient
conjugate of the central Sylow element `z` if its intrinsic centralizers are
proper and their ambient normalizers fix `z`. The two centralizer hypotheses
are needed only for elements conjugate to `z`. No order assumption on `z`
is needed for this normalizer version. -/
public theorem Sylow.not_isConj_of_stable_centralizer_normalizers
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (z : S) (hzC : z ∈ center S)
    (X : Set S)
    (hstable : ∀ t : S, t ∈ X → ∀ g : G, Commute g (z : G) →
      ∀ u : S, (MulAut.conj g) (t : G) = (u : G) → u ∈ X)
    (hproper : ∀ t : S, t ∈ X → IsConj (z : G) (t : G) →
      centralizer ({t} : Set S) ≠ ⊤)
    (hnormalizer : ∀ t : S, t ∈ X → IsConj (z : G) (t : G) →
      normalizer ((centralizer ({t} : Set S)).map (S : Subgroup G).subtype : Set G) ≤
        centralizer ({(z : G)} : Set G)) :
    ∀ t : S, t ∈ X → ¬ IsConj (z : G) (t : G) := by
  classical
  let H : Subgroup G := centralizer ({(z : G)} : Set G)
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (fun q : S => (q : G)) (mem_center_iff.mp hzC ⟨s, hs⟩))
  intro t0 ht0 hconj
  let Y : Set S := {u | u ∈ X ∧ IsConj (z : G) (u : G)}
  obtain ⟨t, ⟨htX, hzt⟩, htmax⟩ := Set.Finite.exists_maximalFor
    (fun u : S => Nat.card (centralizer ({u} : Set S))) Y (Set.toFinite Y)
    ⟨t0, ht0, hconj⟩
  let C : Subgroup S := centralizer ({t} : Set S)
  let K : Subgroup G := C.map (S : Subgroup G).subtype
  have hKS : K ≤ (S : Subgroup G) := map_subtype_le C
  have hKC : K ≤ centralizer ({(t : G)} : Set G) := by
    rw [show K = (S : Subgroup G) ⊓ centralizer ({(t : G)} : Set G) from
      map_subtype_centralizer_singleton (S : Subgroup G) t]
    exact inf_le_right
  have hKp : IsPGroup 2 K := S.isPGroup'.to_le hKS
  obtain ⟨T, hKT, hTC⟩ := exists_centralizing_sylow S z hzC (t : G) hzt K hKp hKC
  have hKproper : K.subgroupOf (T : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    intro hTK
    have hcard : Nat.card S ≤ Nat.card C := by
      calc
        Nat.card S = Nat.card T := Nat.card_congr (S.equiv T).toEquiv
        _ ≤ Nat.card K := card_le_of_le hTK
        _ = Nat.card C := card_map_of_injective (S : Subgroup G).subtype_injective
    apply hproper t htX hzt
    exact eq_of_le_of_card_ge le_top (by simpa only [Nat.card_congr topEquiv.toEquiv] using hcard)
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  let R : Subgroup G := normalizer (K : Set G) ⊓ (T : Subgroup G)
  have hKR : K ≤ R := le_inf le_normalizer hKT
  have hRne : R ≠ K := by
    obtain ⟨v, hvN, hvK⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (K.subgroupOf (T : Subgroup G)) hKproper)
    rw [← subgroupOf_normalizer_eq hKT] at hvN
    intro heq
    exact hvK (heq ▸ (show (v : G) ∈ R from ⟨hvN, v.property⟩))
  have hRH : R ≤ H := inf_le_left.trans (hnormalizer t htX hzt)
  have hRC : R ≤ centralizer ({(t : G)} : Set G) := inf_le_right.trans hTC
  have hRp : IsPGroup 2 R := T.isPGroup'.to_le inf_le_right
  obtain ⟨a, ha⟩ := exists_conj_map_le 2 (S.subtype hSH)
    (hRp.comap_subtype (K := H))
  let f : G ≃* G := MulAut.conj (a : G)
  have hRS : R.map f.toMonoidHom ≤ (S : Subgroup G) := by
    rintro _ ⟨r, hr, rfl⟩
    exact ha (mem_map_of_mem (MulAut.conj a).toMonoidHom
      (show (⟨r, hRH hr⟩ : H) ∈ R.subgroupOf H from hr))
  have htK : (t : G) ∈ K := mem_map_of_mem (S : Subgroup G).subtype
    (mem_centralizer_singleton_iff.mpr rfl)
  let t' : S := ⟨f (t : G), hRS (mem_map_of_mem f.toMonoidHom (hKR htK))⟩
  have ht'X : t' ∈ X := hstable t htX a
    (mem_centralizer_singleton_iff.mp a.property) t' rfl
  have hzt' : IsConj (z : G) (t' : G) :=
    hzt.trans (isConj_iff.mpr ⟨(a : G), rfl⟩)
  let K' : Subgroup G := (centralizer ({t'} : Set S)).map (S : Subgroup G).subtype
  have hRK' : R.map f.toMonoidHom ≤ K' := by
    dsimp only [K']
    rw [map_subtype_centralizer_singleton]
    refine le_inf hRS ?_
    rintro _ ⟨r, hr, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f r * f (t : G) = f (t : G) * f r
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hRC hr))
  have hcard : Nat.card R ≤ Nat.card (centralizer ({t'} : Set S)) := by
    calc
      Nat.card R = Nat.card (R.map f.toMonoidHom) := (card_map_of_injective f.injective).symm
      _ ≤ Nat.card K' := card_le_of_le hRK'
      _ = Nat.card (centralizer ({t'} : Set S)) :=
        card_map_of_injective (S : Subgroup G).subtype_injective
  have hcardKR : Nat.card K ≤ Nat.card R := card_le_of_le hKR
  have hcardKt : Nat.card K = Nat.card (centralizer ({t} : Set S)) :=
    card_map_of_injective (S : Subgroup G).subtype_injective
  have hmax := htmax (show t' ∈ Y from ⟨ht'X, hzt'⟩)
    (by change Nat.card (centralizer ({t} : Set S)) ≤ _
        rw [← hcardKt]; exact hcardKR.trans hcard)
  exact hRne (eq_of_le_of_card_ge hKR (by rw [hcardKt]; exact hcard.trans hmax)).symm

/-- An intrinsic derived-center line in a subgroup of `H` forces the ambient
normalizer of its image to fix the generating involution. This transports the
line along `C ≃* C.map H.subtype` before applying the ambient criterion. -/
public theorem Subgroup.normalizer_map_subtype_le_centralizer_of_derived_center_line {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (C : Subgroup H) (z : H) (hz : orderOf z = 2)
    (hline : (_root_.commutator C ⊓ center C).map C.subtype = zpowers z) :
    normalizer (C.map H.subtype : Set G) ≤ centralizer ({(z : G)} : Set G) := by
  let D := C.map H.subtype
  let e : C ≃* D := C.equivMapOfInjective H.subtype H.subtype_injective
  have hder : (_root_.commutator C).map e.toMonoidHom = _root_.commutator D := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hcen : (center C).map e.toMonoidHom = center D := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      apply mem_center_iff.mpr
      intro d
      obtain ⟨c', rfl⟩ := e.surjective d
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (mem_center_iff.mp hc c')
    · intro d hd
      refine ⟨e.symm d, mem_center_iff.mpr ?_, e.apply_symm_apply d⟩
      intro c
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hd (e c)
  have htrans : (_root_.commutator C ⊓ center C).map e.toMonoidHom =
      _root_.commutator D ⊓ center D := by
    rw [map_inf _ _ _ e.injective, hder, hcen]
  have hcomp : D.subtype.comp e.toMonoidHom = H.subtype.comp C.subtype := by
    ext c
    exact C.coe_equivMapOfInjective_apply H.subtype H.subtype_injective c
  apply normalizer_le_centralizer_of_derived_center_line D (z : G)
    ((orderOf_coe z).trans hz)
  rw [← htrans, map_map, hcomp, ← map_map, hline, MonoidHom.map_zpowers]
  rfl

/-- Derived-center lines in the proper centralizers of a stable family exclude
fusion with a central Sylow involution. The line identity is entirely intrinsic
to `S`; the ambient image and its normalizer are handled by the bridge above. -/
public theorem Sylow.not_isConj_of_stable_derived_center_lines
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (X : Set S)
    (hstable : ∀ t : S, t ∈ X → ∀ g : G, Commute g (z : G) →
      ∀ u : S, (MulAut.conj g) (t : G) = (u : G) → u ∈ X)
    (hproper : ∀ t : S, t ∈ X → IsConj (z : G) (t : G) →
      centralizer ({t} : Set S) ≠ ⊤)
    (hline : ∀ t : S, t ∈ X → IsConj (z : G) (t : G) →
      let C := centralizer ({t} : Set S)
      (_root_.commutator C ⊓ center C).map C.subtype = zpowers z) :
    ∀ t : S, t ∈ X → ¬ IsConj (z : G) (t : G) := by
  apply S.not_isConj_of_stable_centralizer_normalizers z hzC X hstable hproper
  intro t ht hzt
  exact normalizer_map_subtype_le_centralizer_of_derived_center_line
    (S : Subgroup G) (centralizer ({t} : Set S)) z hz (hline t ht hzt)
