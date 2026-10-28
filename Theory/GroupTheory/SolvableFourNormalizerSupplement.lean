module

public import Theory.GroupTheory.CharacteristicTwoCoreFour
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# A four-containing normalizer supplement to the odd core

In a finite solvable group whose chosen Sylow two-subgroup contains an
elementary eight, some subgroup of that Sylow subgroup contains an elementary
four and has normalizer supplementing the odd core.

Quotient by the odd core. The quotient map is injective on the Sylow subgroup,
so the elementary eight survives. The quotient two-core contains a four by
`exists_elementary_four_le_pCore_of_solvable_oddCore_eq_bot`. Pull the two-core
back inside the chosen Sylow subgroup, and lift its four along the same
injection. Normalizer lifting through the odd kernel supplies the supplement.
The refined statement retains the image as exactly the quotient two-core,
and the quotient four-group existence is also available on its own.

This is the quotient step in solvable two-generated-core arguments; compare
GLS, Number 2, Section 22, and Kurzweil–Stellmacher, 8.3.4.
-/

open Subgroup

/-- The Sylow lift of the two-core of the odd quotient contains a four-group,
and its normalizer supplements the odd core. -/
public theorem exists_core_four_containing_normalizer_supplement_of_solvable
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow 2 G) (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hEP : E ≤ P) (hE : 8 ≤ Nat.card E) :
    ∃ Q : Subgroup G, Q ≤ P ∧
      (∃ V : Subgroup G, V ≤ Q ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4) ∧
      Q.map (QuotientGroup.mk' (pPrimeCore 2 G)) =
        pCore 2 (G ⧸ pPrimeCore 2 G) ∧
      normalizer (Q : Set G) ⊔ pPrimeCore 2 G = ⊤ := by
  let M := pPrimeCore 2 G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let f : P →* G ⧸ M := q.comp (P : Subgroup G).subtype
  have hdisj : Disjoint (P : Subgroup G) M := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := G)).pow_left n
  have hfinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hxM : (x : G) ∈ M := (QuotientGroup.eq_one_iff _).mp hx
    exact mem_bot.mp ((disjoint_iff.mp hdisj).le ⟨x.property, hxM⟩)
  let Pbar : Sylow 2 (G ⧸ M) := P.mapSurjective (QuotientGroup.mk'_surjective M)
  have hPrange : f.range = (Pbar : Subgroup (G ⧸ M)) := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  let EP := E.subgroupOf P
  let : IsElementaryAbelian 2 EP := IsElementaryAbelian.subgroupOf hEP
  let Ebar := EP.map f
  let : IsElementaryAbelian 2 Ebar := IsElementaryAbelian.map f
  have hEbarP : Ebar ≤ Pbar := by
    rw [← hPrange]
    exact map_le_range f EP
  have hEbar : 8 ≤ Nat.card Ebar := by
    rw [card_map_of_injective hfinj,
      Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv]
    exact hE
  obtain ⟨Vbar, hVR, hVe, hVcard⟩ :=
    exists_elementary_four_le_pCore_of_solvable_oddCore_eq_bot
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2) Pbar Ebar hEbarP hEbar
  let : IsElementaryAbelian 2 Vbar := hVe
  let R := pCore 2 (G ⧸ M)
  have hRrange : R ≤ f.range := by
    rw [hPrange]
    exact pCore_isPGroup.le_sylow_of_normal Pbar
  let QP := R.comap f
  let Q := QP.map (P : Subgroup G).subtype
  have hQP : Q ≤ P := map_subtype_le QP
  have hQmap : Q.map q = R := by
    rw [map_map]
    exact map_comap_eq_self hRrange
  let VP := Vbar.comap f
  let e : VP ≃* Vbar := MulEquiv.ofBijective (f.subgroupComap Vbar) (by
    constructor
    · intro x y h
      apply Subtype.ext
      exact hfinj (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, hx⟩ := hRrange (hVR y.property)
      exact ⟨⟨x, by change f x ∈ Vbar; rw [hx]; exact y.property⟩,
        Subtype.ext hx⟩)
  let : IsElementaryAbelian 2 VP := {
    toIsMulCommutative := Vbar.comap_injective_isMulCommutative hfinj
    exponent_dvd_p := by
      rw [Monoid.exponent_eq_of_mulEquiv e]
      exact IsElementaryAbelian.exponent_dvd_p 2 Vbar }
  let V := VP.map (P : Subgroup G).subtype
  have hVQ : V ≤ Q := map_mono (comap_mono hVR)
  have hVfour : Nat.card V = 4 := by
    rw [card_map_of_injective (P : Subgroup G).subtype_injective,
      Nat.card_congr e.toEquiv]
    exact hVcard
  refine ⟨Q, hQP, ⟨V, hVQ, IsElementaryAbelian.map_subtype, hVfour⟩, hQmap, ?_⟩
  let : Fact (IsPGroup 2 Q) := ⟨P.isPGroup'.to_le hQP⟩
  have hnormalizer : (normalizer (Q : Set G)).map q = ⊤ := by
    rw [← normalizer_map_quotient_eq_map_normalizer 2 Q M inferInstance
      (pPrimeCore_coprime_card (p := 2) (G := G)), hQmap]
    exact normalizer_eq_top R
  have h := congrArg (Subgroup.comap q) hnormalizer
  simpa only [q, QuotientGroup.comap_map_mk', comap_top, sup_comm] using h

/-- A Sylow two-subgroup of elementary rank at least three contains a subgroup
with a four-group whose normalizer supplements the odd core. -/
public theorem exists_four_containing_normalizer_supplement_of_solvable
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow 2 G) (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hEP : E ≤ P) (hE : 8 ≤ Nat.card E) :
    ∃ Q : Subgroup G, Q ≤ P ∧
      (∃ V : Subgroup G, V ≤ Q ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4) ∧
      normalizer (Q : Set G) ⊔ pPrimeCore 2 G = ⊤ := by
  obtain ⟨Q, hQP, hfour, -, hsupp⟩ :=
    exists_core_four_containing_normalizer_supplement_of_solvable P E hEP hE
  exact ⟨Q, hQP, hfour, hsupp⟩

/-- An elementary eight in a finite solvable group forces an elementary four
in the two-core of its odd-core quotient. -/
public theorem exists_elementary_four_le_pCore_odd_quotient_of_solvable
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E) :
    ∃ V : Subgroup (G ⧸ pPrimeCore 2 G),
      V ≤ pCore 2 (G ⧸ pPrimeCore 2 G) ∧
      IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  let N := pPrimeCore 2 G
  let q := QuotientGroup.mk' N
  let f := q.comp E.subtype
  have hf : Function.Injective f :=
    injective_comp_subtype_of_coprime_ker q
      (by simpa only [q, QuotientGroup.ker_mk'] using
        (pPrimeCore_coprime_card (p := 2) (G := G))) E
      (IsElementaryAbelian.isPGroup 2 E)
  let B := (⊤ : Subgroup E).map f
  let : IsElementaryAbelian 2 (⊤ : Subgroup E) := {
    exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom (⊤ : Subgroup E).subtype
      (⊤ : Subgroup E).subtype_injective).trans
        (IsElementaryAbelian.exponent_dvd_p 2 E) }
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hB : 8 ≤ Nat.card B := by
    rw [card_map_of_injective hf, Nat.card_congr Subgroup.topEquiv.toEquiv]
    exact hE
  obtain ⟨P, hBP⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  exact exists_elementary_four_le_pCore_of_solvable_oddCore_eq_bot
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2) P B hBP hB
