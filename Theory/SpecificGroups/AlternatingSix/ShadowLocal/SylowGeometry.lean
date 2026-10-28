module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphSubgroups
public import Theory.Quasithin.Rank

/-!
# Local structure of actual Sylow subgroups of Aut(A₆)

The marked equivalence with the cyclic-eight holomorph transports its inner
and natural subgroups, centers, Frattini and derived subgroups, central
quotient, and normal cyclic-four geometry. The two four-groups remain actual
subgroups of the inner Sylow intersection, with an explicit conjugator and
normalizers of order sixteen.

The same equivalence transports the rank-one subgroup classification without
assuming normality, and the automorphism-prime restriction for normal
subgroups. The latter uses the proved direct bound, avoiding the false
unrestricted derived-subgroup dichotomy in the printed proof of 2.5.22.
All groups and quotient maps in the conclusions belong to the actual
`MulAut (alternatingGroup (Fin 6))`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.567–570, especially 2.5.22 and 2.5.27.
-/

public section

open Subgroup
namespace AlternatingSix.ShadowLocal.SylowGeometry
open Identification

private theorem map_center {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp only [mem_map_equiv, MulEquiv.symm_apply_apply, mem_center_iff]
  constructor
  · intro hx y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (hx y)
  · intro hx y
    apply e.injective
    simpa only [map_mul] using hx (e y)

private theorem map_centralizer {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (U : Subgroup G) :
    (centralizer (U : Set G)).map e.toMonoidHom =
      centralizer (U.map e.toMonoidHom : Set H) := by
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp only [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hx y hy
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (hx y (by simpa using hy))
  · intro hx y hy
    apply e.injective
    simpa only [map_mul] using hx (e y) (by simpa using hy)

/-- The marked cyclic four-subgroup of the actual inner Sylow intersection. -/
@[expose] noncomputable def cyclicFour (P : Sylow 2 AutA6) : Subgroup P :=
  Holomorph.cyclicFour.map (sylowEquiv P).toMonoidHom

/-- The subgroup induced by the genuine transposition in the marked equivalence. -/
@[expose] noncomputable def transpositionSubgroup (P : Sylow 2 AutA6) : Subgroup P :=
  Holomorph.transpositionSubgroup.map (sylowEquiv P).toMonoidHom

noncomputable def cyclicFourEquiv (P : Sylow 2 AutA6) :
    cyclicFour P ≃* Multiplicative (ZMod 4) :=
  ((sylowEquiv P).subgroupMap Holomorph.cyclicFour).symm.trans Holomorph.fourEquiv

instance cyclicFour_isCyclic (P : Sylow 2 AutA6) : IsCyclic (cyclicFour P) :=
  (cyclicFourEquiv P).isCyclic.mpr inferInstance

instance cyclicFour_normal (P : Sylow 2 AutA6) : (cyclicFour P).Normal :=
  Holomorph.cyclicFour_normal.map _ (sylowEquiv P).surjective

noncomputable def innerQuotientEquiv (P : Sylow 2 AutA6) :
    (P ⧸ sylowInner P) ≃* Holomorph.E4 :=
  (QuotientGroup.congr Holomorph.innerD (sylowInner P) (sylowEquiv P)
    (sylowEquiv_innerD P)).symm.trans Holomorph.innerQuotientEquiv

theorem frattini_eq (P : Sylow 2 AutA6) : frattini P = cyclicFour P := by
  have h := (sylowEquiv P).mapSubgroup.map_radical
  change (frattini Holomorph.Model).map (sylowEquiv P).toMonoidHom = frattini P at h
  rw [Holomorph.frattini_model] at h
  exact h.symm

theorem derived_eq (P : Sylow 2 AutA6) : commutator P = cyclicFour P := by
  rw [cyclicFour, ← Holomorph.derived_model, map_commutator_eq,
    MonoidHom.range_eq_top.mpr (sylowEquiv P).surjective, commutator_def]

theorem center_eq (P : Sylow 2 AutA6) :
    center P = zpowers (sylowEquiv P (Holomorph.rotation ^ 4)) := by
  rw [← map_center (sylowEquiv P), Holomorph.center_model]
  exact (sylowEquiv P).toMonoidHom.map_zpowers _

private theorem map_centralTwo (P : Sylow 2 AutA6) :
    Holomorph.centralTwo.map (sylowEquiv P).toMonoidHom = center P := by
  rw [← Holomorph.center_model, map_center]

theorem centralizer_inner (P : Sylow 2 AutA6) :
    centralizer (sylowInner P : Set P) = center P ⊔ transpositionSubgroup P := by
  rw [← sylowEquiv_innerD P, ← map_centralizer, Holomorph.centralizer_innerD,
    Subgroup.map_sup, map_centralTwo]
  rfl

noncomputable def centralizerInnerEquiv (P : Sylow 2 AutA6) :
    centralizer (sylowInner P : Set P) ≃* Holomorph.E4 :=
  (MulEquiv.subgroupCongr (by rw [← sylowEquiv_innerD P, ← map_centralizer]; rfl)).trans
    (((sylowEquiv P).subgroupMap _).symm.trans Holomorph.centralizerInnerEquiv)

theorem centralizer_transposition (P : Sylow 2 AutA6) :
    centralizer (transpositionSubgroup P : Set P) = sylowNatural P := by
  rw [transpositionSubgroup, ← map_centralizer, Holomorph.centralizer_transpositionSubgroup,
    sylowEquiv_natural]

noncomputable def centralizerTranspositionEquiv (P : Sylow 2 AutA6) :
    centralizer (transpositionSubgroup P : Set P) ≃*
      (Multiplicative (ZMod 2) × DihedralGroup 4) :=
  (MulEquiv.subgroupCongr (map_centralizer (sylowEquiv P)
    Holomorph.transpositionSubgroup).symm).trans
    (((sylowEquiv P).subgroupMap _).symm.trans Holomorph.centralizerTranspositionEquiv)

noncomputable def centralizerFourEquiv (P : Sylow 2 AutA6) :
    centralizer (cyclicFour P : Set P) ≃* Holomorph.Modular16 :=
  (MulEquiv.subgroupCongr (map_centralizer (sylowEquiv P) Holomorph.cyclicFour).symm).trans
    (((sylowEquiv P).subgroupMap _).symm.trans Holomorph.centralizerFourEquiv)

/-- The center of the central quotient, with its actual quotient map. -/
theorem center_central_quotient (P : Sylow 2 AutA6) :
    center (P ⧸ center P) =
      (cyclicFour P ⊔ transpositionSubgroup P).map (QuotientGroup.mk' (center P)) := by
  let q := QuotientGroup.congr Holomorph.centralTwo (center P) (sylowEquiv P)
    (map_centralTwo P)
  rw [← map_center q, Holomorph.center_central_quotient, map_map]
  change _ = (Holomorph.cyclicFour.map (sylowEquiv P).toMonoidHom ⊔
    Holomorph.transpositionSubgroup.map (sylowEquiv P).toMonoidHom).map _
  rw [← Subgroup.map_sup, map_map]
  rfl

/-- Normality here is in all of P, as in the source's final cyclic-four argument. -/
theorem normal_cyclicFour_sup_transposition (P : Sylow 2 AutA6)
    (V : Subgroup P) [IsCyclic V] [V.Normal] (hV : Nat.card V = 4) :
    V ⊔ transpositionSubgroup P = cyclicFour P ⊔ transpositionSubgroup P := by
  let e := sylowEquiv P
  let W := V.map e.symm.toMonoidHom
  let : IsCyclic W := (e.symm.subgroupMap V).isCyclic.mp inferInstance
  let : W.Normal := (inferInstance : V.Normal).map _ e.symm.surjective
  have hW : Nat.card W = 4 := (Nat.card_congr (e.symm.subgroupMap V).toEquiv).symm.trans hV
  have h := congrArg (Subgroup.map e.toMonoidHom)
    (Holomorph.normal_cyclicFour_sup_transposition W hW)
  have hmap : W.map e.toMonoidHom = V := e.mapSubgroup.apply_symm_apply V
  simpa only [Subgroup.map_sup, hmap, cyclicFour, transpositionSubgroup, e] using h

theorem inner_involution_not_square (P : Sylow 2 AutA6) (u : P)
    (huD : u ∈ sylowInner P) (huZ : u ∉ center P) (hu2 : u ^ 2 = 1) :
    ∀ x : P, x ^ 2 ≠ u := by
  let e := sylowEquiv P
  have hD : e.symm u ∈ Holomorph.innerD := by
    rwa [← sylowEquiv_innerD P, mem_map_equiv] at huD
  have hZ : e.symm u ∉ Holomorph.centralTwo := by
    rwa [← map_centralTwo P, mem_map_equiv] at huZ
  have h2 : (e.symm u) ^ 2 = 1 := by simpa using congrArg e.symm hu2
  intro x hx
  exact Holomorph.inner_involution_not_square _ hD hZ h2 (e.symm x)
    (by simpa using congrArg e.symm hx)

theorem inner_involution_inverts_normal_cyclicFour (P : Sylow 2 AutA6)
    (V : Subgroup P) [IsCyclic V] [V.Normal] (hV : Nat.card V = 4)
    (u : P) (huD : u ∈ sylowInner P) (huZ : u ∉ center P) (hu2 : u ^ 2 = 1) :
    ∀ x ∈ V, u * x * u⁻¹ = x⁻¹ := by
  let e := sylowEquiv P
  let W := V.map e.symm.toMonoidHom
  let : IsCyclic W := (e.symm.subgroupMap V).isCyclic.mp inferInstance
  let : W.Normal := (inferInstance : V.Normal).map _ e.symm.surjective
  have hW : Nat.card W = 4 := (Nat.card_congr (e.symm.subgroupMap V).toEquiv).symm.trans hV
  have hD : e.symm u ∈ Holomorph.innerD := by
    rwa [← sylowEquiv_innerD P, mem_map_equiv] at huD
  have hZ : e.symm u ∉ Holomorph.centralTwo := by
    rwa [← map_centralTwo P, mem_map_equiv] at huZ
  have h2 : (e.symm u) ^ 2 = 1 := by simpa using congrArg e.symm hu2
  intro x hx
  apply e.symm.injective
  simpa only [map_mul, map_inv] using
    Holomorph.inner_involution_inverts_normal_cyclicFour W hW _ hD hZ h2
      (e.symm x) (by exact ⟨x, hx, rfl⟩)

/-- No normality is required in the rank-one classification. -/
theorem rank_one_subgroup_classification (P : Sylow 2 AutA6) (X : Subgroup P)
    (hrank : primeRank 2 X = 1) (hphi : frattini X ≠ ⊥) :
    Nonempty (X ≃* Multiplicative (ZMod 4)) ∨
    Nonempty (X ≃* Multiplicative (ZMod 8)) ∨
    Nonempty (X ≃* QuaternionGroup 2) := by
  let W := X.map (sylowEquiv P).symm.toMonoidHom
  let e : X ≃* W := (sylowEquiv P).symm.subgroupMap X
  have hr : primeRank 2 W = 1 := (primeRank_congr 2 e).symm.trans hrank
  have hf : frattini W ≠ ⊥ := by
    intro h
    apply hphi
    have he := e.mapSubgroup.map_radical
    change (frattini X).map e.toMonoidHom = frattini W at he
    exact ((frattini X).map_eq_bot_iff_of_injective e.injective).mp (he.trans h)
  rcases Holomorph.rank_one_subgroup_classification W hr hf with h | h | h
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inl ⟨e.trans f⟩)
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr ⟨e.trans f⟩)

/-- The needed conclusion of 2.5.22's local calculation, without the false
unrestricted derived-subgroup dichotomy in its printed proof. -/
theorem normal_subgroup_automorphism_primes (P : Sylow 2 AutA6)
    (R : Subgroup P) [R.Normal] {p : ℕ} (hp : p.Prime)
    (hdiv : p ∣ Nat.card (MulAut R)) : p = 2 ∨ p = 3 := by
  let W := R.map (sylowEquiv P).symm.toMonoidHom
  let e : R ≃* W := (sylowEquiv P).symm.subgroupMap R
  let : W.Normal := (inferInstance : R.Normal).map _ (sylowEquiv P).symm.surjective
  apply Holomorph.normal_subgroup_automorphism_primes W hp
  rwa [← Nat.card_congr (MulAut.congr e).toEquiv]

theorem cyclicFour_card (P : Sylow 2 AutA6) : Nat.card (cyclicFour P) = 4 := by
  rw [Nat.card_congr (cyclicFourEquiv P).toEquiv]
  simp

theorem cyclicFour_le_inner (P : Sylow 2 AutA6) : cyclicFour P ≤ sylowInner P := by
  rw [cyclicFour, ← sylowEquiv_innerD P]
  apply map_mono
  exact zpowers_le.mpr (subset_closure (by simp))

/-- The named subgroup P₀ is still the image of an actual transposition on six letters. -/
theorem transpositionSubgroup_image (P : Sylow 2 AutA6) :
    ∃ τ : Equiv.Perm (Fin 6), τ.IsSwap ∧
      (transpositionSubgroup P).map (P : Subgroup AutA6).subtype =
        zpowers (permutationAction τ) :=
  ⟨_, conjugatedTransposition_isSwap P, sylowEquiv_transpositionSubgroup_image P⟩

theorem centralizer_innerCentralizer_involution (P : Sylow 2 AutA6) (u : P)
    (hu : u ∈ centralizer (sylowInner P : Set P)) (huZ : u ∉ center P)
    (hu2 : u ^ 2 = 1) :
    centralizer ({u} : Set P) = centralizer (transpositionSubgroup P : Set P) := by
  let e := sylowEquiv P
  have hD : e.symm u ∈ centralizer (Holomorph.innerD : Set Holomorph.Model) := by
    rwa [← sylowEquiv_innerD P, ← map_centralizer, mem_map_equiv] at hu
  have hZ : e.symm u ∉ Holomorph.centralTwo := by
    rwa [← map_centralTwo P, mem_map_equiv] at huZ
  have h2 : (e.symm u) ^ 2 = 1 := by simpa using congrArg e.symm hu2
  have h := Holomorph.centralizer_innerCentralizer_involution _ hD hZ h2
  rw [Holomorph.centralizer_transpositionSubgroup] at h
  rw [centralizer_transposition, ← sylowEquiv_natural P]
  ext x
  rw [mem_centralizer_singleton_iff, mem_map_equiv, ← h, mem_centralizer_singleton_iff]
  exact ⟨fun hx => by simpa only [map_mul] using congrArg e.symm hx,
    fun hx => e.symm.injective (by simpa only [map_mul] using hx)⟩

/-- The two four-groups in the actual inner Sylow subgroup. -/
@[expose] noncomputable def kleinZero (P : Sylow 2 AutA6) : Subgroup P :=
  Holomorph.kleinZero.map (sylowEquiv P).toMonoidHom

@[expose] noncomputable def kleinOne (P : Sylow 2 AutA6) : Subgroup P :=
  Holomorph.kleinOne.map (sylowEquiv P).toMonoidHom

private theorem map_isKleinFour {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (U : Subgroup G) [IsKleinFour U] : IsKleinFour (U.map e.toMonoidHom) where
  card_four := (Nat.card_congr (e.subgroupMap U).toEquiv).symm.trans IsKleinFour.card_four
  exponent_two := (Monoid.exponent_eq_of_mulEquiv (e.subgroupMap U)).symm.trans
    IsKleinFour.exponent_two

instance kleinZero_isKleinFour (P : Sylow 2 AutA6) : IsKleinFour (kleinZero P) :=
  map_isKleinFour (sylowEquiv P) _

instance kleinOne_isKleinFour (P : Sylow 2 AutA6) : IsKleinFour (kleinOne P) :=
  map_isKleinFour (sylowEquiv P) _

theorem kleinZero_le_inner (P : Sylow 2 AutA6) : kleinZero P ≤ sylowInner P := by
  rw [kleinZero, ← sylowEquiv_innerD P]
  exact map_mono Holomorph.kleinZero_le_innerD

theorem kleinOne_le_inner (P : Sylow 2 AutA6) : kleinOne P ≤ sylowInner P := by
  rw [kleinOne, ← sylowEquiv_innerD P]
  exact map_mono Holomorph.kleinOne_le_innerD

theorem kleinZero_ne_kleinOne (P : Sylow 2 AutA6) : kleinZero P ≠ kleinOne P :=
  fun h => Holomorph.kleinZero_ne_kleinOne ((sylowEquiv P).mapSubgroup.injective h)

theorem rotation_conjugates_klein (P : Sylow 2 AutA6) :
    (kleinZero P).map (MulAut.conj (sylowEquiv P Holomorph.rotation)).toMonoidHom =
      kleinOne P := by
  have h := congrArg (Subgroup.map (sylowEquiv P).toMonoidHom)
    Holomorph.rotation_conjugates_klein
  rw [map_map] at h
  rw [kleinZero, kleinOne, map_map]
  convert h using 2
  ext x
  simp

theorem kleinFour_subgroups_inner (P : Sylow 2 AutA6) (E : Subgroup P)
    [IsKleinFour E] (hED : E ≤ sylowInner P) : E = kleinZero P ∨ E = kleinOne P := by
  let e := sylowEquiv P
  let W := E.map e.symm.toMonoidHom
  let : IsKleinFour W := map_isKleinFour e.symm E
  have hW : W ≤ Holomorph.innerD := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hED hx
    rwa [← sylowEquiv_innerD P, mem_map_equiv] at h
  have hmap : W.map e.toMonoidHom = E := e.mapSubgroup.apply_symm_apply E
  rcases Holomorph.kleinFour_subgroups_innerD W hW with h | h
  · exact Or.inl (hmap.symm.trans (congrArg (Subgroup.map e.toMonoidHom) h))
  · exact Or.inr (hmap.symm.trans (congrArg (Subgroup.map e.toMonoidHom) h))

theorem normalizer_kleinZero (P : Sylow 2 AutA6) :
    normalizer (kleinZero P : Set P) = sylowNatural P := by
  rw [kleinZero, ← map_equiv_normalizer_eq, Holomorph.normalizer_kleinZero,
    sylowEquiv_natural]

theorem normalizer_kleinOne (P : Sylow 2 AutA6) :
    normalizer (kleinOne P : Set P) = sylowNatural P := by
  rw [kleinOne, ← map_equiv_normalizer_eq, Holomorph.normalizer_kleinOne,
    sylowEquiv_natural]

/-- Each of the two four-groups has normalizer of order sixteen in P. -/
theorem card_normalizer_kleinFour (P : Sylow 2 AutA6) (E : Subgroup P)
    [IsKleinFour E] (hED : E ≤ sylowInner P) : Nat.card (normalizer (E : Set P)) = 16 := by
  rcases kleinFour_subgroups_inner P E hED with rfl | rfl
  · rw [normalizer_kleinZero, sylowNatural_card]
  · rw [normalizer_kleinOne, sylowNatural_card]

/-- The natural S₆ intersection is the join of the marked transposition and D₈. -/
theorem natural_eq_transposition_sup_inner (P : Sylow 2 AutA6) :
    sylowNatural P = transpositionSubgroup P ⊔ sylowInner P := by
  have h : Holomorph.natural = Holomorph.transpositionSubgroup ⊔ Holomorph.innerD := by
    rw [Holomorph.natural, Holomorph.transpositionSubgroup, Holomorph.innerD,
      zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  rw [← sylowEquiv_natural P, h, Subgroup.map_sup, sylowEquiv_innerD]
  rfl

/-- The modular order-sixteen centralizer retains its marked generators. -/
theorem centralizer_cyclicFour (P : Sylow 2 AutA6) :
    centralizer (cyclicFour P : Set P) =
      closure {sylowEquiv P Holomorph.rotation, sylowEquiv P Holomorph.transposition} := by
  rw [cyclicFour, ← map_centralizer, Holomorph.centralizer_cyclicFour, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom]

end AlternatingSix.ShadowLocal.SylowGeometry
