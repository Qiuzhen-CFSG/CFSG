module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.ModelWitnesses
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.SylowNormalizer.QuotientCoordinates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction
public import Theory.GroupTheory.SylowThreeNormalizerSection
public import Theory.GroupTheory.DihedralRotationQuotient.SectionEquations

/-!
# The Sylow three-normalizer and its dihedral section

The Frattini construction is applied inside YT, with relative normality.
An intrinsic cover bound puts C_R(X) in V₁; the genuine action kernel
centralizes V, and the fixed-vector calculation then gives C_R(X) = 1.
Restriction of the two quotient maps identifies N_YS(X) with S₃ × S₃ and
constructs the dihedral section with image exactly N_T(X). The same section
identifies N_S(X), lifts inversion from Y/R to X, and gives the reflection
product centralizing V₁ outside V₁.

`exists_lift_of_natural_action` constructs `NaturalCoordinates` from the
genuine rank-four action and applies the Frattini construction. This is a
conditional local helper, not the completed source reduction.
The three intrinsic cover inputs are the bound on C_R(X) and the graph and
square-Frobenius coset calculations, all using the supplied projective marking.
The companion `SylowNormalizer.SourceAssembly` specializes R to S_L = O₂(Y),
derives its restriction to T as L ∩ T, and includes X = X_L × X_D. No section,
normalizer isomorphism, TI or fusion hypothesis is assumed.

Source: Aschbacher--Smith, proof of 15.3.38, combined manuscript
(1 March 2004), printed p.1136. The subsequent rotation, index and cyclic-four
quotient results are supplied by `Theory.GroupTheory.DihedralRotationQuotient`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer
variable {G : Type*} [Group G] [Finite G]

private def infSubgroupEquiv (U N : Subgroup G) :
    (U ⊓ N : Subgroup G) ≃* N.subgroupOf U where
  toFun x := ⟨⟨x, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val, ⟨x.val.property, x.property⟩⟩
  map_mul' _ _ := rfl

omit [Finite G] in
private theorem normalizer_in_S (T : Sylow 2 G) (S L P : Subgroup G)
    (d : DihedralGroup.SplitSection (L.subgroupOf (T : Subgroup G)))
    (hST : S ≤ T)
    (hN : d.sectionMap.range.map (T : Subgroup G).subtype =
      (T : Subgroup G) ⊓ normalizer (P : Set G))
    (hS : ∀ t : T, (t : G) ∈ S ↔ d.projection t ∈ baseFour) :
    S ⊓ normalizer (P : Set G) =
      zpowers (d.firstReflection : G) ⊔ zpowers (d.halfTurn : G) := by
  let F : DihedralGroup 4 →* G := (T : Subgroup G).subtype.comp d.sectionMap
  have hmap : baseFour.map F =
      zpowers (d.firstReflection : G) ⊔ zpowers (d.halfTurn : G) := by
    rw [baseFour_eq, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    simp only [F, MonoidHom.comp_apply, d.sectionMap_sr_zero, d.sectionMap_r_two,
      Subgroup.subtype_apply]
  rw [← hmap]
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ⟨k, rfl⟩, rfl⟩ := hN.ge ⟨hST hx.1, hx.2⟩
    refine ⟨k, ?_, rfl⟩
    change k ∈ baseFour
    simpa only [d.rightInverse k] using (hS (d.sectionMap k)).mp hx.1
  · rintro x ⟨k, hk, rfl⟩
    refine ⟨(hS (d.sectionMap k)).mpr ?_, ?_⟩
    · change k ∈ baseFour at hk
      simpa only [d.rightInverse k] using hk
    · exact (hN.le ⟨d.sectionMap k, ⟨k, rfl⟩, rfl⟩).2

/-- Assembly from compatible action coordinates and the intrinsic cover
calculations. `exists_lift_of_natural_action` discharges the coordinates. -/
theorem exists_lift_of_coordinates
    (T : Sylow 2 G) (M Y S L R V V₁ : Subgroup G)
    (a : NaturalOrthogonalAction M V) (hTM : (T : Subgroup G) ≤ M)
    (hYSM : Y ⊔ S ≤ M) (hST : S ≤ T) (hRT : R ≤ T) (hRY : R ≤ Y)
    [(R.subgroupOf Y).Normal]
    (hYR : Y ≤ normalizer (R : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hq : IsPGroup 3 (Y ⧸ R.subgroupOf Y)) (hR : IsPGroup 2 R)
    (hRL : R.subgroupOf (T : Subgroup G) = L.subgroupOf (T : Subgroup G))
    (hV₁R : V₁ ≤ R) (hV₁V : V₁ ≤ V)
    (c : ProjectiveMarking L 4)
    (d : NaturalCoordinates T M Y S R V V₁ a hTM hYSM)
    (hbound : ∀ X : Sylow 3 Y,
      R ⊓ centralizer (((X : Subgroup Y).map Y.subtype) : Set G) ≤ V₁)
    (hgraph : ∀ t : T, d.tProjection t = .sr 0 → c.Graph (t : G))
    (hfield : ∀ t : T, d.tProjection t = .r 2 → c.Field (t : G)) :
    ∃ b : SylowThreeLift T Y S L c,
      R ⊓ centralizer (((b.X : Subgroup Y).map Y.subtype) : Set G) = ⊥ ∧
      S ⊓ normalizer (((b.X : Subgroup Y).map Y.subtype) : Set G) =
        zpowers (b.dihedral.firstReflection : G) ⊔ zpowers (b.dihedral.halfTurn : G) ∧
      (b.dihedral.firstReflection * b.dihedral.halfTurn : G) ∈ centralizer (V₁ : Set G) ∧
      (b.dihedral.firstReflection * b.dihedral.halfTurn : G) ∉ V₁ := by
  let X : Sylow 3 Y := Classical.choice inferInstance
  let P : Subgroup G := (X : Subgroup Y).map Y.subtype
  have hgen := SylowThreeNormalizer.sylow_supplement Y R hRY hq X
  have hRV : R ≤ centralizer (V : Set G) := by
    intro r hr
    let t : T := ⟨r, hRT hr⟩
    have ht : d.tProjection t = 1 := show t ∈ d.tProjection.ker from d.tKernel.symm ▸ hr
    have ha : a.actor (inclusion hTM t) = 1 := by rw [d.tCompatible, ht, map_one]
    have hm : inclusion hTM t ∈ a.actor.ker := ha
    rw [a.ker_actor] at hm
    exact hm
  have hC : R ⊓ centralizer (P : Set G) = ⊥ :=
    SylowThreeNormalizer.sylow_centralizer_eq_bot_of_bound Y R V X hgen
      hRV d.fixed_vectors ((hbound X).trans hV₁V)
  let d₀ := SylowThreeNormalizer.dihedralSection Y R X hgen hYR hR hC
    (T : Subgroup G) hRT hTR hTY d.tProjection d.tOnto d.tKernel
  let D : DihedralGroup.SplitSection (L.subgroupOf (T : Subgroup G)) :=
    { projection := d₀.projection
      sectionMap := d₀.sectionMap
      rightInverse := d₀.rightInverse
      kernel := d₀.kernel.trans hRL }
  have hproj (t : T) : D.projection t = d.tProjection t := rfl
  have hN : D.sectionMap.range.map (T : Subgroup G).subtype =
      (T : Subgroup G) ⊓ normalizer (P : Set G) :=
    SylowThreeNormalizer.dihedralSection_range Y R X hgen hYR hR hC
      (T : Subgroup G) hRT hTR hTY d.tProjection d.tOnto d.tKernel
  have hS (t : T) : (t : G) ∈ S ↔ D.projection t ∈ baseFour := d.s_preimage t
  have hτ : d.tProjection D.firstReflection = .sr 0 := D.projection_firstReflection
  have hf : d.tProjection D.halfTurn = .r 2 := D.projection_halfTurn
  have ht : d.tProjection D.secondReflection = .sr 1 := D.projection_secondReflection
  have hτS : (D.firstReflection : G) ∈ S := (d.s_preimage _).mpr (hτ ▸ Or.inr (Or.inl rfl))
  have hfS : (D.halfTurn : G) ∈ S := (d.s_preimage _).mpr (hf ▸ Or.inr (Or.inr (Or.inl rfl)))
  have htS : (D.secondReflection : G) ∉ S := by
    intro hs
    have hh := (d.s_preimage _).mp hs
    rw [ht] at hh
    have hn : (DihedralGroup.sr (1 : ZMod 4)) ∉ baseFour := by
      change ¬ (DihedralGroup.sr (1 : ZMod 4) = 1 ∨ _ ∨ _ ∨ _)
      decide
    exact hn hh
  have hYS : Nonempty (((Y ⊔ S : Subgroup G) ⊓ normalizer (P : Set G) : Subgroup G) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
    refine ⟨(infSubgroupEquiv (Y ⊔ S) (normalizer (P : Set G))).trans ?_⟩
    exact SylowThreeNormalizer.normalizerEquiv Y R X hgen hYR hR hC
      (Y ⊔ S) (hRY.trans le_sup_left) (sup_le hYR (hST.trans hTR))
      (sup_le Y.le_normalizer (hST.trans hTY)) d.ysProjection d.ysOnto d.ysKernel
  have hdisj : Disjoint R P :=
    IsPGroup.disjoint_of_ne 2 3 (by decide) R P hR (X.isPGroup'.map Y.subtype)
  have hfinv : ∀ x : X, (MulAut.conj (D.halfTurn : G)) ((x : Y) : G) = (((x : Y) : G))⁻¹ := by
    intro x
    apply SylowThreeNormalizer.normalizer_inverts_of_modulo R P hdisj (D.halfTurn : G)
    · exact (hN.le ⟨D.halfTurn, D.halfTurn_mem_range, rfl⟩).2
    · intro y hy
      exact d.inverts_modulo D.halfTurn hf y ((map_subtype_le _) hy)
    · exact ⟨x, x.property, rfl⟩
  let b : SylowThreeLift T Y S L c :=
    { X := X
      dihedral := D
      normalizer_YS := hYS
      normalizer_T := hN
      first_mem := hτS
      halfTurn_mem := hfS
      second_not_mem := htS
      graph := hgraph D.firstReflection hτ
      field := hfield D.halfTurn hf
      inverts := hfinv }
  have hprod : d.tProjection (D.firstReflection * D.halfTurn) = .sr 2 := by
    rw [map_mul, hτ, hf]
    rfl
  refine ⟨b, hC, normalizer_in_S T S L P D hST hN hS, d.fixes_plane _ hprod, ?_⟩
  intro hm
  have hk : D.firstReflection * D.halfTurn ∈ d.tProjection.ker := d.tKernel.symm ▸ hV₁R hm
  have he : d.tProjection (D.firstReflection * D.halfTurn) = 1 := hk
  rw [hprod] at he
  change DihedralGroup.sr (2 : ZMod 4) = DihedralGroup.r 0 at he
  cases he

/-- Construct the coordinates and then the actual Sylow normalizer. Only the
centralizer bound and recognition of the graph and field cosets remain as
intrinsic cover calculations. All three use the same projective marking.
The coset calculations are quantified over compatible coordinates, so no
quotient map, section or normalizer is supplied as an input. -/
theorem exists_lift_of_natural_action
    (T : Sylow 2 G) (M Y S L R V V₁ : Subgroup G)
    (a : NaturalOrthogonalAction M V) (hTM : (T : Subgroup G) ≤ M)
    (hYSM : Y ⊔ S ≤ M) (hST : S ≤ T) (hRY : R ≤ Y)
    [(R.subgroupOf Y).Normal]
    (hYR : Y ≤ normalizer (R : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (e : (Y ⧸ R.subgroupOf Y) ≃* Multiplicative (Fin 2 → ZMod 3))
    (hTK : (T : Subgroup G) ⊓ centralizer (V : Set G) = R)
    (hYSK : (Y ⊔ S) ⊓ centralizer (V : Set G) = R)
    (hRL : R.subgroupOf (T : Subgroup G) = L.subgroupOf (T : Subgroup G))
    (hV₁R : V₁ ≤ R) (hV₁ : V₁ = a.plane 1)
    (hS : ∀ t : T, (t : G) ∈ S ↔ (a.actor (inclusion hTM t)).right = 1)
    (c : ProjectiveMarking L 4)
    (hbound : ∀ X : Sylow 3 Y,
      R ⊓ centralizer (((X : Subgroup Y).map Y.subtype) : Set G) ≤ V₁)
    (hgraph : ∀ d : NaturalCoordinates T M Y S R V V₁ a hTM hYSM,
      ∀ t : T, d.tProjection t = .sr 0 → c.Graph (t : G))
    (hfield : ∀ d : NaturalCoordinates T M Y S R V V₁ a hTM hYSM,
      ∀ t : T, d.tProjection t = .r 2 → c.Field (t : G)) :
    ∃ b : SylowThreeLift T Y S L c,
      R ⊓ centralizer (((b.X : Subgroup Y).map Y.subtype) : Set G) = ⊥ ∧
      S ⊓ normalizer (((b.X : Subgroup Y).map Y.subtype) : Set G) =
        zpowers (b.dihedral.firstReflection : G) ⊔ zpowers (b.dihedral.halfTurn : G) ∧
      (b.dihedral.firstReflection * b.dihedral.halfTurn : G) ∈ centralizer (V₁ : Set G) ∧
      (b.dihedral.firstReflection * b.dihedral.halfTurn : G) ∉ V₁ := by
  obtain ⟨d⟩ := NaturalConstruction.exists_coordinates T M Y S R V V₁ a hTM hYSM
    hST hRY e hTK hYSK hV₁ hS
  have hRT : R ≤ T := hTK.ge.trans inf_le_left
  have hq : IsPGroup 3 (Y ⧸ R.subgroupOf Y) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  have hV₁V : V₁ ≤ V := hV₁ ▸ map_subtype_le _
  exact exists_lift_of_coordinates T M Y S L R V V₁ a hTM hYSM hST hRT hRY
    hYR hTR hTY hq (T.isPGroup'.to_le hRT) hRL hV₁R hV₁V c d
    hbound (hgraph d) (hfield d)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer
