module



public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Kernel
public import Theory.Representation.SylowFixedCentralQuotient
public import Theory.Representation.BinaryPermutation.EightSylowFixed
public import Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Geometry

/-!
# Marking the original seed through the natural quotient

The seed is Sylow-fixed in W_K itself. Its image in the natural module is
nonzero by movement, and has a conjugate four-block stabilizer. The binary
central-displacement lemma lifts that stabilizer through C_{W_K}(K), using
centrality only under K⁺ and the actual Tᵥ⁺ supplement. The resulting marking
therefore describes the original seed before quotienting, with all extension
effects retained. The actual C_K(z) image follows by LocalAction's centralizer
identity; the checked exceptional equivalence identifies the end-node parabolic.

These theorems consume NaturalSeedSection. Its construction from the source
FF alternatives remains necessary for the source theorem.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the paragraph following 13.6.23, printed p.933 (PDF p.950).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
open ComponentSelection Theory.SpecificGroups.SymmetricEight
variable {G : Type*} [Group G] [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

omit [Finite G] in
/-- The original seed is fixed by the literal Tᵥ plus image. -/
theorem seed_fixed_by_Tv (a : Gplus K L T z v hL hz)
    (ha : a ∈ plusImage K L T z v hL hz (Tv T v)) :
    representation K L T z v hL hz a
      (Additive.ofMul (markedSeed K L T z v)) = Additive.ofMul (markedSeed K L T z v) := by
  obtain ⟨t, ht, rfl⟩ := ha
  exact (mk_mem_seedStabilizer K L T z v hL hz t).mpr (hz ht)

omit [Finite G] in
/-- Movement of the original seed forces nonzero natural quotient image. -/
theorem seed_projection_ne_zero
    (d : NaturalSeedSection K L T z v hL hz)
    (hmove : ¬ K ≤ Gv z) : d.projection (Additive.ofMul (markedSeed K L T z v)) ≠ 0 := by
  intro hzero
  apply hmove
  intro k hk
  let a : plusActor K L T v := ⟨k, K_le_plusActor K L T v hk⟩
  have ha : plusMk K L T z v hL hz a ∈ plusImage K L T z v hL hz K := ⟨a, hk, rfl⟩
  have hf := (d.kernel _).mp hzero ⟨_, ha⟩
  exact (mk_mem_seedStabilizer K L T z v hL hz a).mp hf

/-- Rotate the actor and quotient coordinates together; the fixed kernel is retained. -/
noncomputable def NaturalSeedSection.conjugate
    (d : NaturalSeedSection K L T z v hL hz) (r : Equiv.Perm (Fin 8)) :
    NaturalSeedSection K L T z v hL hz where
  actor := d.actor.trans (MulAut.conj r)
  component_image := by
    change (plusImage K L T z v hL hz K).map
      ((MulAut.conj r).toMonoidHom.comp d.actor.toMonoidHom) = _
    rw [← Subgroup.map_map, d.component_image]
    exact mem_normalizer_iff_map_conj_eq.mp (by
      rw [Subgroup.normalizer_eq_top]
      exact mem_top r)
  projection := (BinaryPermutation.naturalRepresentation (Fin 8) r).comp d.projection
  surjective := ((BinaryPermutation.naturalRepresentation (Fin 8)).apply_bijective r).surjective.comp d.surjective
  equivariant := by
    intro g w
    change BinaryPermutation.naturalRepresentation (Fin 8) r
        (d.projection (representation K L T z v hL hz g w)) = _
    rw [d.equivariant]
    change _ = BinaryPermutation.naturalRepresentation (Fin 8) (r * d.actor g * r⁻¹)
      (BinaryPermutation.naturalRepresentation (Fin 8) r (d.projection w))
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  kernel := by
    intro w
    have hinj := ((BinaryPermutation.naturalRepresentation (Fin 8)).apply_bijective r).injective
    change BinaryPermutation.naturalRepresentation (Fin 8) r (d.projection w) = 0 ↔ _
    rw [← (BinaryPermutation.naturalRepresentation (Fin 8) r).map_zero,
      hinj.eq_iff, d.kernel]

/-- A natural quotient with the actual fixed kernel marks the original seed.
The conjugating permutation is retained so that section coordinates can be
rotated compatibly with this same actor marking. -/
theorem exists_seed_marking
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hmove : ¬ K ≤ Gv z)
    (S : Sylow 2 (Gplus K L T z v hL hz))
    (hS : (S : Subgroup _) = plusImage K L T z v hL hz (Tv T v))
    (d : NaturalSeedSection K L T z v hL hz) :
    ∃ (r : Equiv.Perm (Fin 8)) (d' : NaturalSeedSection K L T z v hL hz),
      d' = d.conjugate K L T z v hL hz r ∧
      (seedStabilizer K L T z v hL hz).map d'.actor.toMonoidHom =
        A6ShadowTwoLocals.fourStabilizer := by
  let ρ := representation K L T z v hL hz
  let σ := (BinaryPermutation.naturalRepresentation (Fin 8)).comp d.actor.toMonoidHom
  let u := Additive.ofMul (markedSeed K L T z v)
  let C := plusImage K L T z v hL hz K
  let : C.Normal := plusComponent_normal K L T z v hL hz hLK hK
  have hs : ∀ s ∈ (S : Subgroup _), ρ s u = u := by
    intro s hs
    exact seed_fixed_by_Tv K L T z v hL hz s (hS ▸ hs)
  have hgen : C ⊔ (S : Subgroup _) = ⊤ := by
    rw [hS]
    exact plusComponent_sup_Tv K L T z v hL hz hK hLK
  have hlift := Representation.SylowFixedCentralQuotient.fixed_iff_of_component_central_kernel
    ρ σ d.projection d.equivariant C (fun k w hw => (d.kernel w).mp hw k) S hgen u hs
  let Q := S.mapSurjective (f := d.actor.toMonoidHom) d.actor.surjective
  have hQ : ∀ g ∈ (Q : Subgroup _), BinaryPermutation.naturalRepresentation (Fin 8) g
      (d.projection u) = d.projection u := by
    rintro g ⟨s, hs', rfl⟩
    exact (d.equivariant s u).symm.trans (congrArg d.projection (hs s hs'))
  obtain ⟨r, hr⟩ := BinaryPermutation.EightSylowFixed.exists_conjugate_stabilizer Q
    (d.projection u) (seed_projection_ne_zero K L T z v hL hz d hmove) hQ
  let d' := d.conjugate K L T z v hL hz r
  have hi (g : Gplus K L T z v hL hz) : g ∈ seedStabilizer K L T z v hL hz ↔
      d'.actor g ∈ A6ShadowTwoLocals.fourStabilizer :=
    (hlift g).trans (hr (d.actor g))
  refine ⟨r, d', rfl, ?_⟩
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (hi a).mp ha
  · intro hg
    exact ⟨d'.actor.symm g, (hi _).mpr (by simpa only [MulEquiv.apply_symm_apply] using hg),
      d'.actor.apply_symm_apply g⟩

omit [Finite G] [IsElementaryAbelian 2 (WK K L T z v)] in
/-- The marked original-seed stabilizer identifies the literal C_K(z) image. -/
theorem centralizer_image_of_seed_marking
    (e : Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8))
    (hC : (plusImage K L T z v hL hz K).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hseed : (seedStabilizer K L T z v hL hz).map e.toMonoidHom =
      A6ShadowTwoLocals.fourStabilizer) :
    (plusImage K L T z v hL hz (K ⊓ Gv z)).map e.toMonoidHom =
      alternatingGroup (Fin 8) ⊓ A6ShadowTwoLocals.fourStabilizer := by
  rw [plusImage_centralizer, Subgroup.map_inf _ _ _ e.injective, hC, hseed]

omit [Finite G] [IsElementaryAbelian 2 (WK K L T z v)] in
/-- The same centralizer image is the actual two-plane parabolic under the
checked exceptional equivalence, namely the parabolic determined by the end nodes. -/
theorem centralizer_parabolic_image
    (e : Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8))
    (hC : (plusImage K L T z v hL hz K).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hseed : (seedStabilizer K L T z v hL hz).map e.toMonoidHom =
      A6ShadowTwoLocals.fourStabilizer) :
    (((plusImage K L T z v hL hz (K ⊓ Gv z)).map e.toMonoidHom).subgroupOf
      (alternatingGroup (Fin 8))).map FourBlockParabolic.equiv.toMonoidHom =
        BinaryLinear.parabolic FourBlockParabolic.plane := by
  rw [centralizer_image_of_seed_marking K L T z v hL hz e hC hseed]
  have h : (alternatingGroup (Fin 8) ⊓ A6ShadowTwoLocals.fourStabilizer).subgroupOf
      (alternatingGroup (Fin 8)) =
        A6ShadowTwoLocals.fourStabilizer.subgroupOf (alternatingGroup (Fin 8)) := by
    ext a
    exact and_iff_right a.property
  rw [h, ← FourBlockParabolic.parabolic_comap,
    map_comap_eq_self_of_surjective FourBlockParabolic.equiv.surjective]

/-- Application to the genuine local Sylow and selected Y_z component.
The natural quotient is still an explicit recognition obligation. -/
theorem exists_marked_centralizer
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (d : NaturalSeedSection K L T z v hL hz) :
    ∃ (r : Equiv.Perm (Fin 8)) (d' : NaturalSeedSection K L T z v hL hz),
      d' = d.conjugate K L T z v hL hz r ∧
      (seedStabilizer K L T z v hL hz).map d'.actor.toMonoidHom =
        A6ShadowTwoLocals.fourStabilizer ∧
      (plusImage K L T z v hL hz (K ⊓ Gv z)).map d'.actor.toMonoidHom =
        alternatingGroup (Fin 8) ⊓ A6ShadowTwoLocals.fourStabilizer ∧
      (((plusImage K L T z v hL hz (K ⊓ Gv z)).map d'.actor.toMonoidHom).subgroupOf
        (alternatingGroup (Fin 8))).map FourBlockParabolic.equiv.toMonoidHom =
          BinaryLinear.parabolic FourBlockParabolic.plane := by
  have hx := (invariant_component_consequences K L T z v hY hK).1
  have hmove : ¬ K ≤ Gv z := fun h => hx.2
    ((starPreimage_starImage_centralizes_seed_iff z v K hY.1.1).mpr h)
  obtain ⟨S, hS⟩ := exists_plus_sylow K L T z v hL hz hY.1.1 hSyl
  obtain ⟨r, d', hr, hseed⟩ := exists_seed_marking K L T z v hL hz hK hLK hmove S hS d
  exact ⟨r, d', hr, hseed,
    centralizer_image_of_seed_marking K L T z v hL hz d'.actor d'.component_image hseed,
    centralizer_parabolic_image K L T z v hL hz d'.actor d'.component_image hseed⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
