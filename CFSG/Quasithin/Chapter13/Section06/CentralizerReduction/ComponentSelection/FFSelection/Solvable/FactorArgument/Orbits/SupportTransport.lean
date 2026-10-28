module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Orbits.FactorConjugation

/-!
# Transport and assembly for the four-element supports

The specified internal space product gives disjoint supports generating U_H.
Conjugation through the literal star quotient transports a support whenever
it transports its S₃ factor. Thus T_v* transitivity makes every nonempty
invariant sum of supports equal to U_H.

`InvariantSupportSums` isolates the remaining local module calculation:
an X-invariant subgroup is the sum of the supports it contains. It does not
assert transitivity or irreducibility, and its construction remains necessary
before applying the conditional irreducibility theorem below.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.6.13, printed p.929.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.NormalS3Decomposition
variable {G : Type*} [Group G] {z v : G} {X : Subgroup (Gstar z v)}
variable (d : NormalS3Decomposition z v X)

/-- The subgroup denoted U_i in the source, with its original ambient inclusion. -/
abbrev support (i : Fin d.count) : Subgroup G := factorSupport z v d.H (d.factor i)

theorem movedSubgroup_normalized :
    Gv v ≤ normalizer (movedSubgroup z v d.H : Set G) := by
  let := d.normal
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅Uv z v, starPreimage z v d.H⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom = _
  have hU : (Uv z v).map (MulAut.conj g).toMonoidHom = Uv z v :=
    mem_normalizer_iff_map_conj_eq.mp (Gv_normalizes_Uv z v hg)
  have hH : (starPreimage z v d.H).map (MulAut.conj g).toMonoidHom =
      starPreimage z v d.H :=
    mem_normalizer_iff_map_conj_eq.mp (starPreimage_normalized z v d.H hg)
  rw [map_commutator, hU, hH]
  rfl

theorem support_le (i : Fin d.count) : d.support i ≤ movedSubgroup z v d.H :=
  le_normalizer_iff_commutator_le_left.mp
    ((starPreimage_le_Gv z v (d.factor i)).trans d.movedSubgroup_normalized)

private theorem starPreimage_map_conj (g : Gv v) (K : Subgroup (Gstar z v)) :
    starPreimage z v (K.map (MulAut.conj (starMk z v g)).toMonoidHom) =
      (starPreimage z v K).map (MulAut.conj (g : G)).toMonoidHom := by
  have he : (K.map (MulAut.conj (starMk z v g)).toMonoidHom).comap (starMk z v) =
      (K.comap (starMk z v)).map (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [mem_comap, mem_map_equiv]
    change (starMk z v g)⁻¹ * starMk z v x * starMk z v g ∈ K ↔
      starMk z v (g⁻¹ * x * g) ∈ K
    rw [map_mul, map_mul, map_inv]
  unfold starPreimage
  rw [he, map_map, map_map]
  rfl

/-- Factor conjugation transports the literal double-commutator supports. -/
theorem support_map_conj (g : Gv v) (i j : Fin d.count)
    (h : (d.factor i).map (MulAut.conj (starMk z v g)).toMonoidHom = d.factor j) :
    (d.support i).map (MulAut.conj (g : G)).toMonoidHom = d.support j := by
  change (⁅movedSubgroup z v d.H, starPreimage z v (d.factor i)⁆ : Subgroup G).map _ = _
  have hW : (movedSubgroup z v d.H).map (MulAut.conj (g : G)).toMonoidHom =
      movedSubgroup z v d.H :=
    mem_normalizer_iff_map_conj_eq.mp (d.movedSubgroup_normalized g.property)
  rw [map_commutator, hW, ← starPreimage_map_conj, h]
  rfl

noncomputable def supportProductMap : (∀ i, d.support i) →* G :=
  (movedSubgroup z v d.H).subtype.comp d.space.toMonoidHom

@[simp] theorem supportProductMap_single (i : Fin d.count) (a : d.support i) :
    d.supportProductMap (Pi.mulSingle i a) = (a : G) := d.space_single i a

theorem supportProductMap_injective : Function.Injective d.supportProductMap :=
  (movedSubgroup z v d.H).subtype_injective.comp d.space.injective

/-- Distinct support subgroups have trivial intersection in the original G. -/
theorem support_disjoint {i j : Fin d.count} (hij : i ≠ j) :
    Disjoint (d.support i) (d.support j) := by
  rw [Subgroup.disjoint_def]
  intro a hai haj
  have he : Pi.mulSingle i (⟨a, hai⟩ : d.support i) =
      Pi.mulSingle j (⟨a, haj⟩ : d.support j) :=
    d.supportProductMap_injective
      ((d.supportProductMap_single i ⟨a, hai⟩).trans
        (d.supportProductMap_single j ⟨a, haj⟩).symm)
  have hi := congrFun he i
  simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at hi
  exact congrArg Subtype.val hi

/-- The full preimage of H normalizes each support individually. -/
theorem support_normalized (i : Fin d.count) :
    starPreimage z v d.H ≤ normalizer (d.support i : Set G) := by
  have hN : d.H ≤ normalizer (d.factor i : Set (Gstar z v)) :=
    (normal_subgroupOf_iff_le_normalizer (d.factor_le i)).mp (d.factor_normal_in_H i)
  intro g hg
  change ∃ a : Gv v, starMk z v a ∈ d.H ∧ (a : G) = g at hg
  obtain ⟨g, hg, rfl⟩ := hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact d.support_map_conj g i i (mem_normalizer_iff_map_conj_eq.mp (hN hg))

theorem iSup_support : (⨆ i, d.support i) = movedSubgroup z v d.H := by
  apply le_antisymm (iSup_le d.support_le)
  intro a ha
  let x := d.space.symm ⟨a, ha⟩
  have hc : Pairwise fun i j => ∀ (a : d.support i) (b : d.support j),
      Commute ((d.support i).subtype a) ((d.support j).subtype b) := by
    intro i j hij a b
    change Commute (a : G) (b : G)
    simpa only [d.supportProductMap_single] using
      (Pi.mulSingle_commute hij a b).map d.supportProductMap
  let f := MonoidHom.noncommPiCoprod (fun i => (d.support i).subtype) hc
  have hf : f = d.supportProductMap := by
    apply MonoidHom.pi_ext
    intro i a
    simp only [f, MonoidHom.noncommPiCoprod_mulSingle,
      d.supportProductMap_single, Subgroup.subtype_apply]
  have hr : f.range = ⨆ i, d.support i := by
    change (MonoidHom.noncommPiCoprod (fun i => (d.support i).subtype) hc).range = _
    rw [MonoidHom.noncommPiCoprod_range]
    simp only [Subgroup.range_subtype]
  rw [← hr]
  refine ⟨x, ?_⟩
  rw [hf]
  exact congrArg Subtype.val (d.space.apply_symm_apply ⟨a, ha⟩)

theorem support_ne_bot (i : Fin d.count) : d.support i ≠ ⊥ := by
  intro hz
  have hc := d.support_card i
  change Nat.card (d.support i) = 4 at hc
  rw [hz, card_bot] at hc
  omega

theorem movedSubgroup_ne_bot : movedSubgroup z v d.H ≠ ⊥ := by
  intro hz
  exact d.support_ne_bot ⟨0, d.count_pos⟩
    (le_bot_iff.mp ((d.support_le _).trans hz.le))

/-- A local module-theoretic output: every X-invariant subgroup of U_H is
exactly the sum of the individual supports it contains. It permits all
coordinate sums; no T_v transitivity or irreducibility is asserted. -/
@[expose] def InvariantSupportSums : Prop :=
  ∀ B : Subgroup G, B ≤ movedSubgroup z v d.H →
    starPreimage z v X ≤ normalizer (B : Set G) →
      B = ⨆ i : Fin d.count, ⨆ (_ : d.support i ≤ B), d.support i

/-- Transitivity upgrades the local invariant-support decomposition to
irreducibility for the actual X T_v actor. -/
theorem irreducible_of_invariantSupportSums (T : Subgroup G)
    (htrans : d.FactorsTransitive T) (hsum : d.InvariantSupportSums) :
    IrreducibleOn (starPreimage z v X ⊔ Tv T v) (movedSubgroup z v d.H) := by
  refine ⟨d.movedSubgroup_ne_bot,
    (sup_le (starPreimage_le_Gv z v X) inf_le_right).trans d.movedSubgroup_normalized, ?_⟩
  intro B hBW hn
  by_cases hbot : B = ⊥
  · exact Or.inl hbot
  right
  have he := hsum B hBW (le_sup_left.trans hn)
  obtain ⟨i, hi⟩ : ∃ i, d.support i ≤ B := by
    by_contra! hh
    apply hbot
    rw [he]
    simp only [hh, iSup_false, iSup_bot]
  have hle (j : Fin d.count) : d.support j ≤ B := by
    obtain ⟨t, ht, hij⟩ := htrans i j
    obtain ⟨g, hg, rfl⟩ := mem_map.mp ht
    have htB : (g : G) ∈ normalizer (B : Set G) :=
      (show Tv T v ≤ normalizer (B : Set G) from le_sup_right.trans hn) hg
    have hb := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hi
    have hB : B.map (MulAut.conj (g : G)).toMonoidHom = B :=
      mem_normalizer_iff_map_conj_eq.mp htB
    rw [d.support_map_conj g i j hij, hB] at hb
    exact hb
  exact le_antisymm hBW (d.iSup_support ▸ iSup_le hle)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.NormalS3Decomposition
end
