module

public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.NormLattice.Coordinates.Construction.Orbit
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Orbit

/-!
# Component and norm embeddings of the oriented pairs

The selected conjugates embed in the actual component orbit, commute at
distinct indices, and generate that orbit. The norm embeddings are the products
of the two equally oriented component embeddings. Their ranges generate the
actual norm diagonal. Conjugation by `r_j * r_i⁻¹` carries both embeddings
of pair i to those of pair j, retaining the prescribed B-action.

Source: GLS2, Chapter B, Lemma 3.27(v),(ix), and Chapter G, Theorem 25.14,
Steps 2--3. All statements concern the original ambient embeddings.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Representation.QuadraticFourGroup.PairConstruction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}
  {h : Hypotheses ρ L B a}
namespace Frame
variable (d : Frame h)

def actor (p : Fin d.count × Bool) : B :=
  if p.2 then ⟨a,h.mem⟩ * d.rep p.1 else d.rep p.1
@[simp] theorem coe_actor (p : Fin d.count × Bool) :
    (d.actor p : G) = if p.2 then a * d.rep p.1 else d.rep p.1 := by
  rcases p with ⟨i,s⟩
  cases s <;> rfl

def embedding (p : Fin d.count × Bool) : L →* componentOrbit L B :=
  ((MulAut.conj (d.actor p : G)).toMonoidHom.comp L.subtype).codRestrict
    (componentOrbit L B) (fun x =>
      le_iSup (fun b : B => conj L (b : G)) (d.actor p) (mem_map_of_mem _ x.property))
@[simp] theorem embedding_apply (p : Fin d.count × Bool) (x : L) :
    (d.embedding p x : G) = MulAut.conj (d.actor p : G) (x : G) := rfl

theorem embedding_injective (p : Fin d.count × Bool) : Function.Injective (d.embedding p) := by
  intro x y he
  exact Subtype.ext ((MulAut.conj (d.actor p : G)).injective (congrArg Subtype.val he))

theorem embedding_commute : Pairwise fun p q => ∀ x y : L,
    Commute (d.embedding p x) (d.embedding q y) := by
  intro p q hpq x y
  have hne : conj L (d.actor p : G) ≠ conj L (d.actor q : G) := by
    simpa only [coe_actor] using (fun he => hpq (d.distinct he))
  have hc := (h.component.map_conj (d.actor p : G)).commutator_eq_bot_of_ne
    (h.component.map_conj (d.actor q : G)) hne
  apply Subtype.ext
  exact (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hc)
    (mem_map_of_mem _ x.property)) _ (mem_map_of_mem _ y.property)).symm

theorem embedding_range (p : Fin d.count × Bool) :
    (d.embedding p).range.map (componentOrbit L B).subtype = conj L (d.actor p : G) := by
  rw [MonoidHom.map_range]
  change ((MulAut.conj (d.actor p : G)).toMonoidHom.comp L.subtype).range = _
  rw [MonoidHom.range_comp, range_subtype]
  rfl

theorem embedding_generate : (⨆ p, (d.embedding p).range) = ⊤ := by
  apply map_injective (componentOrbit L B).subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
  simp_rw [embedding_range]
  apply le_antisymm
  · exact iSup_le fun p => le_iSup (fun b : B => conj L (b : G)) (d.actor p)
  · apply iSup_le
    intro b
    obtain ⟨p,hp⟩ := d.covers b
    have hp' : conj L (b : G) = conj L (d.actor p : G) := by simpa only [coe_actor] using hp
    change conj L (b : G) ≤ _
    rw [hp']
    exact le_iSup (fun p : Fin d.count × Bool => conj L (d.actor p : G)) p

/-- Equality of component embeddings transports the actual norm images. -/
theorem norm_conjugate_eq {b c : B} (he : conj L (b : G) = conj L (c : G)) :
    conj (NormPair.normRange h.component h.moves) (b : G) =
      conj (NormPair.normRange h.component h.moves) (c : G) := by
  apply localFactor_conjugate_eq_of_component_conjugate_eq (L := L) (A := B) (K := _)
    (fun z hz => NormPair.normalizes_norm h.component h.moves
      (commute h ⟨z,hz.1⟩) hz.2) b c he

/-- Conjugating a norm generator gives the product of the two oriented embeddings. -/
theorem norm_generator (i : Fin d.count) (x : L) :
    MulAut.conj (d.rep i : G) (componentSwapNorm h.component h.moves x) =
      (d.embedding (i,false) x : G) * (d.embedding (i,true) x : G) := by
  change MulAut.conj (d.rep i : G) ((x : G) * MulAut.conj a (x : G)) =
    MulAut.conj (d.rep i : G) (x : G) * MulAut.conj (a * d.rep i : G) (x : G)
  rw [map_mul, ← (commute h (d.rep i)).eq]
  simp [MulAut.conj_apply, mul_assoc]

theorem norm_actor (p : Fin d.count × Bool) :
    conj (NormPair.normRange h.component h.moves) (d.actor p : G) =
      conj (NormPair.normRange h.component h.moves) (d.rep p.1 : G) := by
  have ha : conj (NormPair.normRange h.component h.moves) a =
      NormPair.normRange h.component h.moves :=
    mem_normalizer_iff_map_conj_eq.mp (NormPair.normalizes_norm_of_pair
      h.component h.moves (by simpa only [pow_two] using square h)
      (Commute.refl a) (Or.inr rfl))
  rcases p with ⟨i,s⟩
  cases s
  · rfl
  · change conj _ (a * (d.rep i : G)) = _
    rw [← (commute h (d.rep i)).eq, conj_mul, ha]

/-- One norm subgroup per oriented pair generates the source norm diagonal. -/
theorem norm_generate : h.normDiagonal =
    ⨆ i, conj (NormPair.normRange h.component h.moves) (d.rep i : G) := by
  apply le_antisymm
  · apply iSup_le
    intro b
    obtain ⟨p,hp⟩ := d.covers b
    have hp' : conj L (b : G) = conj L (d.actor p : G) := by
      simpa only [coe_actor] using hp
    exact ((norm_conjugate_eq (h := h) hp').trans (d.norm_actor p)).le.trans
      (le_iSup (fun i : Fin d.count =>
        conj (NormPair.normRange h.component h.moves) (d.rep i : G)) p.1)
  · exact iSup_le fun i => le_iSup
      (fun b : B => conj (NormPair.normRange h.component h.moves) (b : G)) (d.rep i)

def normEmbedding (i : Fin d.count) : L →* componentOrbit L B :=
  ((MulAut.conj (d.rep i : G)).toMonoidHom.comp
    (componentSwapNorm h.component h.moves)).codRestrict (componentOrbit L B) (fun x => by
      change MulAut.conj (d.rep i : G) (componentSwapNorm h.component h.moves x) ∈ _
      rw [d.norm_generator]
      exact mul_mem (d.embedding (i,false) x).property (d.embedding (i,true) x).property)

theorem normEmbedding_apply (i : Fin d.count) (x : L) :
    d.normEmbedding i x = d.embedding (i,false) x * d.embedding (i,true) x :=
  Subtype.ext (d.norm_generator i x)

theorem normEmbedding_range (i : Fin d.count) :
    (d.normEmbedding i).range.map (componentOrbit L B).subtype =
      conj (NormPair.normRange h.component h.moves) (d.rep i : G) := by
  rw [MonoidHom.map_range]
  change ((MulAut.conj (d.rep i : G)).toMonoidHom.comp
    (componentSwapNorm h.component h.moves)).range = _
  exact MonoidHom.range_comp _ _

theorem normEmbedding_generate : (⨆ i, (d.normEmbedding i).range) =
    h.normDiagonal.subgroupOf (componentOrbit L B) := by
  apply map_injective (componentOrbit L B).subtype_injective
  rw [Subgroup.map_iSup, map_subgroupOf_eq_of_le
    (h.normDiagonal_le_orbitCentralizer.trans inf_le_left)]
  simp_rw [normEmbedding_range]
  exact d.norm_generate.symm

/-- Actual B-conjugation carries both oriented embeddings of one pair to another. -/
theorem conjugation_embedding (i j : Fin d.count) (s : Bool) (x : L) :
    h.orbitConjugation (d.rep j * (d.rep i)⁻¹) (d.embedding (i,s) x) =
      d.embedding (j,s) x := by
  apply Subtype.ext
  let b : B := d.rep j * (d.rep i)⁻¹
  change MulAut.conj (b : G) (MulAut.conj (d.actor (i,s) : G) (x : G)) =
    MulAut.conj (d.actor (j,s) : G) (x : G)
  have hab : (b : G) * a = a * b := (commute h b).eq
  have hc : (b : G) * (d.actor (i,s) : G) = d.actor (j,s) := by
    cases s
    · change ((d.rep j : G) * (d.rep i : G)⁻¹) * (d.rep i : G) = _
      simp
    · change (b : G) * (a * (d.rep i : G)) = a * (d.rep j : G)
      rw [← mul_assoc, hab, mul_assoc]
      dsimp [b]
      simp
  calc
    _ = MulAut.conj ((b : G) * (d.actor (i,s) : G)) (x : G) := by
      change (b : G) * ((d.actor (i,s) : G) * (x : G) * (d.actor (i,s) : G)⁻¹) * (b : G)⁻¹ =
        ((b : G) * (d.actor (i,s) : G)) * (x : G) * ((b : G) * (d.actor (i,s) : G))⁻¹
      group
    _ = _ := by rw [hc]

end Frame
end Representation.QuadraticFourGroup.PairConstruction

end
