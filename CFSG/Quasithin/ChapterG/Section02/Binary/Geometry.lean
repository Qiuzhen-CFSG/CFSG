module

public import CFSG.Quasithin.ChapterG.Section02.Binary.Source

/-!
# Irreducibility of the actual binary natural C₃ action

A checked calculation on the eight binary triples shows that the cubic
permutes the three nonzero vectors of the even-weight plane transitively.
The literal star map is surjective, so natural coordinates transport this
orbit statement to conjugation by the original L. Every nonzero invariant
subgroup of V therefore contains all of V.

Source: Aschbacher–Smith, G.2.3, printed p.333.
-/
open InvertedCubicTensor BinaryPermutation
private theorem orbit : ∀ v w : Fin 3 → ZMod 2,
    (∑ i, v i) = 0 → (∑ i, w i) = 0 → v ≠ 0 → w ≠ 0 →
    ∃ k : Fin 3, ∀ i, v ((cubic ^ k.val)⁻¹ i) = w i := by
  decide +kernel
private theorem natural_transitive : ∀ v w : core (Fin 3), v ≠ 0 → w ≠ 0 →
    ∃ a : alternatingGroup (Fin 3), coreRepresentation (Fin 3) a.val v = w := by
  intro v w hv hw
  have hv' : v.val ≠ 0 := fun h => hv (Subtype.ext h)
  have hw' : w.val ≠ 0 := fun h => hw (Subtype.ext h)
  obtain ⟨k, hk⟩ := orbit v.val w.val v.property w.property hv' hw'
  have hca : cubic ∈ alternatingGroup (Fin 3) := by
    change Equiv.Perm.sign cubic = 1
    decide +kernel
  refine ⟨⟨cubic ^ k.val, (alternatingGroup (Fin 3)).pow_mem hca k.val⟩, ?_⟩
  apply Subtype.ext
  exact funext hk

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] {D : Setup G}
/-- The source natural coordinates imply the invariant-subgroup form of
irreducibility used by rank_one_central_first_layer. -/
public theorem BinaryNaturalData.irreducible (b : D.BinaryNaturalData)
    (A : Subgroup G) (hAV : A ≤ D.V) (hLA : D.L ≤ normalizer (A : Set G)) :
    A = ⊥ ∨ A = D.V := by
  by_cases hA : A = ⊥
  · exact Or.inl hA
  right
  apply le_antisymm hAV
  obtain ⟨a, ha⟩ := ne_bot_iff_exists_ne_one.mp hA
  let av : D.V := ⟨a, hAV a.property⟩
  have hav : av ≠ 1 := fun h => ha (Subtype.ext (congrArg (fun x : D.V => (x : G)) h))
  intro v hv
  by_cases hv1 : v = 1
  · simpa only [hv1] using A.one_mem
  let vv : D.V := ⟨v, hv⟩
  have havc : (b.coordinates av).toAdd ≠ 0 := by
    intro h
    apply hav
    apply b.coordinates.injective
    exact h.trans b.coordinates.map_one.symm
  have hvvc : (b.coordinates vv).toAdd ≠ 0 := by
    intro h
    apply hv1
    exact congrArg Subtype.val (b.coordinates.injective (h.trans b.coordinates.map_one.symm))
  obtain ⟨r, hr⟩ := natural_transitive _ _ havc hvvc
  obtain ⟨l, hl⟩ := D.binaryLStar_surjective (b.quotientEquiv.symm r)
  have hlr : b.quotientEquiv (D.binaryLStar l) = r := by rw [hl]; exact b.quotientEquiv.apply_symm_apply r
  let c : D.V := D.V.normalizerMonoidHom ⟨l, b.L_normalizes_V l.property⟩ av
  have hc : c = vv := by
    apply b.coordinates.injective
    apply Multiplicative.toAdd.injective
    have he := b.equivariant l av
    rw [hlr] at he
    exact he.trans hr
  have hcmem : (c : G) ∈ A :=
    (mem_normalizer_iff.mp (hLA l.property) a).mp a.property
  rwa [hc] at hcmem
end CFSG.Quasithin.ChapterG.Section02.Setup
