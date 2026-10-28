module

public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Root normalizers in actual automorphism extensions

Extensions are literal preimages under Aut(M) → Out(M), with the actual
inner embedding retained. Normalizing the embedded root group is equivalent
to preserving its subgroup of M. Consequently a concrete calculation of the
root stabilizer restricts to every such preimage, without choosing a splitting.

Source: the outer-preimage convention of Aschbacher–Smith, Notation A.3.16,
printed p.51, and its Borel use in 13.6.6, printed p.927.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.AutomorphismExtensionBorel
variable {M : Type*} [Group M]

/-- The actual preimage, rather than a semidirect product with the outer group. -/
def outerPreimage (D : Subgroup (MulAut.Outer M)) : Subgroup (MulAut M) :=
  D.comap (QuotientGroup.mk' (MulAut.innerSubgroup M))

theorem inner_le_outerPreimage (D : Subgroup (MulAut.Outer M)) :
    MulAut.innerSubgroup M ≤ outerPreimage D := by
  intro a ha
  change QuotientGroup.mk a ∈ D
  rw [(QuotientGroup.eq_one_iff (N := MulAut.innerSubgroup M) a).mpr ha]
  exact D.one_mem

/-- The full preimage of an outer image recovers an overgroup of Inn(M).
This controls the entire extension, including its inner cosets. -/
theorem outerPreimage_map_eq (E : Subgroup (MulAut M))
    (hE : MulAut.innerSubgroup M ≤ E) :
    outerPreimage (E.map (QuotientGroup.mk' (MulAut.innerSubgroup M))) = E := by
  rw [outerPreimage, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hE]

/-- The mixed field–diagonal outer preimage lies in any overgroup of the
inner automorphisms containing both actual actors. This does not split it. -/
theorem mixed_outerPreimage_le (E : Subgroup (MulAut M))
    (hE : MulAut.innerSubgroup M ≤ E) (f d : MulAut M)
    (hf : f ∈ E) (hd : d ∈ E) :
    outerPreimage (zpowers (QuotientGroup.mk' (MulAut.innerSubgroup M) f *
      QuotientGroup.mk' (MulAut.innerSubgroup M) d)) ≤ E := by
  rw [← outerPreimage_map_eq E hE]
  apply Subgroup.comap_mono
  exact zpowers_le.mpr (Subgroup.mul_mem _ (mem_map_of_mem _ hf) (mem_map_of_mem _ hd))

/-- The component's original inner embedding into the specified extension. -/
def innerEmbedding (E : Subgroup (MulAut M))
    (hE : MulAut.innerSubgroup M ≤ E) : M →* E :=
  MulAut.conj.codRestrict E (fun x => hE ⟨x, rfl⟩)

theorem innerEmbedding_injective (E : Subgroup (MulAut M))
    (hE : MulAut.innerSubgroup M ≤ E)
    (hi : Function.Injective (MulAut.conj : M →* MulAut M)) :
    Function.Injective (innerEmbedding E hE) := by
  intro x y h
  exact hi (congrArg Subtype.val h)

/-- The root subgroup in the extension, with its literal inner embedding. -/
def rootIn (U : Subgroup M) (E : Subgroup (MulAut M)) : Subgroup E :=
  (U.map MulAut.conj).subgroupOf E

theorem rootIn_eq_map (U : Subgroup M) (E : Subgroup (MulAut M))
    (hE : MulAut.innerSubgroup M ≤ E) :
    rootIn U E = U.map (innerEmbedding E hE) := by
  ext a
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, Subtype.ext he⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The normalizer calculation reduces to a concrete actor calculation on M. -/
theorem mem_normalizer_rootIn_iff (U : Subgroup M) (E : Subgroup (MulAut M))
    (hE : MulAut.innerSubgroup M ≤ E)
    (hi : Function.Injective (MulAut.conj : M →* MulAut M)) (a : E) :
    a ∈ normalizer (rootIn U E : Set E) ↔ U.map a.val.toMonoidHom = U := by
  have hUE : U.map MulAut.conj ≤ E := (map_le_range _ _).trans hE
  rw [rootIn, ← subgroupOf_normalizer_eq hUE]
  change a.val ∈ normalizer (U.map MulAut.conj : Set (MulAut M)) ↔ _
  rw [mem_normalizer_iff_map_conj_eq]
  have he : (MulAut.conj a.val : MulAut M →* MulAut M).comp MulAut.conj =
      MulAut.conj.comp a.val.toMonoidHom := by
    ext x y
    simp
  rw [Subgroup.map_map, he, ← Subgroup.map_map]
  exact map_injective hi |>.eq_iff

/-- Restrict a concretely described actor Borel to the actual extension.
The input is the matrix/root stabilizer calculation, not a normalizer definition. -/
theorem normalizer_rootIn (U : Subgroup M) (E B : Subgroup (MulAut M))
    (hE : MulAut.innerSubgroup M ≤ E)
    (hi : Function.Injective (MulAut.conj : M →* MulAut M))
    (hB : ∀ a : E, U.map a.val.toMonoidHom = U ↔ a.val ∈ B) :
    normalizer (rootIn U E : Set E) = B.subgroupOf E := by
  ext a
  exact (mem_normalizer_rootIn_iff U E hE hi a).trans (hB a)

end Theory.GroupTheory.AutomorphismExtensionBorel
