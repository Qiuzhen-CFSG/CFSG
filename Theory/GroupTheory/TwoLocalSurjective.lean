module

public import Theory.Quasithin
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# Lifting two-local subgroups through surjections

Every two-local subgroup of a homomorphic image of a finite group is the
image of a two-local subgroup. If the target subgroup is the normalizer of
a nontrivial two-subgroup `Q`, choose a Sylow two-subgroup of the inverse
image of `Q`. Its ambient image `U` maps onto `Q`, so is nontrivial.
The Frattini argument in the inverse image of the normalizer of `Q` shows
that the normalizer of `U` maps onto that normalizer: the extra factor `Q`
already lies in the image of `U`, hence in the image of its normalizer.

This is the two-local lifting input in Aschbacher–Smith, *The Classification
of Quasithin Groups*, Lemma A.2.7, printed p.34 (`refs/quasithin.pdf`).
No rank or classification hypotheses are required.
-/

open Subgroup

variable {G H : Type*} [Group G] [Finite G] [Group H]

private theorem sylow_lift_images {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f)
    (Q : Subgroup H) (hQ : IsPGroup p Q) (P : Sylow p (Q.comap f)) :
    let U := (P : Subgroup (Q.comap f)).map (Q.comap f).subtype
    U.map f = Q ∧ (normalizer (U : Set G)).map f = normalizer (Q : Set H) := by
  let K := Q.comap f
  let U := (P : Subgroup K).map K.subtype
  have hPmap : (P : Subgroup K).map (f.subgroupComap Q) = ⊤ := by
    let R := P.mapSurjective (f.subgroupComap_surjective_of_surjective Q hf)
    exact (R.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  have hmap : U.map f = Q := by
    have he : Q.subtype.comp (f.subgroupComap Q) = f.comp K.subtype := rfl
    rw [show U = (P : Subgroup K).map K.subtype from rfl, map_map,
      ← he, ← map_map, hPmap, ← MonoidHom.range_eq_map, range_subtype]
  refine ⟨hmap, le_antisymm ?_ ?_⟩
  · simpa only [hmap] using U.le_normalizer_map f
  · have hfr := le_normalizer_sylow_sup K ((normalizer (Q : Set H)).comap f)
      (comap_mono Q.le_normalizer) (Q.le_normalizer_comap f) P
    have hm := map_mono (f := f) hfr
    rw [Subgroup.map_sup, map_comap_eq_self_of_surjective hf,
      map_comap_eq_self_of_surjective hf] at hm
    apply hm.trans
    apply sup_le le_rfl
    rw [← hmap]
    exact map_mono U.le_normalizer

/-- A two-local subgroup lifts to a two-local subgroup through a surjective
homomorphism of finite groups. Finiteness of the codomain follows from surjectivity. -/
public theorem IsTwoLocal.exists_map_eq_of_surjective
    (f : G →* H) (hf : Function.Surjective f)
    {M : Subgroup H} (hM : IsTwoLocal M) :
    ∃ L : Subgroup G, IsTwoLocal L ∧ L.map f = M := by
  obtain ⟨Q, hQne, hQ, rfl⟩ := hM
  let P : Sylow 2 (Q.comap f) := Sylow.nonempty.some
  let U := (P : Subgroup (Q.comap f)).map (Q.comap f).subtype
  obtain ⟨hmap, hnmap⟩ := sylow_lift_images f hf Q hQ P
  have hUne : U ≠ ⊥ := by
    intro hU
    apply hQne
    rw [← hmap]
    change U.map f = ⊥
    rw [hU, Subgroup.map_bot]
  exact ⟨normalizer (U : Set G),
    ⟨U, hUne, P.isPGroup'.map (Q.comap f).subtype, rfl⟩, hnmap⟩

/-- A two-local lift together with the induced surjective homomorphism.
The homomorphism agrees with the original map on the lifted subgroup. -/
public theorem IsTwoLocal.exists_surjective_of_surjective
    (f : G →* H) (hf : Function.Surjective f)
    {M : Subgroup H} (hM : IsTwoLocal M) :
    ∃ L : Subgroup G, IsTwoLocal L ∧ L.map f = M ∧
      ∃ φ : L →* M, Function.Surjective φ ∧ ∀ x : L, (φ x : H) = f x := by
  obtain ⟨L, hL, hmap⟩ := hM.exists_map_eq_of_surjective f hf
  let φ : L →* M := (f.comp L.subtype).codRestrict M (fun x => by
    change f x ∈ M
    rw [← hmap]
    exact mem_map_of_mem f x.property)
  refine ⟨L, hL, hmap, φ, ?_, fun _ => rfl⟩
  intro y
  have hy : (y : H) ∈ L.map f := hmap.symm ▸ y.property
  obtain ⟨x, hx, hxy⟩ := mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
