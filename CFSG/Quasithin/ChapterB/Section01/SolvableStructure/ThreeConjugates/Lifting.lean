module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.ImageData

/-!
# Lifting the distinct cyclic-three conjugates

The fixed-space action has a two-group kernel and is therefore injective on
K₀, a three-group. Consequently it preserves distinctness of all T-conjugates
of K. Mapping the actual Sylow subgroup gives a bijection of the conjugate
families, compatible with the literal conjugation maps. These are the lifting
maps used in the internal-product assembly of B.1.12.

Source: Aschbacher–Smith, B.1.12, printed p. 73 (PDF p. 84).
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ThreeConjugates

private theorem mapInside_conj {G D : Type*} [Group G] [Group D]
    (H : Subgroup G) (f : H →* D) (A : Subgroup G) (t : H) :
    ((A.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf H).map f =
      ((A.subgroupOf H).map f).map (MulAut.conj (f t)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨a, ⟨b, hb, he⟩, rfl⟩
    change (t : G) * b * (t : G)⁻¹ = (a : G) at he
    have hbH : b ∈ H := by
      have : (t : G)⁻¹ * (a : G) * t ∈ H := H.mul_mem (H.mul_mem (H.inv_mem t.property) a.property) t.property
      simpa only [← he, MulAut.conj_apply, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one] using this
    refine ⟨f ⟨b, hbH⟩, ⟨⟨b, hbH⟩, hb, rfl⟩, ?_⟩
    change f t * f ⟨b, hbH⟩ * (f t)⁻¹ = f a
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext he)
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨t * a * t⁻¹, ⟨a, ha, rfl⟩, ?_⟩
    change f (t * a * t⁻¹) = f t * f a * (f t)⁻¹
    simp only [map_mul, map_inv]

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The image of an ambient subgroup after restriction to H and action on U. -/
noncomputable def localImageOf (K T A : Subgroup G) :
    Subgroup (subspaceActionImage (localRepresentation ρ K T) (localFixedSpace ρ K T)) :=
  (A.subgroupOf (K ⊔ T)).map (localActionHom ρ K T)

/-- The action homomorphism is injective on the whole conjugate closure. -/
theorem closureAction_injective [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) :
    Function.Injective ((localActionHom ρ K T).comp
      (inclusion (conjugateClosure_le_sup K T))) := by
  let f := localActionHom ρ K T
  let N := (conjugateClosure K T).subgroupOf (K ⊔ T)
  have h2 : IsPGroup 2 f.ker := (localActionHom_ker ρ hf K T hK hcard hT).symm ▸ pCore_isPGroup
  have hd : Disjoint N f.ker := (conjugateClosure_isThreeGroup K T hK hcard).comap_subtype.disjoint_of_coprime
    h2 (by decide : Nat.Coprime 3 2)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  apply Subtype.ext
  have hm : inclusion (conjugateClosure_le_sup K T) a ∈ N ⊓ f.ker := ⟨a.property, ha⟩
  rw [hd.eq_bot] at hm
  have he : inclusion (conjugateClosure_le_sup K T) a = (1 : (K ⊔ T : Subgroup G)) := mem_bot.mp hm
  exact congrArg (fun x : (K ⊔ T : Subgroup G) => (x : G)) he

/-- Restricting the action to any subgroup of K₀ preserves subgroup equality. -/
theorem localImageOf_injective_below [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) {A B : Subgroup G}
    (hA : A ≤ conjugateClosure K T) (hB : B ≤ conjugateClosure K T)
    (he : localImageOf ρ K T A = localImageOf ρ K T B) : A = B := by
  have hi := closureAction_injective ρ hf K T hK hcard hT
  have hle {C D : Subgroup G} (hC : C ≤ conjugateClosure K T)
      (hD : D ≤ conjugateClosure K T)
      (h : localImageOf ρ K T C ≤ localImageOf ρ K T D) : C ≤ D := by
    intro x hx
    have hxH := (conjugateClosure_le_sup K T) (hC hx)
    obtain ⟨y, hy, he⟩ := h (mem_map_of_mem (localActionHom ρ K T)
      (show (⟨x, hxH⟩ : (K ⊔ T : Subgroup G)) ∈ C.subgroupOf (K ⊔ T) from hx))
    have he' : (y : G) = x := congrArg Subtype.val (hi (a₁ := ⟨y, hD hy⟩)
      (a₂ := ⟨x, hC hx⟩) he)
    exact he' ▸ hy
  exact le_antisymm (hle hA hB he.le) (hle hB hA he.ge)

omit [Finite G] in
/-- An original T-conjugate maps to the corresponding image-Sylow conjugate. -/
theorem localImageOf_conjugate (K : Subgroup G) (T : Sylow 2 G) (t : T) :
    localImageOf ρ K (T : Subgroup G) (K.map (MulAut.conj (t : G)).toMonoidHom) =
      (localImageThree ρ K (T : Subgroup G)).map
        (MulAut.conj (localActionHom ρ K (T : Subgroup G)
          (inclusion (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right) t))).toMonoidHom :=
  mapInside_conj (K ⊔ (T : Subgroup G)) (localActionHom ρ K (T : Subgroup G)) K
    (inclusion (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right) t)

/-- The distinct conjugates before and after the faithful odd-core map correspond. -/
noncomputable def conjugateImageEquiv [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (K : Subgroup G) (T : Sylow 2 G)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hcard : Nat.card K = 3) :
    conjugateFamily K (T : Subgroup G) ≃
      conjugateFamily (localImageThree ρ K (T : Subgroup G)) (localImageSylow ρ K T) := by
  let f := localActionHom ρ K (T : Subgroup G)
  have hm (c : conjugateFamily K (T : Subgroup G)) :
      localImageOf ρ K (T : Subgroup G) c ∈
        conjugateFamily (localImageThree ρ K (T : Subgroup G)) (localImageSylow ρ K T) := by
    obtain ⟨t, ht⟩ := c.property
    let tH := inclusion (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right) t
    refine ⟨⟨f tH, mem_map_of_mem f t.property⟩, ?_⟩
    change K.map (MulAut.conj (t : G)).toMonoidHom = (c : Subgroup G) at ht
    rw [← ht]
    exact (localImageOf_conjugate ρ K T t).symm
  refine Equiv.ofBijective (fun c => ⟨_, hm c⟩) ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    exact localImageOf_injective_below ρ hf K (T : Subgroup G) hK hcard T.isPGroup'
      (conjugate_le_closure _ _ a) (conjugate_le_closure _ _ b) (congrArg Subtype.val h)
  · rintro ⟨c, s, hs⟩
    obtain ⟨t, ht, he⟩ := s.property
    let tT : T := ⟨t, ht⟩
    refine ⟨⟨K.map (MulAut.conj (tT : G)).toMonoidHom, ⟨tT, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (localImageOf_conjugate ρ K T tT).trans (he ▸ hs)

@[simp] theorem conjugateImageEquiv_apply [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (K : Subgroup G) (T : Sylow 2 G)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hcard : Nat.card K = 3)
    (c : conjugateFamily K (T : Subgroup G)) :
    (conjugateImageEquiv ρ hf K T hK hcard c : Subgroup _) = localImageOf ρ K (T : Subgroup G) c := rfl

omit [Finite G] in
theorem localImageOf_map_conj (K T A : Subgroup G) (t : T) :
    localImageOf ρ K T (A.map (MulAut.conj (t : G)).toMonoidHom) =
      (localImageOf ρ K T A).map (MulAut.conj
        (localActionHom ρ K T (inclusion (show T ≤ K ⊔ T from le_sup_right) t))).toMonoidHom :=
  mapInside_conj (K ⊔ T) (localActionHom ρ K T) A
    (inclusion (show T ≤ K ⊔ T from le_sup_right) t)

omit [Finite G] in
theorem localImageOf_eq_range (K T A : Subgroup G) (hA : A ≤ K ⊔ T) :
    localImageOf ρ K T A = ((localActionHom ρ K T).comp (inclusion hA)).range := by
  rw [MonoidHom.range_comp, inclusion_range]
  rfl

omit [Finite G] in
theorem conjugateClosure_eq_iSup_family (K T : Subgroup G) :
    conjugateClosure K T = ⨆ c : conjugateFamily K T, (c : Subgroup G) := by
  apply le_antisymm
  · exact iSup_le fun t => le_iSup_of_le ⟨_, ⟨t, rfl⟩⟩ le_rfl
  · exact iSup_le (conjugate_le_closure K T)

omit [Finite G] in
/-- The indexing family is the actual transitive T-orbit. -/
theorem conjugateFamily_transitive (K T : Subgroup G) (c c' : conjugateFamily K T) :
    ∃ t : T, (c : Subgroup G).map (MulAut.conj (t : G)).toMonoidHom = (c' : Subgroup G) := by
  obtain ⟨a, ha⟩ := c.property
  obtain ⟨b, hb⟩ := c'.property
  refine ⟨b * a⁻¹, ?_⟩
  rw [← ha, ← hb, Subgroup.map_map]
  congr 1
  ext x
  change ((b : G) * (a : G)⁻¹) * ((a : G) * x * (a : G)⁻¹) *
    ((b : G) * (a : G)⁻¹)⁻¹ = (b : G) * x * (b : G)⁻¹
  group

end CFSG.Quasithin.ChapterB.ThreeConjugates
