module
public import Theory.Representation.NormalElementaryQuotient

/-!
# Comparing the original action with its subgroup restriction

The centralizer quotient on an embedded normal elementary subgroup restricts
to the given faithful subgroup action. The comparison retains the quotient
maps and conjugation coordinates, as needed in C.2.7 and14.6.10(5).
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction.Join
variable {A B D S : Type*} [Group A] [Group B] [Group D] [Group S]
variable (i : A →* B) (hi : Function.Injective i) (U : Subgroup A)
variable (q : A →* S) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set A))
variable (Q : B →* D) (hQk : Q.ker = centralizer (U.map i : Set B))

include hi hk hQk in
theorem restricted_kernel : (Q.comp i).ker = q.ker := by
  rw [hk]
  ext a
  change Q (i a) = 1 ↔ a ∈ centralizer (U : Set A)
  change i a ∈ Q.ker ↔ _
  rw [hQk]
  constructor
  · intro ha u hu
    apply hi
    simpa only [map_mul] using ha (i u) (mem_map_of_mem i hu)
  · intro ha v hv
    obtain ⟨u,hu,rfl⟩ := hv
    simpa only [map_mul] using congrArg i (ha u hu)

noncomputable def actorMap : S →* D :=
  q.liftOfSurjective hq ⟨Q.comp i,(restricted_kernel i hi U q hk Q hQk).ge⟩

theorem actorMap_apply (a : A) : actorMap i hi U q hq hk Q hQk (q a) = Q (i a) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem actorMap_injective : Function.Injective (actorMap i hi U q hq hk Q hQk) := by
  apply (actorMap i hi U q hq hk Q hQk).ker_eq_bot_iff.mp
  apply bot_unique
  intro s hs
  obtain ⟨a,rfl⟩ := hq s
  change actorMap i hi U q hq hk Q hQk (q a) = 1 at hs
  rw [actorMap_apply] at hs
  have ha : a ∈ (Q.comp i).ker := hs
  rw [restricted_kernel i hi U q hk Q hQk] at ha
  exact ha

theorem actorMap_image (L : Subgroup A) :
    (L.map q).map (actorMap i hi U q hq hk Q hQk) = (L.map i).map Q := by
  rw [map_map,map_map]
  congr 1
  exact MonoidHom.ext (actorMap_apply i hi U q hq hk Q hQk)

variable [U.Normal] [IsElementaryAbelian 2 U]
  [(U.map i).Normal] [IsElementaryAbelian 2 (U.map i)]

noncomputable def embeddedLinearEquiv : Additive U ≃ₗ[ZMod 2] Additive (U.map i) :=
  (U.equivMapOfInjective i hi).toAdditive.toLinearEquiv
    (fun c v => map_smul
      ((U.equivMapOfInjective i hi).toMonoidHom.toAdditive.toZModLinearMap 2) c v)

theorem embedded_intertwines (hQ : Function.Surjective Q) (s : S) (v : Additive U) :
    embeddedLinearEquiv i hi U (NormalElementaryQuotient.representation U q hq hk s v) =
      NormalElementaryQuotient.representation (U.map i) Q hQ hQk
        (actorMap i hi U q hq hk Q hQk s) (embeddedLinearEquiv i hi U v) := by
  obtain ⟨a,rfl⟩ := hq s
  rw [actorMap_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change i ((NormalElementaryQuotient.representation U q hq hk (q a) v).toMul : A) = _
  rw [NormalElementaryQuotient.representation_apply,
    NormalElementaryQuotient.representation_apply,map_mul,map_mul,map_inv]
  rfl

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction.Join
