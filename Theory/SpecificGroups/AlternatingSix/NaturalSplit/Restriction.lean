module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Basic
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Restricting automorphisms of the natural split A₆ block

The translation subgroup is the two-core, hence characteristic. Restriction
therefore maps every automorphism into the normalizer of the actual natural
A₆ image. Coordinate permutations lift to automorphisms preserving the chosen
complement. Once the natural-image normalizer is identified with S₆, every
automorphism is a cocycle translation followed by such a lift.

Source: Aschbacher–Smith 14.3.19(10), the split-extension automorphism argument.
-/

@[expose] public section
namespace BinaryPermutation.SixNaturalSplit
open Subgroup SemidirectProduct
noncomputable instance : Finite Model := Finite.of_equiv (Vector × Actor) SemidirectProduct.equivProd.symm
noncomputable def translations : Subgroup Model := (inl : Vector →* Model).range
noncomputable def translationEquiv : Vector ≃* translations := MonoidHom.ofInjective inl_injective

private theorem actor_twoCore : pCore 2 Actor=⊥ := by
  let : IsSimpleGroup Actor := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (pCore 2 Actor).Normal).eq_bot_or_eq_top with h|h
  · exact h
  · have hp : IsPGroup 2 (⊤ : Subgroup Actor) := h ▸ pCore_isPGroup
    have hp' : IsPGroup 2 Actor := hp.of_equiv Subgroup.topEquiv
    obtain ⟨n,hn⟩ := hp'.exists_card_eq
    have hcop : Nat.Coprime (2^n) 3 := (by decide : Nat.Coprime 2 3).pow_left n
    rw [← hn,nat_card_alternatingGroup] at hcop
    norm_num [Nat.factorial] at hcop

public theorem translations_eq_twoCore : translations=pCore 2 Model := by
  have hpV : IsPGroup 2 Vector := IsPGroup.of_card (n := 4) (by
    change Nat.card (natural (Fin 6))=2^4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_natural_even _ (by decide)]
    rfl)
  have hpA : IsPGroup 2 translations := hpV.of_equiv translationEquiv
  have he : translations=(rightHom : Model →* Actor).ker := range_inl_eq_ker_rightHom
  have hpker : IsPGroup 2 (rightHom : Model →* Actor).ker := he ▸ hpA
  have h := (rightHom : Model →* Actor).comap_pCore_of_ker_isPGroup rightHom_surjective hpker
  rw [actor_twoCore] at h
  change (rightHom : Model →* Actor).ker=pCore 2 Model at h
  exact he.trans h

instance translations_characteristic : translations.Characteristic := by
  rw [translations_eq_twoCore]
  infer_instance

noncomputable def restriction : MulAut Model →* MulAut Vector :=
  (MulAut.congr translationEquiv.symm).toMonoidHom.comp (MulAut.characteristic translations)

public theorem restriction_apply (a : MulAut Model) (v : Vector) :
    (inl (restriction a v) : Model)=a (inl v) := by
  exact congrArg Subtype.val (translationEquiv.apply_symm_apply
    ((MulAut.characteristic translations a) (translationEquiv v)))

public theorem restriction_ker : restriction.ker=pointwiseKernel := by
  ext a
  change restriction a=1 ↔ ∀ v : Vector, a (inl v)=inl v
  constructor
  · intro ha v
    rw [← restriction_apply,ha]
    rfl
  · intro ha
    apply MulEquiv.ext
    intro v
    apply inl_injective (φ := action)
    exact (restriction_apply a v).trans (ha v)

public theorem restriction_intertwines (a : MulAut Model) (g : Actor) (v : Vector) :
    restriction a (action g v) = action (a (inr g)).right (restriction a v) := by
  apply inl_injective (φ := action)
  rw [restriction_apply,inl_aut,map_mul,map_mul,map_inv,← restriction_apply]
  simpa only [map_inv] using Representation.OneCohomology.split_conjugate_inl action (a (inr g)) (restriction a v)

public theorem restriction_conjugates (a : MulAut Model) (g : Actor) :
    restriction a * action g * (restriction a)⁻¹ = action (a (inr g)).right := by
  apply MulEquiv.ext
  intro v
  change restriction a (action g ((restriction a).symm v)) = _
  rw [restriction_intertwines,MulEquiv.apply_symm_apply]

public theorem restriction_mem_normalizer (a : MulAut Model) :
    restriction a ∈ normalizer (action.range : Set (MulAut Vector)) := by
  rw [mem_normalizer_iff]
  intro f
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨(a (inr g)).right, (restriction_conjugates a g).symm⟩
  · intro hf
    have hi : restriction a⁻¹ * (restriction a*f*(restriction a)⁻¹) * (restriction a⁻¹)⁻¹=f := by
      rw [map_inv]
      group
    obtain ⟨g,hg⟩ := hf
    refine ⟨(a⁻¹ (inr g)).right,?_⟩
    rw [← restriction_conjugates, hg,hi]

noncomputable def diagonalAut (s : Equiv.Perm (Fin 6)) : MulAut Model :=
  SemidirectProduct.congr (naturalMulAction (Fin 6) s) (MulAut.conjNormal s) (by
    intro g
    apply MulEquiv.ext
    intro v
    have he : action (MulAut.conjNormal s g) * naturalMulAction (Fin 6) s =
        naturalMulAction (Fin 6) s * action g := by
      change naturalMulAction (Fin 6) (s*g.val*s⁻¹) * naturalMulAction (Fin 6) s =
        naturalMulAction (Fin 6) s * naturalMulAction (Fin 6) g.val
      rw [← map_mul,← map_mul]
      congr 1
      group
    exact (MulEquiv.congr_fun he v).symm)

noncomputable def diagonal : Equiv.Perm (Fin 6) →* MulAut Model where
  toFun := diagonalAut
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply SemidirectProduct.ext
    · change naturalMulAction (Fin 6) 1 x.left=x.left
      rw [map_one]
      rfl
    · change MulAut.conjNormal 1 x.right=x.right
      rw [map_one]
      rfl
  map_mul' s t := by
    apply MulEquiv.ext
    intro x
    apply SemidirectProduct.ext
    · exact MulEquiv.congr_fun ((naturalMulAction (Fin 6)).map_mul s t) x.left
    · exact MulEquiv.congr_fun (MulAut.conjNormal.map_mul s t) x.right

public theorem restriction_diagonal (s : Equiv.Perm (Fin 6)) :
    restriction (diagonal s)=naturalMulAction (Fin 6) s := by
  apply MulEquiv.ext
  intro v
  exact congrArg SemidirectProduct.left (restriction_apply (diagonal s) v)

public theorem diagonal_injective : Function.Injective diagonal := by
  intro s t h
  apply symmetric_action_injective
  simpa only [restriction_diagonal] using congrArg restriction h

public theorem exists_kernel_mul_diagonal
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range)
    (a : MulAut Model) : ∃ k : pointwiseKernel, ∃ s : Equiv.Perm (Fin 6), a=k.val*diagonal s := by
  have ha := restriction_mem_normalizer a
  rw [hN] at ha
  obtain ⟨s,hs⟩ := ha
  have hk : a*(diagonal s)⁻¹ ∈ pointwiseKernel := by
    rw [← restriction_ker]
    change restriction (a*(diagonal s)⁻¹)=1
    rw [map_mul,map_inv,restriction_diagonal,← hs,mul_inv_cancel]
  exact ⟨⟨a*(diagonal s)⁻¹,hk⟩,s,by simp⟩

end BinaryPermutation.SixNaturalSplit
