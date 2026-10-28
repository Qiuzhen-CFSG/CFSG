module

public import Theory.Representation.AbelianAllWeights
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Data.Fintype.EquivFin

/-!
# Normalizers acting on abelian character weights

The normalizer sends a simultaneous character space to the space for the
character pulled back by inverse conjugation. This yields an action of the
induced automizer on the occurring characters. Since these spaces span a
cross-characteristic abelian representation, the characters separate elements
whenever the representation is faithful. Thus the action is faithful and the
normalizer action has kernel exactly the centralizer.

The dimension bound on the number of weights then embeds the automizer into
the symmetric group of that degree. No assumption on invariants or on the
trivial character is made. This is the abelian argument in Aschbacher–Smith,
Lemma A.3.21(c), printed pp. 55–56.
-/

public section

namespace Representation

variable {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]

private theorem weight_conjugate_nonzero (rho : Representation E G V) (Q : Subgroup G)
    (g : (Subgroup.normalizer (Q : Set G))) (chi : Q →* Eˣ)
    (hchi : characterWeightSpace (rho.comp Q.subtype) chi ≠ ⊥) :
    characterWeightSpace (rho.comp Q.subtype)
      (chi.comp (Q.normalizerMonoidHom g).symm.toMonoidHom) ≠ ⊥ := by
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hchi
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨rho g v, ?_, ?_⟩
  · simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hv ⊢
    intro k
    have hc : (k : G) * g = g * ((Q.normalizerMonoidHom g).symm k : Q) := by
      have h := congrArg (fun z : Q => (z : G))
        ((Q.normalizerMonoidHom g).apply_symm_apply k)
      change (g : G) * ((Q.normalizerMonoidHom g).symm k : Q) * (g : G)⁻¹ = k at h
      rw [← h]
      group
    change rho (k : G) (rho g v) = (chi ((Q.normalizerMonoidHom g).symm k) : E) • rho g v
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    rw [show rho (((Q.normalizerMonoidHom g).symm k : Q) : G) v =
      (chi ((Q.normalizerMonoidHom g).symm k) : E) • v from hv ((Q.normalizerMonoidHom g).symm k)]
    exact map_smul _ _ _
  · intro hz
    have he := congrArg (rho (g : G)⁻¹) hz
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at he
    exact hn he

/-- The induced automizer permutes the nonzero character spaces by inverse pullback. -/
@[expose] noncomputable def automizerWeightPerm (rho : Representation E G V) (Q : Subgroup G) :
    Q.normalizerMonoidHom.range →* Equiv.Perm (CharacterWeight (rho.comp Q.subtype)) := by
  let mapWeight (a : Q.normalizerMonoidHom.range)
      (chi : (CharacterWeight (rho.comp Q.subtype))) : (CharacterWeight (rho.comp Q.subtype)) :=
    ⟨chi.val.comp a.val.symm.toMonoidHom, by
      obtain ⟨g, hg⟩ := a.property
      rw [← hg]
      exact weight_conjugate_nonzero rho Q g chi.val chi.property⟩
  exact {
    toFun := fun a => {
      toFun := mapWeight a
      invFun := mapWeight a⁻¹
      left_inv := by
        intro chi
        apply Subtype.ext
        apply MonoidHom.ext
        intro k
        change chi.val (a.val.symm (a.val k)) = chi.val k
        rw [MulEquiv.symm_apply_apply]
      right_inv := by
        intro chi
        apply Subtype.ext
        apply MonoidHom.ext
        intro k
        change chi.val (a.val (a.val.symm k)) = chi.val k
        rw [MulEquiv.apply_symm_apply] }
    map_one' := by
      ext chi k
      rfl
    map_mul' := by
      intro a b
      ext chi k
      rfl }

/-- Pullback on an occurring character is the inverse induced automorphism. -/
theorem automizerWeightPerm_apply (rho : Representation E G V) (Q : Subgroup G)
    (a : Q.normalizerMonoidHom.range) (chi : (CharacterWeight (rho.comp Q.subtype))) (k : Q) :
    (automizerWeightPerm rho Q a chi).val k = chi.val (a.val.symm k) := rfl

variable [FiniteDimensional E V] [IsAlgClosed E]

/-- Occurring characters separate elements in a faithful abelian representation. -/
theorem eq_of_characterWeight_values {K : Type*} [Group K] [IsMulCommutative K]
    (sigma : Representation E K V) (hsigma : Function.Injective sigma)
    (horder : (Nat.card K : E) ≠ 0) (a b : K)
    (hab : ∀ chi : sigma.CharacterWeight, chi.val a = chi.val b) : a = b := by
  apply hsigma
  apply LinearMap.eqLocus_eq_top.mp
  apply top_unique
  rw [← sigma.iSup_characterWeightSpace_eq_top horder]
  refine iSup_le fun chi v hv => ?_
  simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hv
  change sigma a v = sigma b v
  rw [hv a, hv b, hab chi]

/-- A faithful abelian representation makes the automizer action on weights faithful. -/
theorem automizerWeightPerm_injective (rho : Representation E G V) (Q : Subgroup G)
    [IsMulCommutative Q] (hrho : Function.Injective rho)
    (horder : (Nat.card Q : E) ≠ 0) : Function.Injective (automizerWeightPerm rho Q) := by
  intro a b hab
  apply Subtype.ext
  suffices a.val.symm = b.val.symm by
    simpa using congrArg MulEquiv.symm this
  apply MulEquiv.ext
  intro k
  apply eq_of_characterWeight_values (rho.comp Q.subtype)
    (hrho.comp Subtype.val_injective) horder
  intro chi
  exact congrArg (fun p : Equiv.Perm (CharacterWeight (rho.comp Q.subtype)) => (p chi).val k) hab

/-- The weight action of the normalizer has precisely the centralizer as kernel. -/
theorem normalizerWeightPerm_ker (rho : Representation E G V) (Q : Subgroup G)
    [IsMulCommutative Q] (hrho : Function.Injective rho)
    (horder : (Nat.card Q : E) ≠ 0) :
    ((automizerWeightPerm rho Q).comp Q.normalizerMonoidHom.rangeRestrict).ker =
      (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)) := by
  rw [← Q.normalizerMonoidHom_ker]
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  rw [← (automizerWeightPerm rho Q).map_one,
    (automizerWeightPerm_injective rho Q hrho horder).eq_iff]
  exact Subtype.val_inj.symm

/-- The automizer of an abelian subgroup embeds in a symmetric group of the
representation's degree (or any larger degree). -/
theorem automizer_embeds_perm_of_abelian (rho : Representation E G V) (Q : Subgroup G)
    [IsMulCommutative Q] (hrho : Function.Injective rho)
    (horder : (Nat.card Q : E) ≠ 0) (n : ℕ) (hdim : Module.finrank E V ≤ n) :
    ∃ j : Q.normalizerMonoidHom.range →* Equiv.Perm (Fin n), Function.Injective j := by
  classical
  obtain ⟨hfinite, hcard⟩ := characterWeight_card_le (rho.comp Q.subtype) horder
  let := hfinite
  let := Fintype.ofFinite (CharacterWeight (rho.comp Q.subtype))
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := (CharacterWeight (rho.comp Q.subtype)))
    (β := Fin n) (by simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hcard.trans hdim)
  exact ⟨(Equiv.Perm.viaEmbeddingHom e).comp (automizerWeightPerm rho Q),
    (Equiv.Perm.viaEmbeddingHom_injective e).comp (automizerWeightPerm_injective rho Q hrho horder)⟩

end Representation
