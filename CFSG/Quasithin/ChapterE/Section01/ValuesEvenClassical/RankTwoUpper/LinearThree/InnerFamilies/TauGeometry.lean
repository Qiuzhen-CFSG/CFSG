module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.LocalPair
public import Theory.SpecificGroups.PSL3Even.TauGeometry.Pair
public import Theory.SpecificGroups.PSL3Even.TauGeometry.Actors
public import Theory.SpecificGroups.PSL3Even.TauGeometry.Fixers
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Local-pair action and large inner actors in an aligned PSL₃ extension

The actual conjugation action of the ambient group is transported through
`linearThreeEmbedding`. Sylow alignment forces it to stabilize the entire
standard unipotent subgroup, so every Sylow element fixes both actual locals
or exchanges them, including the graph and binary cases.

For a large elementary inner actor, UT₃ coordinates identify its full inner
centralizer with a root plane and show that it escapes the opposite local
core. Faithfulness of the simple generalized-Fitting subgroup and its trivial
two-core reduce the ambient tau assertion to `LargeActorFixersAreInner`:
a Sylow-preserving two-element fixing the large coordinate subgroup pointwise
must be inner. The proved semilinear calculation discharges this premise in
`large_actor_tau`, including the graph, field, and binary cases. Together with
`local_pair_action`, it supplies both geometric inputs of the inner-family
assembly. These two inputs require no further use of the SQTK hypothesis.

Source: Aschbacher–Smith, E.1.1–6 and E.1.14(1), printed pp.209–214,
and F.1.12(I)(1), printed pp.263–264 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies
variable {G F : Type*} [Group G] [Field F] [Finite F]

/-- The literal ambient conjugation action in the supplied socle coordinates. -/
noncomputable def modelAction (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F)) :
    G →* MulAut PSL(3,F) := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

omit [Finite F] in
theorem embedding_modelAction (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    (g : G) (x : PSL(3,F)) :
    linearThreeEmbedding L e (modelAction L e g x) =
      g * linearThreeEmbedding L e x * g⁻¹ := by
  change (e.symm (e (MulAut.conjNormal g (e.symm x))) : G) = _
  rw [e.symm_apply_apply]
  rfl

theorem modelAction_stabilizes_unipotent (L : Subgroup G) [L.Normal]
    (e : L ≃* PSL(3,F)) (T : Sylow 2 G) {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (g : G) (hg : g ∈ T) :
    (unipotent F).map (modelAction L e g).toMonoidHom = unipotent F := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    rw [← sylow_comap_eq L e T hf hF halign]
    change linearThreeEmbedding L e (modelAction L e g x) ∈ T
    rw [embedding_modelAction]
    exact T.mul_mem (T.mul_mem hg (halign (mem_map_of_mem _ hx))) (T.inv_mem hg)
  · rw [Subgroup.card_map_of_injective (modelAction L e g).injective]

omit [Finite F] in
theorem localImage_map_conj (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    (g : G) (b : Bool) :
    (localImage L e b).map (MulAut.conj g).toMonoidHom =
      ((localModel F b).map (modelAction L e g).toMonoidHom).map
        (linearThreeEmbedding L e) := by
  rw [localImage, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  exact (embedding_modelAction L e g x).symm

/-- Every element of the aligned ambient Sylow fixes both literal locals or
exchanges them. Normality of the model subgroup suffices for this premise. -/
theorem local_pair_action (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    (T : Sylow 2 G) {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G)) :
    ∀ g ∈ (T : Subgroup G),
      (∀ b, (localImage L e b).map (MulAut.conj g).toMonoidHom = localImage L e b) ∨
      (∀ b, (localImage L e b).map (MulAut.conj g).toMonoidHom = localImage L e (!b)) := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, Nat.ne_of_gt hf])
  let : CharP F 2 := ringChar.of_eq hc
  intro g hg
  have h := Matrix.PSL3Even.TauGeometry.local_pair_of_unipotent_stable F hf hF
    (modelAction L e g) (modelAction_stabilizes_unipotent L e T hf hF halign g hg)
  rcases h with h | h
  · left
    intro b
    rw [localImage_map_conj]
    exact congrArg (fun P : Subgroup PSL(3,F) => P.map (linearThreeEmbedding L e)) (h b)
  · right
    intro b
    rw [localImage_map_conj]
    exact congrArg (fun P : Subgroup PSL(3,F) => P.map (linearThreeEmbedding L e)) (h b)

omit [Finite F] in
theorem coreImage_eq_map (L : Subgroup G) (e : L ≃* PSL(3,F)) (b : Bool) :
    coreImage L e b = ((pCore 2 (localModel F b)).map (localModel F b).subtype).map
      (linearThreeEmbedding L e) := by
  let E : localModel F b ≃* localImage L e b :=
    (localModel F b).equivMapOfInjective (linearThreeEmbedding L e) (embedding_injective L e)
  rw [coreImage, ← pCore_map_iso 2 E, Subgroup.map_map, Subgroup.map_map]
  rfl

/-- Alignment also places every inner actor in the literal embedded UT₃ group. -/
theorem inner_actor_le_unipotent (L : Subgroup G) (e : L ≃* PSL(3,F))
    (T : Sylow 2 G) {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) (hAL : A ≤ L) :
    A ≤ (unipotent F).map (linearThreeEmbedding L e) := by
  intro a ha
  have haL := hAL ha
  rw [← linearThreeEmbedding_range L e] at haL
  obtain ⟨x,rfl⟩ := haL
  refine mem_map_of_mem _ ?_
  rw [← sylow_comap_eq L e T hf hF halign]
  exact hAT ha

omit [Finite F] in
open scoped commutatorElement in
/-- With trivial ambient two-core, source tau is the literal relative centralizer. -/
theorem tau_eq_inf_centralizer (hcore : pCore 2 G = ⊥) (T A : Subgroup G) :
    tau T A = T ⊓ centralizer (A : Set G) := by
  ext x
  rw [tau, mem_centralizerModulo_iff, mem_inf, mem_centralizer_iff]
  simp only [hcore, mem_bot, commutatorElement_eq_one_iff_mul_comm]
  rfl

open Matrix.PSL3Even.UnipotentGeometry in
/-- The complete inner calculation: once tau is inner, the opposite local
contains tau and its actual two-core does not contain the large actor. -/
theorem large_actor_of_tau_le_socle [CharP F 2] [Finite G]
    (L : Subgroup G) (e : L ≃* PSL(3,F)) (T : Sylow 2 G)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (hcore : pCore 2 G = ⊥)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hAL : A ≤ L) (hr : f < Group.rank A)
    (htau : tau (T : Subgroup G) A ≤ L) :
    ∃ b : Bool, tau (T : Subgroup G) A ≤ localImage L e b ∧ ¬ A ≤ coreImage L e b := by
  let := hA
  let j := (linearThreeEmbedding L e).comp (projective F)
  have hj : Function.Injective j := (embedding_injective L e).comp (projective_injective F)
  let B := A.comap j
  have hB : B.map j = A := by
    apply map_comap_eq_self
    have hh := inner_actor_le_unipotent L e T hf hF halign A hAT hAL
    simpa only [j, MonoidHom.range_comp, projective_range] using hh
  have hBm : (B.map (projective F)).map (linearThreeEmbedding L e) = A := by
    rw [Subgroup.map_map]
    exact hB
  have hc : Nat.card F < Nat.card B := by
    have hh : Nat.card A = Nat.card B := by rw [← hB, card_map_of_injective hj]
    rw [← hh, hF]
    exact lt_of_not_ge (fun h => (not_le_of_gt hr)
      (IsElementaryAbelian.rank_le_of_card_le A h))
  have he : ∀ a ∈ B, a^2 = 1 := by
    intro a ha
    apply hj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (j a) ha
  obtain ⟨b,hcent,hne⟩ := Matrix.PSL3Even.TauGeometry.large_actor_opposite_local F B he hc
  refine ⟨b, ?_, ?_⟩
  · intro g hg
    have hgL := htau hg
    rw [← linearThreeEmbedding_range L e] at hgL
    obtain ⟨x,rfl⟩ := hgL
    apply mem_map_of_mem
    apply hcent
    intro y hy
    apply embedding_injective L e
    rw [map_mul, map_mul]
    have hgy : linearThreeEmbedding L e y ∈ A := hBm ▸ mem_map_of_mem _ hy
    rw [tau_eq_inf_centralizer hcore] at hg
    exact hg.2 _ hgy
  · intro h
    apply hne
    rw [coreImage_eq_map, ← hBm] at h
    exact (map_le_map_iff_of_injective (embedding_injective L e)).mp h

omit [Finite F] in
theorem modelAction_injective (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    (hC : centralizer (L : Set G) = ⊥) : Function.Injective (modelAction L e) := by
  exact (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L hC)

omit [Finite F] in
theorem modelAction_embedding (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    (z : PSL(3,F)) : modelAction L e (linearThreeEmbedding L e z) = MulAut.conj z := by
  ext x
  apply embedding_injective L e
  rw [embedding_modelAction]
  change _ = linearThreeEmbedding L e (z*x*z⁻¹)
  rw [map_mul, map_mul, map_inv]

open Matrix.PSL3Even.UnipotentGeometry in
/-- Faithful ambient conjugation turns the intrinsic pointwise-fixer
calculation into the missing tau containment in the socle. -/
theorem tau_le_socle_of_large_fixers [Finite G]
    (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F)) (T : Sylow 2 G)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (hC : centralizer (L : Set G) = ⊥) (hcore : pCore 2 G = ⊥)
    (hfixers : Matrix.PSL3Even.TauGeometry.LargeActorFixersAreInner F)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hAL : A ≤ L) (hr : f < Group.rank A) :
    tau (T : Subgroup G) A ≤ L := by
  let := hA
  let j := (linearThreeEmbedding L e).comp (projective F)
  have hj : Function.Injective j := (embedding_injective L e).comp (projective_injective F)
  let B := A.comap j
  have hB : B.map j = A := by
    apply map_comap_eq_self
    have hh := inner_actor_le_unipotent L e T hf hF halign A hAT hAL
    simpa only [j, MonoidHom.range_comp, projective_range] using hh
  have hc : Nat.card F < Nat.card B := by
    have hh : Nat.card A = Nat.card B := by rw [← hB, card_map_of_injective hj]
    rw [← hh, hF]
    exact lt_of_not_ge (fun h => (not_le_of_gt hr)
      (IsElementaryAbelian.rank_le_of_card_le A h))
  have he : ∀ a ∈ B, a^2 = 1 := by
    intro a ha
    apply hj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (j a) ha
  intro g hg
  have hgT := tau_le (T : Subgroup G) A hg
  have hin : modelAction L e g ∈ MulAut.innerSubgroup PSL(3,F) := by
    apply hfixers B he hc (modelAction L e g)
      (modelAction_stabilizes_unipotent L e T hf hF halign g hgT)
    · obtain ⟨k,hk⟩ := T.isPGroup'.exists_pow_pow_eq_one (⟨g,hgT⟩ : T)
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have hgk : g^(2^k) = 1 := congrArg Subtype.val hk
      rw [hgk, map_one]
    · intro a ha
      apply embedding_injective L e
      rw [embedding_modelAction]
      have hh := (tau_eq_inf_centralizer hcore (T : Subgroup G) A) ▸ hg
      have comm := hh.2 (j a) ha
      change g * j a * g⁻¹ = j a
      rw [← comm, mul_inv_cancel_right]
  obtain ⟨z,hz⟩ := hin
  have hgval : g = linearThreeEmbedding L e z :=
    modelAction_injective L e hC (hz.symm.trans (modelAction_embedding L e z).symm)
  rw [hgval]
  exact (e.symm z).property

/-- The exact large-actor premise for the source socle. The sole remaining
input is the independently stated semilinear pointwise-fixer calculation. -/
theorem large_actor_tau_of_large_fixers [Finite G]
    [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding (generalizedFitting G) e) ≤
      (T : Subgroup G))
    (hfixers : Matrix.PSL3Even.TauGeometry.LargeActorFixersAreInner F) :
    ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
      A ≤ generalizedFitting G → f < Group.rank A → ∃ b : Bool,
        tau (T : Subgroup G) A ≤ localImage (generalizedFitting G) e b ∧
          ¬ A ≤ coreImage (generalizedFitting G) e b := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, Nat.ne_of_gt hf])
  let : CharP F 2 := ringChar.of_eq hc
  let : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  let : Group.IsPerfect (generalizedFitting G) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hs := SimpleSocle.structure_of_sylow_supplement
    (Group.IsPerfect.not_isMulCommutative (generalizedFitting G)) T hgen
  intro A hA hAT hAL hr
  exact large_actor_of_tau_le_socle (generalizedFitting G) e T hf hF halign hs.2.2.1
    A hA hAT hAL hr
    (tau_le_socle_of_large_fixers (generalizedFitting G) e T hf hF halign hs.1 hs.2.2.1
      hfixers A hA hAT hAL hr)

/-- The large-inner-actor geometric premise of the E.1.14(1) assembly,
with the semilinear pointwise-fixer calculation discharged. The selected
literal local contains source tau, while its intrinsic two-core misses A. -/
theorem large_actor_tau [Finite G]
    [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding (generalizedFitting G) e) ≤
      (T : Subgroup G)) :
    ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
      A ≤ generalizedFitting G → f < Group.rank A → ∃ b : Bool,
        tau (T : Subgroup G) A ≤ localImage (generalizedFitting G) e b ∧
          ¬ A ≤ coreImage (generalizedFitting G) e b := by
  exact large_actor_tau_of_large_fixers e T hgen hf hF halign
    (Matrix.PSL3Even.TauGeometry.largeActorFixersAreInner F hf hF)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies
