module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.LocalPair
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.AmbientLocalCores
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Ambient local cores and binary tau containment

Conjugation on the simple generalized Fitting subgroup is faithful. Transport
through the supplied PSL₃ equivalence intertwines the original model embedding
with the inner-automorphism map. Normalization of a selected local restricts the
relevant actors to the diagram kernel, even if the full ambient Sylow contains
graph automorphisms. Injective transport of intrinsic two-cores proves the
ambient join identity. In the binary case every normalizing two-group lies in
the local itself, giving the tau containment required by the E1 assembly.

The final two theorems discharge the model premises of the tau-member owner;
they need neither the source SQTK hypothesis nor the large-actor rank bound.
Source: Aschbacher–Smith E.1.1–6 and E.1.14(1), printed pp.209–214, and
F.1.12, printed pp.263–264 (1 March 2004 manuscript).
-/

public section

open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.AmbientCores
open Matrix.PSL3.LinearThree.OuterExtensions
variable {G F : Type*} [Group G] [Field F]

private noncomputable def action (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F)) :
    G →* MulAut PSL(3,F) := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

private theorem embedding_action (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    (g : G) (x : PSL(3,F)) :
    linearThreeEmbedding L e (action L e g x) =
      g * linearThreeEmbedding L e x * g⁻¹ := by
  change (e.symm (e (MulAut.conjNormal g (e.symm x))) : G) = _
  rw [e.symm_apply_apply]
  rfl

private theorem action_embedding (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    (x : PSL(3,F)) : action L e (linearThreeEmbedding L e x) = MulAut.conj x := by
  ext y
  apply embedding_injective L e
  rw [embedding_action]
  change _ = linearThreeEmbedding L e (x*y*x⁻¹)
  rw [map_mul, map_mul, map_inv]

private theorem action_injective (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    (hC : centralizer (L : Set G) = ⊥) : Function.Injective (action L e) :=
  (MulAut.congr e).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot L hC)

private theorem localImage_action (L : Subgroup G) [L.Normal]
    (e : L ≃* PSL(3,F)) (b : Bool) :
    (localImage L e b).map (action L e) = (localFactor F b).map MulAut.conj := by
  rw [localImage, Subgroup.map_map]
  change (localFactor F b).map ((action L e).comp (linearThreeEmbedding L e)) = _
  congr 1
  apply MonoidHom.ext
  intro x
  exact action_embedding L e x

private theorem action_preserves_local (L : Subgroup G) [L.Normal]
    (e : L ≃* PSL(3,F)) (b : Bool) (g : G)
    (hg : g ∈ normalizer (localImage L e b : Set G)) :
    (localFactor F b).map (action L e g).toMonoidHom = localFactor F b := by
  apply Subgroup.map_injective (embedding_injective L e)
  have h := mem_normalizer_iff_map_conj_eq.mp hg
  rw [localImage, Subgroup.map_map] at h
  have hc : (linearThreeEmbedding L e).comp (action L e g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (linearThreeEmbedding L e) := by
    apply MonoidHom.ext
    intro x
    exact embedding_action L e g x
  rw [Subgroup.map_map, hc]
  exact h

variable [Finite F]

/-- The local core identity in the original ambient group. Only the faithful
normal model and normalization of the selected local are needed. -/
theorem localJoin_core_eq [CharP F 2]
    (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    (hC : centralizer (L : Set G) = ⊥) {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2^f) (b : Bool) (U : Subgroup G)
    (hn : U ≤ normalizer (localImage L e b : Set G)) :
    (pCore 2 (localImage L e b ⊔ U : Subgroup G)).map
      (localImage L e b ⊔ U).subtype = coreImage L e b := by
  change (localImage L e b ⊔ U).pCoreIn 2 = (localImage L e b).pCoreIn 2
  apply Subgroup.map_injective (action_injective L e hC)
  rw [map_pCoreIn_of_injective 2 _ _ (action_injective L e hC),
    map_pCoreIn_of_injective 2 _ _ (action_injective L e hC),
    Subgroup.map_sup, localImage_action]
  apply Matrix.PSL3.LinearThree.OuterExtensions.AmbientLocalCores.local_join_core_in_aut F hf hF
  rintro a ⟨g, hg, rfl⟩
  exact action_preserves_local L e b g (hn hg)

/-- In the binary model every normalizing two-group lies in the local itself.
The statement retains the literal original socle embedding. -/
theorem twoGroup_le_localImage_of_card_two [CharP F 2]
    (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    (hC : centralizer (L : Set G) = ⊥) (hF : Nat.card F = 2)
    (b : Bool) (U : Subgroup G) (hU : IsPGroup 2 U)
    (hn : U ≤ normalizer (localImage L e b : Set G)) : U ≤ localImage L e b := by
  intro g hg
  have hp : ∃ k : ℕ, action L e g ^ (2^k) = 1 := by
    obtain ⟨k, hk⟩ := hU.exists_pow_pow_eq_one (⟨g,hg⟩ : U)
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact (congrArg (fun x : U => action L e x.val) hk).trans (map_one _)
  obtain ⟨x,hx,he⟩ :=
    Matrix.PSL3.LinearThree.OuterExtensions.AmbientLocalCores.binary_two_element_local F hF b
      (action L e g) (action_preserves_local L e b g (hn hg)) hp
  have hgx : g = linearThreeEmbedding L e x :=
    action_injective L e hC (he.trans (action_embedding L e x).symm)
  rw [hgx]
  exact mem_map_of_mem _ hx

variable [Finite G] [IsSimpleGroup (generalizedFitting G)]

omit [Finite F] in
private theorem socle_centralizer (e : generalizedFitting G ≃* PSL(3,F)) :
    centralizer (generalizedFitting G : Set G) = ⊥ := by
  let := Atlas.psl_perfect (F := F) 3 (by decide)
  let : Group.IsPerfect (generalizedFitting G) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact SimpleSocle.centralizer_eq_bot
    (Group.IsPerfect.not_isMulCommutative (generalizedFitting G))

/-- The ambient model premise of `tauJoin_isEMemberAt_of_core_eq`.
This holds also when f = 1, without SQTK, rank, or alignment assumptions. -/
theorem tauJoin_core_eq (e : generalizedFitting G ≃* PSL(3,F))
    (T : Sylow 2 G) {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (b : Bool) (A : Subgroup G)
    (hn : tau (T : Subgroup G) A ≤
      normalizer (localImage (generalizedFitting G) e b : Set G)) :
    (pCore 2 (localImage (generalizedFitting G) e b ⊔ tau (T : Subgroup G) A : Subgroup G)).map
      (localImage (generalizedFitting G) e b ⊔ tau (T : Subgroup G) A).subtype =
      coreImage (generalizedFitting G) e b := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact localJoin_core_eq _ e (socle_centralizer e) hf hF b _ hn

/-- The binary tau collapse used by the source E1-member assembly. The full
ambient Sylow may contain graph actors; only this normalizing tau is restricted. -/
theorem tau_le_localImage_of_card_two (e : generalizedFitting G ≃* PSL(3,F))
    (T : Sylow 2 G) (hF : Nat.card F = 2) (b : Bool) (A : Subgroup G)
    (hn : tau (T : Subgroup G) A ≤
      normalizer (localImage (generalizedFitting G) e b : Set G)) :
    tau (T : Subgroup G) A ≤ localImage (generalizedFitting G) e b := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hF)
  exact twoGroup_le_localImage_of_card_two _ e (socle_centralizer e) hF b _
    (T.isPGroup'.to_le (tau_le _ _)) hn

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.AmbientCores
