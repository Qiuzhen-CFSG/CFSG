module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.HeadFamily
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.WeakClosure
public import Theory.SpecificGroups.Triality.ParabolicNormalizer

/-!
# Transport of triality normalizer geometry through a normal model copy

Conjugation on the normal copy L gives an actual homomorphism to automorphisms
of the standard carrier. Its subgroup stabilizers pull back exactly to ambient
normalizers. The normalizer of an embedded full parabolic is its join with T
when G = LT and T is aligned with the positive Sylow subgroup. In particular,
stabilizing the model parabolic gives containment in the prescribed ambient
parabolic overgroup, with the entire conjugation kernel retained.

The pointwise stabilizer of an actor in the image of T lifts to its centralizer
in T and hence to the literal source tau, even if the ambient two-core is
nontrivial. These are transport results; the head-intersection geometry is not
asserted here.

Source: Aschbacher--Smith E.1.1 and the outer-extension setting of E.1.14(2),
printed pp.209,214; GLS3 §§2.3--2.6 for the full model parabolics.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] {f : ℕ} {hf : 0 < f}

/-- The actual conjugation action transported through the marked model isomorphism. -/
def modelAction (L : Subgroup G) [L.Normal] (e : L ≃* BinaryCarrier f hf) :
    G →* MulAut (BinaryCarrier f hf) :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := L))

theorem modelAction_compatible (L : Subgroup G) [L.Normal]
    (e : L ≃* BinaryCarrier f hf) (g : G) (x : BinaryCarrier f hf) :
    modelEmbedding L e (modelAction L e g x) =
      g * modelEmbedding L e x * g⁻¹ := by
  change (e.symm (e ((MulAut.conjNormal (H := L) g) (e.symm x))) : G) = _
  rw [e.symm_apply_apply]
  rfl

theorem map_modelAction (L : Subgroup G) [L.Normal]
    (e : L ≃* BinaryCarrier f hf) (B : Subgroup (BinaryCarrier f hf)) (g : G) :
    (B.map (modelAction L e g).toMonoidHom).map (modelEmbedding L e) =
      (B.map (modelEmbedding L e)).map (MulAut.conj g).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  exact modelAction_compatible L e g x

/-- No faithfulness hypothesis is required for stabilizer transport. -/
theorem modelAction_stabilizes_iff (L : Subgroup G) [L.Normal]
    (e : L ≃* BinaryCarrier f hf) (B : Subgroup (BinaryCarrier f hf)) (g : G) :
    B.map (modelAction L e g).toMonoidHom = B ↔
      g ∈ normalizer (B.map (modelEmbedding L e) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  change _ ↔ (B.map (modelEmbedding L e)).map (MulAut.conj g).toMonoidHom = _
  rw [← map_modelAction]
  exact ⟨fun h => congrArg (fun K => K.map (modelEmbedding L e)) h,
    fun h => map_injective (modelEmbedding_injective L e) h⟩

theorem modelAction_on_model (L : Subgroup G) [L.Normal]
    (e : L ≃* BinaryCarrier f hf) (x : BinaryCarrier f hf) :
    modelAction L e (modelEmbedding L e x) = MulAut.conj x := by
  ext y
  apply modelEmbedding_injective L e
  rw [modelAction_compatible]
  simp only [MulAut.conj_apply, map_mul, map_inv]

/-- The conjugation image of L is exactly the inner automorphism subgroup. -/
theorem modelAction_map_socle (L : Subgroup G) [L.Normal]
    (e : L ≃* BinaryCarrier f hf) :
    L.map (modelAction L e) = (MulAut.conj : BinaryCarrier f hf →*
      MulAut (BinaryCarrier f hf)).range := by
  calc
    L.map (modelAction L e) =
        (modelEmbedding L e).range.map (modelAction L e) :=
      congrArg (fun K => K.map (modelAction L e)) (modelEmbedding_range L e).symm
    _ = _ := ?_
  rw [MonoidHom.map_range]
  congr 1
  apply MonoidHom.ext
  intro x
  exact modelAction_on_model L e x

theorem modelAction_range_of_join (L T : Subgroup G) [L.Normal]
    (e : L ≃* BinaryCarrier f hf) (hLT : L ⊔ T = ⊤) :
    (modelAction L e).range =
      (MulAut.conj : BinaryCarrier f hf →* MulAut (BinaryCarrier f hf)).range ⊔
        T.map (modelAction L e) := by
  rw [← modelAction_map_socle L e, ← Subgroup.map_sup, hLT, ← MonoidHom.range_eq_map]

/-- A model pointwise fixer in the image of T has a lift in the source tau. -/
theorem modelAction_fixer_lifts_to_tau (L T : Subgroup G) [L.Normal]
    (e : L ≃* BinaryCarrier f hf) (B : Subgroup (BinaryCarrier f hf))
    (β : MulAut (BinaryCarrier f hf)) (hβ : β ∈ T.map (modelAction L e))
    (hfix : ∀ x ∈ B, β x = x) :
    β ∈ (tau T (B.map (modelEmbedding L e))).map (modelAction L e) := by
  obtain ⟨t, ht, rfl⟩ := hβ
  refine ⟨t, mem_centralizerModulo_iff.mpr ⟨ht, ?_⟩, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  have he := modelAction_compatible L e t x
  rw [hfix x hx] at he
  have hc : modelEmbedding L e x * t = t * modelEmbedding L e x := by
    have h := congrArg (fun z : G => z * t) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
  exact (pCore 2 G).one_mem

/-- Alignment identifies the model Sylow and makes the image of T preserve it. -/
theorem modelAction_unipotent_invariant (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf))
    (β : MulAut (BinaryCarrier f hf))
    (hβ : β ∈ (T : Subgroup G).map (modelAction L e)) :
    (unipotent (binaryParameters f hf)).map β.toMonoidHom =
      unipotent (binaryParameters f hf) := by
  obtain ⟨t, ht, rfl⟩ := hβ
  apply (modelAction_stabilizes_iff L e _ t).mpr
  rw [aligned_unipotent_map L T e he]
  exact inf_normalizer_le_normalizer_inf
    ⟨(T : Subgroup G).le_normalizer ht, by rw [normalizer_eq_top]; trivial⟩

/-- The full ambient normalizer of a model parabolic is its prescribed T-overgroup. -/
theorem normalizer_ambientParabolic [Finite G] (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf))
    (hLT : L ⊔ (T : Subgroup G) = ⊤) (a : Node) :
    normalizer (ambientParabolic L e a : Set G) = parabolicOvergroup L T e a := by
  have hTN := sylow_normalizes_ambientParabolic L T e he a
  apply le_antisymm
  · intro g hg
    have hprod : g ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L (T : Subgroup G)
        (le_top.trans (normalizer_eq_top (H := L)).ge), hLT]
      trivial
    obtain ⟨l, hl, t, ht, rfl⟩ := hprod
    have hlN : l ∈ normalizer (ambientParabolic L e a : Set G) := by
      have h := (normalizer (ambientParabolic L e a : Set G)).mul_mem hg
        ((normalizer (ambientParabolic L e a : Set G)).inv_mem (hTN ht))
      simpa using h
    let x : BinaryCarrier f hf := e ⟨l, hl⟩
    have hx : modelEmbedding L e x = l := by
      change (e.symm (e ⟨l, hl⟩) : G) = l
      rw [e.symm_apply_apply]
    have hxN : x ∈ normalizer (parabolic (binaryParameters f hf) a : Set _) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [← modelAction_on_model L e x, hx]
      exact (modelAction_stabilizes_iff L e _ l).mpr hlN
    rw [normalizer_parabolic_binary _ rfl] at hxN
    exact (parabolicOvergroup L T e a).mul_mem
      (Subgroup.mem_sup_left (mem_map.mpr ⟨x, hxN, hx⟩)) (Subgroup.mem_sup_right ht)
  · exact sup_le (ambientParabolic L e a).le_normalizer hTN

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
