module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.MuCentralizerModel.Finite
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Transpositions.SixParity

/-!
# Identifying the source involution centralizer

The supplied S6 equivalence carries A onto the even permutations. A centralizes
both generators of the four-group, whereas mu-prime acts by the binary shear.
Consequently the source action agrees with the explicit semidirect product.
The source centralizer equality proves surjectivity of its natural map to
C_G(mu), and the supplied centralizer order proves bijectivity. The first
binary generator maps to the literal ambient mu. No ambient recognition,
root factor, quotient recognition, simplicity or fusion is used.

Source: Held, Illinois J. Math. 13 (1969), Lemmas 4.2 and 5.4,
DOI 10.1215/ijm/1256053756, pp.232,236–237.
-/

@[expose] public section

open Equiv Subgroup
open Theory.GroupTheory.HeldM22A10
open Theory.GroupTheory.HeldM22A10.A10Identification
open Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.MuCentralizerConstruction

noncomputable section
variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer) (L : Source.SixLocalData D e)

def sourceFour : Four →* G := (D.a10ModelEmbedding e).comp fourCoordinates

theorem sourceFour_first : sourceFour D e first = mu D e := by
  change D.a10ModelEmbedding e (fourCoordinates first) = _
  rw [fourCoordinates_first]
  rfl

theorem sourceFour_second : sourceFour D e second = lam D e := by
  change D.a10ModelEmbedding e (fourCoordinates second) = _
  rw [fourCoordinates_second]
  rfl

theorem sourceFour_flip (k : Four) :
    sourceFour D e (flip k) = mu' D e * sourceFour D e k * (mu' D e)⁻¹ := by
  simpa only [sourceFour, MonoidHom.comp_apply, element, map_mul, map_inv] using
    congrArg (D.a10ModelEmbedding e) (fourCoordinates_flip k)

theorem sourceFour_centralized (a : G) (ha : a ∈ L.A) (k : Four) :
    Commute a (sourceFour D e k) := by
  have hm : Commute a (mu D e) :=
    (mem_centralizer_iff.mp (L.A_centralizes ha) _ (by simp)).symm
  have hl : Commute a (lam D e) :=
    (mem_centralizer_iff.mp (L.A_centralizes ha) _ (by simp)).symm
  change Commute a (D.a10ModelEmbedding e
    (modelElement 1 ^ k.toAdd.1.val * modelElement 6 ^ k.toAdd.2.val))
  simpa only [map_mul, map_pow, element] using
    (hm.pow_right k.toAdd.1.val).mul_right (hl.pow_right k.toAdd.2.val)

def sourceSix : Perm (Fin 6) →* G :=
  (L.A ⊔ zpowers (mu' D e) : Subgroup G).subtype.comp L.symmetricEquiv.symm.toMonoidHom

theorem six_even_iff (s : (L.A ⊔ zpowers (mu' D e) : Subgroup G)) :
    Perm.sign (L.symmetricEquiv s) = 1 ↔ (s : G) ∈ L.A := by
  change L.symmetricEquiv s ∈ alternatingGroup (Fin 6) ↔ _
  change s ∈ (alternatingGroup (Fin 6)).comap L.symmetricEquiv.toMonoidHom ↔ _
  rw [six_even_subgroup]
  rfl

theorem sourceSix_even_iff (p : Perm (Fin 6)) :
    Perm.sign p = 1 ↔ sourceSix D e L p ∈ L.A := by
  simpa only [sourceSix, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Subgroup.coe_subtype, MulEquiv.apply_symm_apply] using six_even_iff D e L (L.symmetricEquiv.symm p)

def actor : (L.A ⊔ zpowers (mu' D e) : Subgroup G) :=
  ⟨mu' D e, (show zpowers (mu' D e) ≤ L.A ⊔ zpowers (mu' D e) from le_sup_right)
    (mem_zpowers _)⟩

theorem actor_odd : Perm.sign (L.symmetricEquiv (actor D e L)) = -1 := by
  rcases Int.units_eq_one_or (Perm.sign (L.symmetricEquiv (actor D e L))) with h | h
  · exfalso
    have ha : mu' D e ∈ L.A := (six_even_iff D e L _).mp h
    have hc : lam D e * mu' D e = mu' D e * lam D e :=
      mem_centralizer_iff.mp (L.A_centralizes ha) _ (by simp)
    have hm : modelElement 6 * modelElement 2 = modelElement 2 * modelElement 6 :=
      D.a10ModelEmbedding_injective e (by simpa only [map_mul, element] using hc)
    exact (by decide +kernel : modelElement 6 * modelElement 2 ≠
      modelElement 2 * modelElement 6) hm
  · exact h

theorem source_action (p : Perm (Fin 6)) (k : Four) :
    sourceFour D e (action p k) =
      sourceSix D e L p * sourceFour D e k * (sourceSix D e L p)⁻¹ := by
  rcases Int.units_eq_one_or (Perm.sign p) with hp | hp
  · have ha := (sourceSix_even_iff D e L p).mp hp
    have hc := sourceFour_centralized D e L _ ha k
    change sourceFour D e (signAction (Perm.sign p) k) = _
    simp only [hp, signAction, ite_true, MonoidHom.coe_mk, OneHom.coe_mk, MulAut.one_apply]
    rw [hc.eq, mul_inv_cancel_right]
  · have ha : sourceSix D e L p * mu' D e ∈ L.A := by
      apply (six_even_iff D e L (L.symmetricEquiv.symm p * actor D e L)).mp
      rw [map_mul, map_mul, L.symmetricEquiv.apply_symm_apply, hp, actor_odd]
      decide
    have hc := sourceFour_centralized D e L _ ha (flip k)
    change sourceFour D e (signAction (Perm.sign p) k) = _
    have hn : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [hp, signAction, if_neg hn, MonoidHom.coe_mk, OneHom.coe_mk]
    calc
      sourceFour D e (flip k) =
          (sourceSix D e L p * mu' D e) * sourceFour D e (flip k) *
            (sourceSix D e L p * mu' D e)⁻¹ := by rw [hc.eq, mul_inv_cancel_right]
      _ = sourceSix D e L p * sourceFour D e k * (sourceSix D e L p)⁻¹ := by
        rw [sourceFour_flip]
        have hm := element_square D e 2 (by decide)
        have hi : (mu' D e)⁻¹ = mu' D e := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hm)
        rw [mul_inv_rev, hi]
        simp only [mul_assoc]
        simp only [← mul_assoc (mu' D e), ← pow_two, hm, one_mul]


def sourceHom : Model →* G :=
  SemidirectProduct.lift (sourceFour D e) (sourceSix D e L) (by
    intro p
    apply MonoidHom.ext
    intro k
    exact source_action D e L p k)

theorem sourceHom_first : sourceHom D e L (SemidirectProduct.inl first) = mu D e := by
  rw [sourceHom, SemidirectProduct.lift_inl, sourceFour_first]

theorem sourceHom_second : sourceHom D e L (SemidirectProduct.inl second) = lam D e := by
  rw [sourceHom, SemidirectProduct.lift_inl, sourceFour_second]

theorem sourceHom_range : (sourceHom D e L).range = muCentralizer D e := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [← sourceHom_first D e L]
    exact ((first_central x).symm.map (sourceHom D e L)).eq
  · change centralizer ({mu D e} : Set G) ≤ _
    rw [L.centralizer_mu]
    apply sup_le
    · apply sup_le
      · apply (closure_le _).mpr
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact ⟨SemidirectProduct.inl first, sourceHom_first D e L⟩
        · have hx' : x = lam D e := Set.mem_singleton_iff.mp hx
          subst x
          exact ⟨SemidirectProduct.inl second, sourceHom_second D e L⟩
      · intro a ha
        let a₀ : (L.A ⊔ zpowers (mu' D e) : Subgroup G) := ⟨a, (show L.A ≤ L.A ⊔ zpowers (mu' D e) from le_sup_left) ha⟩
        refine ⟨SemidirectProduct.inr (L.symmetricEquiv a₀), ?_⟩
        simp [sourceHom, sourceSix, a₀]
    · apply zpowers_le.mpr
      refine ⟨SemidirectProduct.inr (L.symmetricEquiv (actor D e L)), ?_⟩
      simp [sourceHom, sourceSix, actor]

def sourceCentralizerHom : Model →* muCentralizer D e :=
  (sourceHom D e L).codRestrict _ (fun x => sourceHom_range D e L ▸ ⟨x, rfl⟩)

theorem sourceCentralizerHom_surjective : Function.Surjective (sourceCentralizerHom D e L) := by
  intro x
  have hx : (x : G) ∈ (sourceHom D e L).range := by rw [sourceHom_range]; exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

def sourceEquiv (hcard : Nat.card (muCentralizer D e) = 2880) :
    Model ≃* muCentralizer D e :=
  MulEquiv.ofBijective (sourceCentralizerHom D e L)
    ((sourceCentralizerHom_surjective D e L).bijective_of_nat_card_le (by rw [model_card, hcard]))

theorem sourceEquiv_first (hcard : Nat.card (muCentralizer D e) = 2880) :
    sourceEquiv D e L hcard (SemidirectProduct.inl first) = centralMu D e := by
  apply Subtype.ext
  exact sourceHom_first D e L

end
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.MuCentralizerConstruction
