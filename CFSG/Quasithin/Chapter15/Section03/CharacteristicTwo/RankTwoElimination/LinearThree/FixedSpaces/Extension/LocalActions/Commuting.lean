module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Transport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.Multiplicity
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.ResidualAlternatives.Duality
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# Commuting actions on the moving SL₃(2) layers

A commuting automorphism of a fully moving module with one natural quotient
is trivial: its action on the quotient is a binary scalar, and displacement
into the fixed kernel kills all component commutators. For two natural copies,
a two-perfect commuting actor either acts trivially or has both full
displacement and zero fixed space. The two conclusions are proved separately.

Source: Aschbacher–Smith, B.4.8, pp.91–92, and the centralizer action in
15.3.23, printed p.1128 of the combined manuscript of 1 March 2004.
-/

@[expose] public section
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

/-- Transport of full displacement along actual equivariant coordinates. -/
theorem full_displacement_of_equiv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) K V) (τ : Representation (ZMod 2) K W)
    (e : V ≃ₗ[ZMod 2] W) (he : ∀ k v, e (σ k v) = τ k (e v))
    (hfull : Coinvariants.ker τ = ⊤) : Coinvariants.ker σ = ⊤ := by
  have hle : Coinvariants.ker τ ≤ (Coinvariants.ker σ).map e.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k,w⟩, rfl⟩
    obtain ⟨v,rfl⟩ := e.surjective w
    exact ⟨σ k v - v, Coinvariants.sub_mem_ker k v, by
      change e (σ k v - v) = τ k (e v) - e v
      rw [map_sub, he]⟩
  apply top_unique
  intro v _
  obtain ⟨w,hw,hh⟩ := hle (hfull ▸ Submodule.mem_top (x := e v))
  exact e.injective hh ▸ hw

private theorem one_natural_trivial
    (σ : Representation (ZMod 2) K (Fin 1 → Fin 3 → ZMod 2))
    (hc : ∀ k g v, σ k (NaturalCopies (ZMod 2) 1 g v) =
      NaturalCopies (ZMod 2) 1 g (σ k v)) : ∀ k, σ k = 1 := by
  intro k
  let f : (specialLinearNatural (k := ZMod 2) 3).IntertwiningMap
      (specialLinearNatural (k := ZMod 2) 3) :=
    { toLinearMap := (LinearMap.proj 0).comp ((σ k).comp
        (LinearMap.pi (fun _ : Fin 1 => LinearMap.id)))
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        exact congrFun (hc k g (fun _ => v)) 0 }
  obtain ⟨a,ha⟩ := ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders.base_end_scalar f
  have hf (v : Fin 1 → Fin 3 → ZMod 2) : σ k v = a • v := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hv : (fun _ : Fin 1 => v 0) = v := by funext j; exact congrArg v (Subsingleton.elim _ _)
    have h := congrArg (fun t : (specialLinearNatural (k := ZMod 2) 3).IntertwiningMap
      (specialLinearNatural (k := ZMod 2) 3) => t (v 0)) ha
    change σ k (fun _ => v 0) 0 = a • v 0 at h
    rwa [hv] at h
  have ha1 : a = 1 := by
    have ha01 : a = 0 ∨ a = 1 := by
      exact (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a
    rcases ha01 with ha0 | ha1
    · have h := congrArg (σ k⁻¹) (hf (fun _ _ => 1))
      rw [ha0, zero_smul, map_zero, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply] at h
      have hn := congrFun (congrFun h 0) 0
      exact (one_ne_zero hn).elim
    · exact ha1
  apply LinearMap.ext
  intro v
  simpa only [ha1, one_smul, Module.End.one_apply] using hf v

variable (ρ : Representation (ZMod 2) SL V) (σ : Representation (ZMod 2) K V)
    (hc : ∀ k g v, σ k (ρ g v) = ρ g (σ k v))

include hc

private theorem fixed_preserved (k : K) :
    fixedSpace ρ ⊤ ≤ (fixedSpace ρ ⊤).comap (σ k) := by
  intro v hv g
  change ρ g.val (σ k v) = σ k v
  rw [← hc]
  exact congrArg (σ k) (hv g)

/-- The commuting action on the actual fixed-kernel quotient, in its marked coordinates. -/
noncomputable def quotientAction {m : ℕ} (q : ModuleQuotient ρ m) :
    Representation (ZMod 2) K (Fin m → Fin 3 → ZMod 2) :=
  (quotientCoordinates q).conjRingEquiv.toMonoidHom.comp
    (σ.quotient (fixedSpace ρ ⊤) (by intro k; exact fixed_preserved ρ σ hc k))

/-- The descended action intertwines the original surjective projection. -/
theorem quotientAction_projection {m : ℕ} (q : ModuleQuotient ρ m) (k : K) (v : V) :
    quotientAction ρ σ hc q k (q.projection v) = q.projection (σ k v) := by
  rw [← quotientCoordinates_mk q v]
  change quotientCoordinates q ((σ.quotient (fixedSpace ρ ⊤)
    (fixed_preserved ρ σ hc)) k ((quotientCoordinates q).symm
      (quotientCoordinates q ((fixedSpace ρ ⊤).mkQ v)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact quotientCoordinates_mk q (σ k v)

/-- The quotient action commutes with the natural copies under the common marking. -/
theorem quotientAction_commutes {m : ℕ} (q : ModuleQuotient ρ m)
    (k : K) (g : SL) (v : Fin m → Fin 3 → ZMod 2) :
    quotientAction ρ σ hc q k (NaturalCopies (ZMod 2) m g v) =
      NaturalCopies (ZMod 2) m g (quotientAction ρ σ hc q k v) := by
  obtain ⟨w,rfl⟩ := q.surjective v
  have he (w : V) : q.projection (ρ (q.marking.symm g) w) =
      NaturalCopies (ZMod 2) m g (q.projection w) := by
    funext i
    change _ = specialLinearNatural 3 g _
    simpa only [q.marking.apply_symm_apply] using q.equivariant (q.marking.symm g) w i
  rw [← he, quotientAction_projection, hc, he, quotientAction_projection]

/-- A fully moving cover of one natural copy has no nontrivial commuting action.
The central kernel need not split and no order restriction on the actor is needed. -/
theorem one_quotient_commuting_trivial (q : ModuleQuotient ρ 1)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) : ∀ k, σ k = 1 := by
  have hq := one_natural_trivial (quotientAction ρ σ hc q)
    (quotientAction_commutes ρ σ hc q)
  intro k
  have hd (v : V) : σ k v - v ∈ fixedSpace ρ ⊤ := by
    rw [← q.kernel]
    change q.projection (σ k v - v) = 0
    rw [map_sub, ← quotientAction_projection ρ σ hc q k v, hq, Module.End.one_apply, sub_self]
  have hle : subspaceCommutator ρ ⊤ ⊤ ≤ (σ k - LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    change σ k (ρ g v - v) - (ρ g v - v) = 0
    have hh := hd v ⟨g, Subgroup.mem_top _⟩
    change ρ g (σ k v - v) = σ k v - v at hh
    rw [map_sub] at hh ⊢
    rw [hc]
    exact sub_eq_zero.mpr ((sub_eq_sub_iff_sub_eq_sub).mp hh)
  apply LinearMap.ext
  intro v
  apply sub_eq_zero.mp
  apply hle
  rw [hfull]
  trivial

/-- A nontrivial two-perfect action on two marked natural copies has zero fixed space. -/
theorem doubled_fixed_eq_bot (copies : Copies ρ 2) (hK : IsPPerfect 2 K)
    (hne : ¬ ∀ k, σ k = 1) : fixedSpace σ ⊤ = ⊥ := by
  let τ := copies.equiv.conjRingEquiv.toMonoidHom.comp σ
  have he (k : K) (v : V) : τ k (copies.equiv v) = copies.equiv (σ k v) := by
    change copies.equiv (σ k (copies.equiv.symm (copies.equiv v))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hcomm (k : K) (g : SL) (v : Fin 2 → Fin 3 → ZMod 2) :
      τ k (NaturalCopies (ZMod 2) 2 g v) = NaturalCopies (ZMod 2) 2 g (τ k v) := by
    obtain ⟨w,rfl⟩ := copies.equiv.surjective v
    have hh (w : V) : copies.equiv (ρ (copies.marking.symm g) w) =
        NaturalCopies (ZMod 2) 2 g (copies.equiv w) := by
      funext i
      change _ = specialLinearNatural 3 g _
      simpa only [copies.marking.apply_symm_apply] using copies.equivariant (copies.marking.symm g) w i
    rw [← hh, he, hc, hh, he]
  apply le_bot_iff.mp
  intro v hv
  by_contra hn
  have hn' : copies.equiv v ≠ 0 := fun h => hn (copies.equiv.injective (h.trans (map_zero _).symm))
  have ht := CoreActions.NaturalActions.twoPerfect_copies_fixed (Or.inr rfl) τ hK hcomm
    (copies.equiv v) hn' (fun k => by
      rw [he]
      exact congrArg copies.equiv (hv ⟨k, Subgroup.mem_top _⟩))
  apply hne
  intro k
  apply LinearMap.ext
  intro w
  apply copies.equiv.injective
  rw [← he, ht]
  rfl

omit hc in
private noncomputable def doubleDualCoordinates :
    (Fin 2 → Fin 3 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 2 → Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) :=
  LinearEquiv.piCongrRight (fun _ => BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv)

omit hc in
private theorem doubleDualCoordinates_action (g : SL) (v : Fin 2 → Fin 3 → ZMod 2) :
    doubleDualCoordinates (NaturalCopies (ZMod 2) 2
      (BinaryLinearThree.AutomorphismAction.graph g) v) =
      DualCopies (ZMod 2) 2 g (doubleDualCoordinates v) := by
  funext i
  exact LinearMap.congr_fun
    (BinaryLinearThree.AutomorphismAction.graphNaturalDual.isIntertwining' g) (v i)

/-- The separate full-displacement assertion on doubled natural coordinates.
Duality detects a proper moved space; the two-perfect multiplicity theorem
then forces the original action to be trivial. -/
theorem doubled_full_displacement (copies : Copies ρ 2) (hK : IsPPerfect 2 K)
    (hne : ¬ ∀ k, σ k = 1) : Coinvariants.ker σ = ⊤ := by
  let E := copies.equiv.trans doubleDualCoordinates
  let τ := E.conjRingEquiv.toMonoidHom.comp σ
  have he (k : K) (v : V) : τ k (E v) = E (σ k v) := by
    change E (σ k (E.symm (E v))) = _
    rw [LinearEquiv.symm_apply_apply]
  have ht (g : SL) (v : V) :
      E (ρ (copies.marking.symm (BinaryLinearThree.AutomorphismAction.graph g)) v) =
        DualCopies (ZMod 2) 2 g (E v) := by
    have hh : copies.equiv
        (ρ (copies.marking.symm (BinaryLinearThree.AutomorphismAction.graph g)) v) =
        NaturalCopies (ZMod 2) 2 (BinaryLinearThree.AutomorphismAction.graph g) (copies.equiv v) := by
      funext i
      change _ = specialLinearNatural 3 (BinaryLinearThree.AutomorphismAction.graph g) _
      simpa only [copies.marking.apply_symm_apply] using
        copies.equivariant (copies.marking.symm (BinaryLinearThree.AutomorphismAction.graph g)) v i
    change doubleDualCoordinates (copies.equiv _) = _
    rw [hh, doubleDualCoordinates_action]
    rfl
  have hcomm (k : K) (g : SL)
      (v : Fin 2 → Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) :
      τ k (DualCopies (ZMod 2) 2 g v) = DualCopies (ZMod 2) 2 g (τ k v) := by
    obtain ⟨w,rfl⟩ := E.surjective v
    rw [← ht, he, hc, ht, he]
  rcases CoreActions.ThreeLayer.ResidualAlternatives.dual_copies_fixed_or_moving τ hK hcomm with h | h
  · apply False.elim
    apply hne
    intro k
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [← he, h]
    rfl
  · exact full_displacement_of_equiv σ τ E (fun k v => (he k v).symm) h

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
