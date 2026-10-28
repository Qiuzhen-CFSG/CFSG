module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.Quotient
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Natural

/-!
# A marked natural model for the L₂ block

An isomorphism between two characteristic-two SL₂ groups takes a root Sylow
subgroup to a conjugate root Sylow subgroup. Taking normalizers matches their
Borels. Conjugating both the actor and its natural module therefore gives a
block model marked by the actual intersection M ∩ L.

The already constructed faithful image of V₂ has order four in this model.
The natural Borel's invariant-subgroup bound forces the model field to have
order four. No classification of automorphisms or comparison of abstract
group-family tags is used.

Source: Aschbacher–Smith 15.3.30, printed pp.1131–1132; C.1.12, p.124.
-/

@[expose] public section

open Subgroup Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

private theorem exists_conjugate_borel {E F : Type*}
    [Field E] [Finite E] [CharP E 2] [Field F] [Finite F] [CharP F 2]
    (e : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) E) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) E,
      ((rankOneBorel F).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        rankOneBorel E := by
  let P := (upperUnipotentSylow F 2).mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) E)
    P (upperUnipotentSylow E 2)
  have hU : ((upperUnipotent F).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      upperUnipotent E := congrArg Sylow.toSubgroup hg
  refine ⟨g, ?_⟩
  rw [rankOneBorel, map_normalizer_eq_of_bijective _ e.bijective,
    map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective, hU]

private def conjugateModel {L A W : Type*} [Group L] [Group A] [Group W]
    {rho : A →* MulAut W} (model : ChapterC.BlockModuleModel L rho) (g : A) :
    ChapterC.BlockModuleModel L rho where
  quotientIso := model.quotientIso.trans (MulAut.conj g)
  moduleIso := model.moduleIso.trans (rho g)
  intertwining l u := by
    change rho g (model.moduleIso _) = rho (g * model.quotientIso _ * g⁻¹)
      (rho g (model.moduleIso _))
    rw [model.intertwining]
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply]

variable {G : Type*} [Group G] (d : LocalData G) (I : Subgroup G)
  (c : ComponentWitness d I) (F : Type*) [Field F]

/-- The natural block representation with the Borel marked by M ∩ L.
Both its action and its quotient map are part of the compatible model. -/
structure MarkedBlockModel where
  model : ChapterC.BlockModuleModel c.L (Matrix.SL2.naturalAction F)
  borel : (d.M.subgroupOf c.L).map
    (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) =
      rankOneBorel F

variable {d I c F} {m n : ℕ} [Finite F] [CharP F 2]

/-- Match the original block model to the Borel coming from the star quotient.
The field is the field of the actual natural block, with its original order. -/
theorem exists_markedBlockModel (b : BorelIdentification d I c n F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hblock : ChapterC.IsL2EvenBlock c.L m) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nat.card E = 2 ^ m ∧ Nonempty (MarkedBlockModel d I c E) := by
  have hblock' := hblock
  obtain ⟨_, _, E, _, _, hE, _, rho, ⟨model⟩, hlinear⟩ := hblock'
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  have hrho : rho = Matrix.SL2.naturalAction E := by
    ext g : 1
    ext v : 1
    exact Multiplicative.toAdd.injective (hlinear g v)
  subst rho
  let f := b.coreLinear h P hP hblock
  let e := f.symm.trans model.quotientIso
  obtain ⟨g, hg⟩ := exists_conjugate_borel e
  refine ⟨E, inferInstance, inferInstance, inferInstance, hE,
    ⟨⟨conjugateModel model g, ?_⟩⟩⟩
  have hmap : (conjugateModel model g).quotientIso.toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 c.L)) =
      (MulAut.conj g).toMonoidHom.comp (e.toMonoidHom.comp
        (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)))) := by
    ext l : 1
    change g * model.quotientIso _ * g⁻¹ = g * model.quotientIso (f.symm (f _)) * g⁻¹
    rw [f.symm_apply_apply]
  rw [hmap, ← map_map, ← map_map, b.coreLinear_borel h P hP hblock]
  exact hg

omit [CharP F 2] in
/-- The faithful four-group in the natural block bounds the marked field. -/
theorem MarkedBlockModel.field_card_le_four [Finite G]
    (a : MarkedBlockModel d I c F) (h : Earlier d I c) (hSI : d.S ≤ I) :
    Nat.card F ≤ 4 := by
  obtain ⟨W, hW, hinv⟩ := h.blockModel_plane d hSI a.model
  have hne : W ≠ ⊥ := by
    intro he
    simp [he] at hW
  have hinv' : ∀ g ∈ rankOneBorel F, ∀ v ∈ W, Matrix.SL2.naturalAction F g v ∈ W := by
    simpa only [a.borel] using hinv
  exact (Matrix.SL2.card_le_of_naturalAction_borel_invariant W hne hinv').trans_eq hW

/-- The natural model field has order four in this local configuration. -/
theorem exists_markedBlockModel_four [Finite G]
    (b : BorelIdentification d I c n F) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hblock : ChapterC.IsL2EvenBlock c.L m) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nat.card E = 4 ∧ Nonempty (MarkedBlockModel d I c E) := by
  obtain ⟨E, _, _, _, hE, ⟨a⟩⟩ := exists_markedBlockModel b h P hP hblock
  have hSI : d.S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  have hle := a.field_card_le_four h hSI
  have hge : 4 ≤ Nat.card E := by
    rw [hE]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by have := hblock.1; omega : 2 ≤ m)
  exact ⟨E, inferInstance, inferInstance, inferInstance, le_antisymm hle hge, ⟨a⟩⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

end
