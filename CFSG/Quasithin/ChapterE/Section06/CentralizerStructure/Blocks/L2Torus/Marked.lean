module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Borel
public import Theory.SpecificGroups.SL2.Affine

/-!
# Matching the natural block model with its Borel

Conjugate the quotient isomorphism and the module isomorphism together to
match the Borel supplied by `L2BlockBorel`. Sylow conjugacy suffices, even
when the two identifications initially use different finite fields.

Faithfulness of the resulting natural action gives C_L(U(L)) = O₂(L).
Consequently Ω₁(Z(S)) lies in O₂(L): it centralizes U(L), which is contained
in every Sylow two-subgroup. This preliminary step needs no covering theorem.

Source: Aschbacher–Smith, C.1.7, C.1.12 and the calculation in E.6.7,
printed pp.123–124 and 246. The simultaneous conjugation argument also
appears in Chapter15's `LinearTwo.Centralizer.NaturalModel`.
-/

@[expose] public section

open Subgroup Matrix.SpecialLinearGroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.L2Torus
variable {L : Type*} [Group L] {F : Type*} [Field F]

structure MarkedBlockModel (L : Type*) [Group L] (B : Subgroup L)
    (F : Type*) [Field F] where
  model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)
  borel : B = (rankOneBorel F).comap
    (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))

variable {B : Subgroup L}

def MarkedBlockModel.linearMap (a : MarkedBlockModel L B F) : L →* SL(2, F) :=
  a.model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem MarkedBlockModel.linearMap_surjective (a : MarkedBlockModel L B F) :
    Function.Surjective a.linearMap :=
  a.model.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

theorem MarkedBlockModel.linearMap_ker (a : MarkedBlockModel L B F) :
    a.linearMap.ker = pCore 2 L := by
  ext x
  change a.model.quotientIso (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ _
  rw [map_eq_one_iff _ a.model.quotientIso.injective]
  exact QuotientGroup.eq_one_iff x

theorem MarkedBlockModel.borel_index [Finite F] (a : MarkedBlockModel L B F) :
    B.index = Nat.card F + 1 := by
  calc
    B.index = ((rankOneBorel F).comap a.linearMap).index := congrArg Subgroup.index a.borel
    _ = _ := by rw [index_comap_of_surjective _ a.linearMap_surjective, index_borel]

theorem MarkedBlockModel.sylow_eq_root_comap [Finite F] [CharP F 2]
    (a : MarkedBlockModel L B F) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    (S : Subgroup L) = (upperUnipotent F).comap a.linearMap := by
  apply L2Torus.sylow_eq_root_comap a.linearMap a.linearMap_surjective
    (by rw [a.linearMap_ker]; exact pCore_isPGroup) S
  exact hS.trans_eq a.borel

theorem MarkedBlockModel.borel_normalizes_sylow [Finite F] [CharP F 2]
    (a : MarkedBlockModel L B F) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    B ≤ normalizer (S : Set L) := by
  rw [← S.coe_coe, a.sylow_eq_root_comap S hS]
  exact le_trans (le_of_eq a.borel) (le_normalizer_comap a.linearMap)

theorem MarkedBlockModel.centralizer_blockU_eq_core (a : MarkedBlockModel L B F)
    (hL : ChapterC.IsShort L) :
    centralizer (ChapterC.blockU L : Set L) = pCore 2 L := by
  apply le_antisymm _ hL.core_centralizes_blockU
  intro z hz
  rw [← a.linearMap_ker]
  change a.linearMap z = 1
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  obtain ⟨uQ, huQ⟩ := a.model.moduleIso.surjective (Multiplicative.ofAdd v)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (ChapterC.blockFixed L) uQ
  have hconj : ChapterC.blockConjugate L z u = u := by
    apply Subtype.ext
    change z * (u : L) * z⁻¹ = u
    rw [← mem_centralizer_iff.mp hz u u.property, mul_inv_cancel_right]
  have he := a.model.intertwining z u
  rw [hconj, huQ] at he
  have hv := (congrArg Multiplicative.toAdd he).symm
  rw [map_one]
  exact hv

theorem MarkedBlockModel.omegaOneCenter_le_core (a : MarkedBlockModel L B F)
    (hL : ChapterC.IsShort L) (S : Sylow 2 L) :
    Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ≤ pCore 2 L := by
  rw [← a.centralizer_blockU_eq_core hL]
  intro z hz
  have hc := (Stellmacher.mem_omegaOneCenterAmbient_iff (S : Subgroup L) z).mp hz
  apply mem_centralizer_iff.mpr
  intro u hu
  exact hc.2.2 u (pCore_isPGroup.le_sylow_of_normal S (ChapterC.blockU_le_core hu))

private theorem exists_conjugate_borel {E F : Type*}
    [Field E] [Finite E] [CharP E 2] [Field F] [Finite F] [CharP F 2]
    (e : SL(2, F) ≃* SL(2, E)) :
    ∃ g : SL(2, E),
      ((rankOneBorel F).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        rankOneBorel E := by
  let P := (upperUnipotentSylow F 2).mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(2, E)) P (upperUnipotentSylow E 2)
  have hU : ((upperUnipotent F).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      upperUnipotent E := congrArg Sylow.toSubgroup hg
  refine ⟨g, ?_⟩
  rw [rankOneBorel, map_normalizer_eq_of_bijective _ e.bijective,
    map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective, hU]

private def conjugateModel {A W : Type*} [Group A] [Group W]
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

theorem exists_markedBlockModel {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (hB : L2BlockBorel L B n) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      Nat.card E = 2 ^ n ∧ Nonempty (MarkedBlockModel L B E) := by
  obtain ⟨_, _, E, _, _, hE, _, rho, ⟨model⟩, hlinear⟩ := hL
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  have hrho : rho = Matrix.SL2.naturalAction E := by
    ext g : 1
    ext v : 1
    exact Multiplicative.toAdd.injective (hlinear g v)
  subst rho
  obtain ⟨F, _, _, hF, eB, hB⟩ := hB
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e := eB.symm.trans model.quotientIso
  obtain ⟨g, hg⟩ := exists_conjugate_borel e
  refine ⟨E, inferInstance, inferInstance, inferInstance, hE,
    ⟨⟨conjugateModel model g, ?_⟩⟩⟩
  ext l
  rw [hB, mem_comap, mem_comap, ← hg, mem_map_equiv, mem_map_equiv]
  change eB (QuotientGroup.mk' (pCore 2 L) l) ∈ rankOneBorel F ↔
    e.symm ((MulAut.conj g).symm ((MulAut.conj g)
      (model.quotientIso (QuotientGroup.mk' (pCore 2 L) l)))) ∈ rankOneBorel F
  rw [MulEquiv.symm_apply_apply]
  change _ ↔ eB (model.quotientIso.symm
    (model.quotientIso (QuotientGroup.mk' (pCore 2 L) l))) ∈ rankOneBorel F
  rw [MulEquiv.symm_apply_apply]

end CFSG.Quasithin.ChapterE.Section06.L2Torus
