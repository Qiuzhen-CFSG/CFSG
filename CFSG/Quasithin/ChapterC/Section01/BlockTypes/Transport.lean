module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport


/-!
# Transport of the intrinsic block models

An isomorphism maps O₂ and its commutator U onto the corresponding subgroups,
and maps C_U(L) onto the fixed subgroup. The induced quotient isomorphisms
intertwine conjugation. Thus both the named quotient and the actual natural
module in an L₂ or alternating block survive changing the subgroup carrier.

This supplies the final identification of the selected component with a factor
of the C.1.26 central product. Source: Aschbacher–Smith, combined manuscript
(1 March 2004), C.1.7 and C.1.12, printed pp.123–124; 15.3.30, p.1131.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {A B : Type*} [Group A] [Group B]

private theorem transport_blockU (e : A ≃* B) :
    (blockU A).map e.toMonoidHom = blockU B := by
  rw [blockU, map_commutator, pCore_map_iso,
    map_top_of_surjective _ e.surjective, blockU]

private def blockUEquiv (e : A ≃* B) : blockU A ≃* blockU B :=
  (e.subgroupMap (blockU A)).trans (MulEquiv.subgroupCongr (transport_blockU e))

private theorem transport_blockFixed (e : A ≃* B) :
    (blockFixed A).map (blockUEquiv e).toMonoidHom = blockFixed B := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.centerCongr e ⟨x, hx⟩).property
  · intro x hx
    exact ⟨(blockUEquiv e).symm x,
      (Subgroup.centerCongr e).symm ⟨x, hx⟩ |>.property,
      (blockUEquiv e).apply_symm_apply x⟩

private def coreQuotientEquiv (e : A ≃* B) :
    (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

private def blockModuleEquiv (e : A ≃* B) : BlockModule A ≃* BlockModule B :=
  QuotientGroup.congr _ _ (blockUEquiv e) (transport_blockFixed e)

private theorem blockUEquiv_conjugate (e : A ≃* B) (a : A) (u : blockU A) :
    blockUEquiv e (blockConjugate A a u) =
      blockConjugate B (e a) (blockUEquiv e u) := by
  apply Subtype.ext
  change e (a * (u : A) * a⁻¹) = e a * e (u : A) * (e a)⁻¹
  simp only [map_mul, map_inv]

/-- Pull back the actual core quotient and conjugation module along an isomorphism. -/
def BlockModuleModel.comap {X V : Type*} [Group X] [Group V]
    {rho : X →* MulAut V} (model : BlockModuleModel A rho) (e : B ≃* A) :
    BlockModuleModel B rho where
  quotientIso := (coreQuotientEquiv e).trans model.quotientIso
  moduleIso := (blockModuleEquiv e).trans model.moduleIso
  intertwining b u := by
    change model.moduleIso (QuotientGroup.mk' (blockFixed A)
      (blockUEquiv e (blockConjugate B b u))) =
      rho (model.quotientIso (QuotientGroup.mk' (pCore 2 A) (e b)))
        (model.moduleIso (QuotientGroup.mk' (blockFixed A) (blockUEquiv e u)))
    rw [blockUEquiv_conjugate]
    exact model.intertwining (e b) (blockUEquiv e u)

/-- The full equivariant linear model is invariant under group isomorphism. -/
theorem IsLinearBlockModel.of_mulEquiv {X V k : Type*} [Group X]
    [AddCommGroup V] [Semiring k] [Module k V]
    {pi : Representation k X V} (h : IsLinearBlockModel A pi) (e : A ≃* B) :
    IsLinearBlockModel B pi := by
  obtain ⟨rho, ⟨model⟩, hpi⟩ := h
  exact ⟨rho, ⟨model.comap e.symm⟩, hpi⟩

/-- Transport an L₂ block without replacing either its quotient or natural module. -/
theorem IsL2EvenBlock.of_mulEquiv {m : ℕ} (h : IsL2EvenBlock A m) (e : A ≃* B) :
    IsL2EvenBlock B m := by
  obtain ⟨hm, hs, F, hF, hfF, hcard, hpsl, hmodel⟩ := h
  refine ⟨hm, hs.of_mulEquiv e, F, hF, hfF, hcard, ?_, hmodel.of_mulEquiv e⟩
  obtain ⟨E, hE, hfE, hcardE, ⟨iso⟩⟩ := hpsl
  exact ⟨E, hE, hfE, hcardE, ⟨(coreQuotientEquiv e).symm.trans iso⟩⟩

/-- The alternating block's actual binary permutation chief factor transports. -/
theorem IsAlternatingBlock.of_mulEquiv {m : ℕ} (h : IsAlternatingBlock A m)
    (e : A ≃* B) : IsAlternatingBlock B m :=
  ⟨h.1, h.2.1.of_mulEquiv e, h.2.2.of_mulEquiv e⟩

end CFSG.Quasithin.ChapterC

end
