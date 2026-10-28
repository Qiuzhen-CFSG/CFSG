module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.FixedSpaces
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport

/-!
# Conjugation of small blocks in E.6.23

Conjugation transports the intrinsic two-core quotient, its commutator module,
and the intertwining equation, as well as subnormality in the centralizer.
The A₅ deleted permutation module is retained unchanged.

The private transport construction is adapted from
`Chapter15/Section03/CharacteristicTwo/RankOneConfiguration/Recognition/LinearTwo/PushingUp/Factors/Transport.lean`;
keeping it here avoids a dependency from Chapter E on Chapter 15.
Source: Aschbacher–Smith, C.1.7 and C.1.12, pp.123–124, and E.6.23, p.255.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
open ChapterC

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
private def pullbackModel {X V : Type*} [Group X] [Group V]
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
private theorem linearModel_of_equiv {X V k : Type*} [Group X]
    [AddCommGroup V] [Semiring k] [Module k V]
    {pi : Representation k X V} (h : IsLinearBlockModel A pi) (e : A ≃* B) :
    IsLinearBlockModel B pi := by
  obtain ⟨rho, ⟨model⟩, hpi⟩ := h
  exact ⟨rho, ⟨pullbackModel model e.symm⟩, hpi⟩

private theorem alternating_of_equiv {m : ℕ} (h : IsAlternatingBlock A m)
    (e : A ≃* B) : IsAlternatingBlock B m :=
  ⟨h.1, h.2.1.of_mulEquiv e, linearModel_of_equiv h.2.2 e⟩

variable {G : Type*} [Group G]

/-- Conjugation transports the block and its actual alternating module between centralizers. -/
theorem smallBlock_conjugate {U L : Subgroup G} (hL : SmallBlock U L) (g : G) :
    SmallBlock (U.map (MulAut.conj g).toMonoidHom)
      (L.map (MulAut.conj g).toMonoidHom) := by
  let e := MulAut.conj g
  let C := centralizer (U : Set G)
  let C' := centralizer (U.map e.toMonoidHom : Set G)
  have he : C.map e.toMonoidHom = C' := Theory.Quasithin.map_centralizer e U
  let f : C ≃* C' := (e.subgroupMap C).trans (MulEquiv.subgroupCongr he)
  have hf : (L.subgroupOf C).map f.toMonoidHom =
      (L.map e.toMonoidHom).subgroupOf C' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, heq⟩
      exact ⟨⟨y, hL.1 hy⟩, hy, Subtype.ext heq⟩
  refine ⟨(map_mono (f := e.toMonoidHom) hL.1).trans he.le,
    hf ▸ hL.2.1.map_equiv f, ?_⟩
  exact hL.2.2.imp (fun h => alternating_of_equiv h (e.subgroupMap L))
    (fun h => alternating_of_equiv h (e.subgroupMap L))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection
